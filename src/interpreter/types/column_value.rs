//! Columnar storage for vectorized execution: [`ColumnValue`] and the
//! [`FuncBinding`] pairs that make up function-valued columns.

use std::collections::HashMap;
use std::iter;
use std::mem::take;

use bit_vec::BitVec;
use smol_str::SmolStr;

use super::{BaseType, Extent, Value};

/// Returns whether the given FuncBindings represent a logical list.
pub fn bindings_are_list(bindings: &[FuncBinding]) -> bool {
    bindings
        .iter()
        .enumerate()
        .all(|(i, b)| b.input == Value::UInt(i))
}

/// A function binding represents a single input-output pair for a function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncBinding {
    pub input: Value,
    pub output: Value,
}

/// Retain elements of `v` where the corresponding `mask` bit is true,
/// preserving the relative order of kept elements.
///
/// Order-stable: walks `v` with a write cursor, swapping each kept element
/// into the next write slot.  A faster two-pointer swap-with-end algorithm
/// (similar to the one used for the `Bools` variant of `ColumnValue::retain`)
/// would not preserve order, which is incompatible with how mutation-loop
/// outputs land in a `Tile::SealedFunction` with a `Union`-domain: the
/// `Union` variants in `ColumnValue::retain` use a stable `select_indices`
/// filter (their order has to match the stably-filtered `tags`), so the
/// codomain — retained via this function — must also stay in source order
/// to keep domain/codomain entries aligned position-by-position.
fn retain_vec<T>(v: &mut Vec<T>, mask: &BitVec) {
    debug_assert_eq!(
        mask.len(),
        v.len(),
        "retain_vec: mask length must match vector length"
    );
    let mut write = 0usize;
    for read in 0..v.len() {
        if mask[read] {
            if write != read {
                v.swap(write, read);
            }
            write += 1;
        }
    }
    v.truncate(write);
}

/// Columnar data for vectorized execution.
/// Each variant holds a typed batch of values produced during interpretation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColumnValue {
    Units(usize),
    Ints(Vec<i64>),
    UInts(Vec<usize>),
    Strings(Vec<SmolStr>),
    Bools(BitVec),
    Variants(Vec<Value>),
    FunctionBindings {
        inputs: Box<ColumnValue>,
        outputs: Box<ColumnValue>,
    },
    Records(HashMap<String, ColumnValue>),
    /// A tagged union column: each element belongs to one of several typed variants.
    ///
    /// `tags[i]` is the 0-based variant index for element `i`.
    /// `variants[j]` holds only the elements whose tag equals `j`, in the order
    /// they appear in the overall sequence.  The total element count is `tags.len()`.
    Union {
        /// Variant index for each element.
        tags: Vec<usize>,
        /// Per-variant column; `variants[j].len()` equals the count of `j`s in `tags`.
        variants: Vec<ColumnValue>,
    },
}

impl ColumnValue {
    /// Construct a `FunctionBindings` variant from inputs and outputs.
    pub fn function_bindings(inputs: ColumnValue, outputs: ColumnValue) -> ColumnValue {
        Self::FunctionBindings {
            inputs: Box::new(inputs),
            outputs: Box::new(outputs),
        }
    }

    /// Get a value at a specific index.
    pub fn index_at(&self, i: usize) -> Value {
        match self {
            ColumnValue::Units(_) => Value::Unit,
            ColumnValue::Bools(v) => Value::Bool(v[i]),
            ColumnValue::Ints(v) => Value::Int(v[i]),
            ColumnValue::UInts(v) => Value::UInt(v[i]),
            ColumnValue::Strings(v) => Value::String(v[i].clone()),
            ColumnValue::Variants(v) => v[i].clone(),
            ColumnValue::FunctionBindings { inputs, outputs } => {
                Value::Function(vec![FuncBinding {
                    input: inputs.index_at(i),
                    output: outputs.index_at(i),
                }])
            }
            ColumnValue::Records(r) => {
                Value::Record(r.iter().map(|(k, v)| (k.clone(), v.index_at(i))).collect())
            }
            ColumnValue::Union { tags, variants } => {
                let tag = tags[i];
                // Count how many elements before index i belong to the same variant.
                let variant_idx = tags[..i].iter().filter(|&&t| t == tag).count();
                Value::Union {
                    tag,
                    inner: Box::new(variants[tag].index_at(variant_idx)),
                }
            }
        }
    }

    /// Repeat a single-element `ColumnValue` to the given length.
    pub fn repeat(&self, n: usize) -> ColumnValue {
        assert_eq!(self.len(), 1, "repeat requires single-element ColumnValue");
        match self {
            ColumnValue::Units(_) => ColumnValue::Units(n),
            ColumnValue::Bools(v) => ColumnValue::Bools(BitVec::from_elem(n, v[0])),
            ColumnValue::Ints(v) => ColumnValue::Ints(vec![v[0]; n]),
            ColumnValue::UInts(v) => ColumnValue::UInts(vec![v[0]; n]),
            ColumnValue::Strings(v) => ColumnValue::Strings(vec![v[0].clone(); n]),
            ColumnValue::Variants(v) => ColumnValue::Variants(vec![v[0].clone(); n]),
            ColumnValue::Records(r) => {
                ColumnValue::Records(r.iter().map(|(k, v)| (k.clone(), v.repeat(n))).collect())
            }
            // A single-element `Union` carries its one value in `variants[tag]`
            // (the other variant columns are empty). Broadcasting it (e.g.
            // `MapResultToConst` lifting a constant `.Abort(unit)` over a stream)
            // repeats that arm's payload `n` times and its `tag` in `tags`; the
            // empty arms stay empty, preserving the `ColumnValue::Union` invariant
            // (`variants[j].len()` equals the count of `j`s in `tags`).
            ColumnValue::Union { tags, variants } => {
                let tag = tags[0];
                let variants = variants
                    .iter()
                    .enumerate()
                    .map(|(i, v)| if i == tag { v.repeat(n) } else { v.clone() })
                    .collect();
                ColumnValue::Union {
                    tags: vec![tag; n],
                    variants,
                }
            }
            _ => panic!("Cannot repeat composite ColumnValue"),
        }
    }

    /// Convert a Vec<Value> into typed ColumnValue.
    pub fn from_values(values: Vec<Value>, extent: &Extent) -> ColumnValue {
        match extent {
            Extent::Base(BaseType::Unit) => ColumnValue::Units(values.len()),
            Extent::Base(BaseType::Bool) => {
                ColumnValue::Bools(values.iter().map(Value::as_bool).collect())
            }
            Extent::Base(BaseType::Int) => {
                ColumnValue::Ints(values.iter().map(Value::as_int).collect())
            }
            Extent::Base(BaseType::UInt) | Extent::UIntRange(..) => {
                ColumnValue::UInts(values.iter().map(Value::as_uint).collect())
            }
            Extent::Base(BaseType::String) => {
                ColumnValue::Strings(values.iter().map(|v| v.as_string().clone()).collect())
            }
            Extent::Record(m) => {
                // Pivot the list of Records into a Record of ColumnValues
                let keys: Vec<String> = m.keys().cloned().collect();
                let fields = keys
                    .into_iter()
                    .map(|key| {
                        let field_values = values
                            .iter()
                            .map(|v| match v {
                                Value::Record(r) => r[&key].clone(),
                                _ => panic!("Expected Record in from_values, got {v:?}"),
                            })
                            .collect();
                        (
                            key.clone(),
                            ColumnValue::from_values(
                                field_values,
                                extent
                                    .record_fields()
                                    .and_then(|fields| fields.get(&key))
                                    .unwrap_or_else(|| {
                                        panic!("Record extent missing field '{key}'")
                                    }),
                            ),
                        )
                    })
                    .collect();
                ColumnValue::Records(fields)
            }
            Extent::DataSourceDomain(d) => {
                ColumnValue::from_values(values, &d.borrow().element_extent())
            }
            Extent::Union(sub_extents) => {
                let mut tags: Vec<usize> = Vec::with_capacity(values.len());
                let mut per_variant: Vec<Vec<Value>> = vec![Vec::new(); sub_extents.len()];
                for v in values {
                    let Value::Union { tag, inner } = v else {
                        panic!("Expected Value::Union in from_values for Union extent, got {v:?}");
                    };
                    tags.push(tag);
                    per_variant[tag].push(*inner);
                }
                ColumnValue::Union {
                    tags,
                    variants: per_variant
                        .into_iter()
                        .zip(sub_extents.iter())
                        .map(|(vals, ext)| ColumnValue::from_values(vals, ext))
                        .collect(),
                }
            }
            _ => ColumnValue::Variants(values),
        }
    }

    /// Sort `FunctionBindings` by their input values.
    pub fn sort_by_inputs(&self) -> ColumnValue {
        match self {
            ColumnValue::FunctionBindings { inputs, outputs } => {
                let n = inputs.len();
                let mut indices: Vec<usize> = (0..n).collect();
                indices.sort_by(|&a, &b| {
                    inputs
                        .index_at(a)
                        .partial_cmp(&inputs.index_at(b))
                        .expect("Cannot compare inputs")
                });
                ColumnValue::function_bindings(
                    inputs.select_indices(indices.iter().cloned(), indices.len()),
                    outputs.select_indices(indices.iter().cloned(), indices.len()),
                )
            }
            other => other.clone(),
        }
    }

    /// Select elements at the given indices.
    pub fn select_indices(
        &self,
        indices: impl Iterator<Item = usize>,
        indices_len: usize,
    ) -> ColumnValue {
        match self {
            ColumnValue::Units(_) => ColumnValue::Units(indices_len),
            ColumnValue::Bools(v) => ColumnValue::Bools(indices.map(|i| v[i]).collect()),
            ColumnValue::Ints(v) => ColumnValue::Ints(indices.map(|i| v[i]).collect()),
            ColumnValue::UInts(v) => ColumnValue::UInts(indices.map(|i| v[i]).collect()),
            ColumnValue::Strings(v) => {
                ColumnValue::Strings(indices.map(|i| v[i].clone()).collect())
            }
            ColumnValue::Variants(v) => {
                ColumnValue::Variants(indices.map(|i| v[i].clone()).collect())
            }
            ColumnValue::FunctionBindings { inputs, outputs } => {
                let i: Vec<_> = indices.collect();
                ColumnValue::function_bindings(
                    inputs.select_indices(i.iter().cloned(), i.len()),
                    outputs.select_indices(i.iter().cloned(), i.len()),
                )
            }
            ColumnValue::Records(r) => {
                let i: Vec<_> = indices.collect();
                ColumnValue::Records(
                    r.iter()
                        .map(|(k, v)| (k.clone(), v.select_indices(i.iter().cloned(), indices_len)))
                        .collect(),
                )
            }
            ColumnValue::Union { tags, variants } => {
                let selected_indices: Vec<usize> = indices.collect();
                // Build the new tags for selected elements.
                let new_tags: Vec<usize> = selected_indices.iter().map(|&i| tags[i]).collect();
                // Count per-variant totals in the original so we can map positions.
                let mut variant_counts: Vec<usize> = vec![0; variants.len()];
                for &t in tags.iter() {
                    variant_counts[t] += 1;
                }
                // For each original position, record which variant-local index it is.
                let mut running: Vec<usize> = vec![0; variants.len()];
                let mut per_element_variant_idx: Vec<usize> = Vec::with_capacity(tags.len());
                for &t in tags.iter() {
                    per_element_variant_idx.push(running[t]);
                    running[t] += 1;
                }
                // For each variant, collect the variant-local indices we want to keep.
                let mut per_variant_selection: Vec<Vec<usize>> = vec![Vec::new(); variants.len()];
                for &orig_idx in &selected_indices {
                    let t = tags[orig_idx];
                    per_variant_selection[t].push(per_element_variant_idx[orig_idx]);
                }
                let new_variants: Vec<ColumnValue> = variants
                    .iter()
                    .enumerate()
                    .map(|(j, cv)| {
                        let sel = &per_variant_selection[j];
                        let len = sel.len();
                        cv.select_indices(sel.iter().cloned(), len)
                    })
                    .collect();
                ColumnValue::Union {
                    tags: new_tags,
                    variants: new_variants,
                }
            }
        }
    }

    /// Return the number of elements in this column.
    pub fn len(&self) -> usize {
        match &self {
            ColumnValue::Units(len) => *len,
            ColumnValue::Bools(v) => v.len(),
            ColumnValue::Ints(v) => v.len(),
            ColumnValue::UInts(v) => v.len(),
            ColumnValue::Strings(v) => v.len(),
            ColumnValue::Variants(v) => v.len(),
            ColumnValue::Records(m) => {
                let result = m.values().next().expect("Empty Record").len();
                debug_assert!(
                    m.values().all(|cv| cv.len() == result),
                    "Inconsistent column lengths in Record",
                );
                result
            }
            ColumnValue::FunctionBindings { inputs, .. } => inputs.len(),
            ColumnValue::Union { tags, .. } => tags.len(),
        }
    }

    /// Return `true` if this column contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return `true` if this column contains exactly one element.
    pub fn is_single(&self) -> bool {
        self.len() == 1
    }

    /// Return `true` if this column's element type is consistent with `extent`.
    ///
    /// This is a structural check — it verifies that the `ColumnValue` variant
    /// matches what `from_values(..., extent)` would have produced for the same
    /// data. `DataSourceDomain` extents are resolved to their element extent
    /// before comparison.
    pub fn is_compatible_with_extent(&self, extent: &Extent) -> bool {
        let extent = match extent {
            Extent::DataSourceDomain(source) => source.borrow().element_extent(),
            Extent::Restricted { base, .. } => *base.clone(),
            other => other.clone(),
        };
        match (self, extent) {
            (ColumnValue::Units(_), Extent::Base(BaseType::Unit)) => true,
            (ColumnValue::Bools(_), Extent::Base(BaseType::Bool)) => true,
            (ColumnValue::Ints(_), Extent::Base(BaseType::Int)) => true,
            (ColumnValue::UInts(_), Extent::Base(BaseType::UInt)) => true,
            (ColumnValue::UInts(_), Extent::UIntRange(..)) => true,
            (ColumnValue::Strings(_), Extent::Base(BaseType::String)) => true,
            (ColumnValue::Records(fields), Extent::Record(ext_fields)) => {
                fields.len() == ext_fields.len()
                    && fields.iter().all(|(k, cv)| {
                        ext_fields
                            .get(k)
                            .is_some_and(|e| cv.is_compatible_with_extent(e))
                    })
            }
            (ColumnValue::FunctionBindings { .. }, Extent::Function { .. }) => true,
            (ColumnValue::Union { variants, .. }, Extent::Union(ext_variants)) => {
                variants.len() == ext_variants.len()
                    && variants
                        .iter()
                        .zip(ext_variants.iter())
                        .all(|(cv, e)| cv.is_compatible_with_extent(e))
            }
            // Variants is the fallback used for Union, unknown, etc.
            (ColumnValue::Variants(_), _) => true,
            _ => false,
        }
    }

    /// Return `true` if this column is a single scalar value that can broadcast.
    /// Note: it's a bit unsafe that we are just using length for this, as it
    /// could mask bugs where a vector column of length 1 could be treated as a
    /// scalar.
    /// TODO: consider adding an explicit Scalar variant to ColumnValue to avoid this ambiguity.
    pub fn is_scalar(&self) -> bool {
        self.len() == 1
    }

    /// Get the single value if this column contains exactly one element.
    pub fn as_single(&self) -> Option<Value> {
        if self.len() == 1 {
            match self {
                ColumnValue::Units(len) => {
                    if *len == 1 {
                        Some(Value::Unit)
                    } else {
                        None
                    }
                }
                ColumnValue::Bools(v) => Some(Value::Bool(v[0])),
                ColumnValue::Ints(v) => Some(Value::Int(v[0])),
                ColumnValue::UInts(v) => Some(Value::UInt(v[0])),
                ColumnValue::Strings(v) => Some(Value::String(v[0].clone())),
                ColumnValue::Variants(v) => Some(v[0].clone()),
                ColumnValue::FunctionBindings { inputs, outputs } => {
                    Some(Value::Function(vec![FuncBinding {
                        input: inputs.as_single().expect("Not single").clone(),
                        output: outputs.as_single().expect("Not single").clone(),
                    }]))
                }
                ColumnValue::Records(r) => Some(Value::Record(
                    r.iter()
                        .map(|e| (e.0.clone(), e.1.as_single().expect("Not single").clone()))
                        .collect(),
                )),
                ColumnValue::Union { tags, variants } => {
                    let tag = tags[0];
                    let inner = variants[tag].as_single()?;
                    Some(Value::Union {
                        tag,
                        inner: Box::new(inner),
                    })
                }
            }
        } else {
            None
        }
    }

    /// Create a `ColumnValue` from a single `Value`, wrapping it in a 1-element column.
    pub fn single(value: Value) -> Self {
        match value {
            // `Unit` has a dedicated dense column (`Units(n)`), which is the
            // canonical representation `from_values`/`empty_tile` produce for a
            // `Unit` extent. Falling through to the `Variants` catch-all would
            // make a singleton `Unit` column collide (`append`/`merge`
            // "mismatched variants") with an extent-canonical `Units` column —
            // e.g. a `.Abort()` (`Unit` payload) variant value fanned through a
            // `Memo`. Keep the representation canonical here.
            Value::Unit => ColumnValue::Units(1),
            Value::Bool(b) => ColumnValue::Bools(BitVec::from_elem(1, b)),
            Value::Int(i) => ColumnValue::Ints(vec![i]),
            Value::UInt(i) => ColumnValue::UInts(vec![i]),
            Value::String(s) => ColumnValue::Strings(vec![s]),
            Value::Record(fields) => ColumnValue::Records(
                fields
                    .into_iter()
                    .map(|(k, v)| (k, ColumnValue::single(v)))
                    .collect(),
            ),
            _ => ColumnValue::Variants(vec![value]),
        }
    }

    /// Drain this column into an owned iterator of [`Value`]s, one per row.
    ///
    /// After the call, `self` is left in a valid but empty state.
    /// Note: this is quite expensive and should be used as a last resort.
    pub fn drain_to_value_iter(&mut self) -> Box<dyn Iterator<Item = Value>> {
        match self {
            ColumnValue::Units(n) => {
                let count = *n;
                *n = 0;
                Box::new(iter::repeat_n(Value::Unit, count))
            }
            ColumnValue::Bools(v) => {
                // BitVec::take gives us ownership so we can return a 'static iterator.
                Box::new(take(v).into_iter().map(Value::Bool))
            }
            ColumnValue::Ints(v) => Box::new(take(v).into_iter().map(Value::Int)),
            ColumnValue::UInts(v) => Box::new(take(v).into_iter().map(Value::UInt)),
            ColumnValue::Strings(v) => Box::new(take(v).into_iter().map(Value::String)),
            ColumnValue::Variants(v) => Box::new(take(v).into_iter()),
            ColumnValue::FunctionBindings { inputs, outputs } => Box::new(
                inputs
                    .drain_to_value_iter()
                    .zip(outputs.drain_to_value_iter())
                    .map(|(input, output)| Value::Function(vec![FuncBinding { input, output }])),
            ),
            ColumnValue::Records(m) => {
                let m = take(m);
                let n = m.values().next().map(|v| v.len()).unwrap_or(0);
                Box::new((0..n).map(move |i| {
                    Value::Record(m.iter().map(|(k, v)| (k.clone(), v.index_at(i))).collect())
                }))
            }
            ColumnValue::Union { tags, variants } => {
                let tags = take(tags);
                let n = tags.len();
                // Snapshot the variants so the closure can own them.
                let variants = variants.to_vec();
                // Build per-variant running counts so we can derive variant-local indices.
                let mut running: Vec<usize> = vec![0; variants.len()];
                Box::new((0..n).map(move |i| {
                    let tag = tags[i];
                    let vi = running[tag];
                    running[tag] += 1;
                    Value::Union {
                        tag,
                        inner: Box::new(variants[tag].index_at(vi)),
                    }
                }))
            }
        }
    }

    /// Create a `ColumnValue` from a `Vec<i64>`.
    pub fn from_ints(values: Vec<i64>) -> Self {
        ColumnValue::Ints(values)
    }

    /// Create a `ColumnValue` from a `Vec<usize>`.
    pub fn from_uints(values: Vec<usize>) -> Self {
        ColumnValue::UInts(values)
    }

    /// Compute the cartesian product of a map of named column values.
    ///
    /// Returns a [`ColumnValue::Records`] where each field is expanded so that the fields
    /// together enumerate every combination of rows across all input columns. The total
    /// row count is the product of all input column lengths.
    ///
    /// # Example
    /// Given `{"a": [1, 2], "b": [3, 4]}`, returns
    /// `Records {"a": [1, 1, 2, 2], "b": [3, 4, 3, 4]}`.
    pub fn cartesian_product(data: HashMap<String, ColumnValue>) -> ColumnValue {
        if data.is_empty() {
            return ColumnValue::Records(HashMap::new());
        }
        // Sort keys for a deterministic column order when computing strides.
        let mut keys: Vec<String> = data.keys().cloned().collect();
        keys.sort();
        let lengths: Vec<usize> = keys.iter().map(|k| data[k].len()).collect();
        let total: usize = lengths.iter().product();
        let expanded = keys
            .iter()
            .enumerate()
            .map(|(j, key)| {
                // stride: how many output rows share the same index into this column
                // before it advances — the product of all subsequent column lengths.
                let stride: usize = lengths[j + 1..].iter().product();
                let indices = (0..total).map(|i| (i / stride) % lengths[j]);
                (key.clone(), data[key].select_indices(indices, total))
            })
            .collect();
        ColumnValue::Records(expanded)
    }

    /// Construct a `ColumnValue` containing the given string values.
    pub fn strings(values: &[&str]) -> ColumnValue {
        ColumnValue::Strings(values.iter().map(|s| (*s).into()).collect())
    }

    pub fn append(&mut self, other: ColumnValue) {
        match (self, other) {
            (ColumnValue::Units(s), ColumnValue::Units(o)) => *s += o,
            (ColumnValue::Ints(s), ColumnValue::Ints(mut o)) => s.append(&mut o),
            (ColumnValue::UInts(s), ColumnValue::UInts(mut o)) => s.append(&mut o),
            (ColumnValue::Bools(s), ColumnValue::Bools(mut o)) => s.append(&mut o),
            (ColumnValue::Strings(s), ColumnValue::Strings(mut o)) => s.append(&mut o),
            (ColumnValue::Variants(s), ColumnValue::Variants(mut o)) => s.append(&mut o),
            (
                ColumnValue::FunctionBindings {
                    inputs: si,
                    outputs: so,
                },
                ColumnValue::FunctionBindings {
                    inputs: oi,
                    outputs: oo,
                },
            ) => {
                si.append(*oi);
                so.append(*oo);
            }
            (ColumnValue::Records(s), ColumnValue::Records(o)) => {
                for (k, v) in o {
                    s.get_mut(&k)
                        .unwrap_or_else(|| panic!("Missing field {k} in append"))
                        .append(v);
                }
            }
            (
                ColumnValue::Union {
                    tags: st,
                    variants: sv,
                },
                ColumnValue::Union {
                    tags: ot,
                    variants: ov,
                },
            ) => {
                assert_eq!(sv.len(), ov.len(), "Union append: variant count mismatch");
                st.extend(ot);
                for (s, o) in sv.iter_mut().zip(ov) {
                    s.append(o);
                }
            }
            _ => panic!("Mismatched ColumnValue variants in append"),
        }
    }

    /// Retain only elements where `mask[i]` is true, in-place.
    ///
    /// Not guaranteed to preserve element ordering; when possible, uses swap-remove to avoid shifting data.
    pub fn retain(&mut self, mask: &BitVec) {
        assert_eq!(
            mask.len(),
            self.len(),
            "mask length must match column length"
        );
        match self {
            ColumnValue::Units(_) => {
                *self = ColumnValue::Units(mask.count_ones() as usize);
            }
            ColumnValue::Ints(v) => retain_vec(v, mask),
            ColumnValue::UInts(v) => retain_vec(v, mask),
            ColumnValue::Strings(v) => retain_vec(v, mask),
            ColumnValue::Variants(v) => retain_vec(v, mask),
            ColumnValue::Bools(v) => {
                let n = v.len();
                if n > 0 {
                    let mut left = 0usize;
                    let mut right = n - 1;
                    loop {
                        while left < right && mask[left] {
                            left += 1;
                        }
                        while right > left && !mask[right] {
                            right -= 1;
                        }
                        if left >= right {
                            break;
                        }
                        let lv = v[left];
                        let rv = v[right];
                        v.set(left, rv);
                        v.set(right, lv);
                        left += 1;
                        right -= 1;
                    }
                }
                let count = mask.iter().filter(|b| *b).count();
                v.truncate(count);
            }
            ColumnValue::FunctionBindings { inputs, outputs } => {
                inputs.retain(mask);
                outputs.retain(mask);
            }
            ColumnValue::Records(r) => {
                for v in r.values_mut() {
                    v.retain(mask);
                }
            }
            ColumnValue::Union { tags, variants } => {
                // Build per-variant masks, then retain in each variant.
                let mut per_variant_mask: Vec<BitVec> = variants
                    .iter()
                    .map(|v| BitVec::from_elem(v.len(), false))
                    .collect();
                let mut running: Vec<usize> = vec![0; variants.len()];
                for (i, &t) in tags.iter().enumerate() {
                    let vi = running[t];
                    running[t] += 1;
                    if mask[i] {
                        per_variant_mask[t].set(vi, true);
                    }
                }
                let new_tags: Vec<usize> = tags
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask[*i])
                    .map(|(_, &t)| t)
                    .collect();
                *tags = new_tags;
                for (v, m) in variants.iter_mut().zip(per_variant_mask.iter()) {
                    // Use select_indices for a stable retain.  Like `retain_vec`,
                    // this preserves source order — required because `tags` above
                    // is filtered stably, and each variant column has to stay
                    // aligned with the tag occurrences of its variant.
                    let kept: Vec<usize> = m
                        .iter()
                        .enumerate()
                        .filter(|(_, b)| *b)
                        .map(|(i, _)| i)
                        .collect();
                    let len = kept.len();
                    *v = v.select_indices(kept.into_iter(), len);
                }
            }
        }
    }

    /// Map each element of `self` through a lookup table defined by parallel
    /// `(map_keys, map_values)` columns.
    ///
    /// Builds a `HashMap<key_type, position>` from `map_keys`, then uses
    /// [`ColumnValue::select_indices`] to extract the corresponding `map_values`
    /// entries.  Dispatching the value-type through `select_indices` means only
    /// the key type needs an explicit match arm here.
    ///
    /// Drains `self` as a side effect (the column is left empty after the call).
    pub fn transform_by_map(
        &mut self,
        map_keys: ColumnValue,
        map_values: ColumnValue,
    ) -> ColumnValue {
        let indices: Vec<usize> = match (self, map_keys) {
            (ColumnValue::UInts(v), ColumnValue::UInts(mk)) => {
                let pos: HashMap<usize, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Ints(v), ColumnValue::Ints(mk)) => {
                let pos: HashMap<i64, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Strings(v), ColumnValue::Strings(mk)) => {
                let pos: HashMap<SmolStr, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Bools(v), ColumnValue::Bools(mk)) => {
                let pos: HashMap<bool, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (ColumnValue::Variants(v), ColumnValue::Variants(mk)) => {
                let pos: HashMap<Value, usize> =
                    mk.into_iter().enumerate().map(|(i, k)| (k, i)).collect();
                take(v).into_iter().map(|k| pos[&k]).collect()
            }
            (s, mk) => panic!(
                "transform_by_map: key type mismatch or unsupported: {:?} vs {:?}",
                s, mk
            ),
        };
        let n = indices.len();
        map_values.select_indices(indices.into_iter(), n)
    }

    /// Map each element of `self` (which must be [`ColumnValue::UInts`] used as
    /// zero-based indices) through `map`, returning the selected entries.
    ///
    /// Delegates entirely to [`ColumnValue::select_indices`], so `map` may be
    /// any `ColumnValue` variant.  Drains `self` as a side effect.
    pub fn transform_by_list(&mut self, map: ColumnValue) -> ColumnValue {
        let ColumnValue::UInts(v) = self else {
            panic!("transform_by_list: input must be UInts, got {self:?}")
        };
        let indices = take(v);
        let n = indices.len();
        map.select_indices(indices.into_iter(), n)
    }

    pub fn for_each_uint(&mut self, f: impl Fn(&mut usize)) {
        match self {
            ColumnValue::UInts(v) => v.iter_mut().for_each(f),
            _ => panic!("Not UInts"),
        }
    }

    /// Returns a reference to the internal bitvec if this ColumnValue is bools.
    pub fn as_bitvec(&self) -> Option<&BitVec> {
        if let ColumnValue::Bools(b) = self {
            Some(b)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn single_unit_is_canonical_units_column() {
        // A singleton `Unit` value must build the dense `Units(1)` column that
        // `from_values`/`empty_tile` produce for a `Unit` extent — not a
        // `Variants([Unit])` singleton, which would collide ("mismatched
        // variants") in `append`/`merge` against an extent-canonical `Units`
        // column (e.g. a `.Abort()` Unit-payload variant fanned through a `Memo`).
        assert_eq!(ColumnValue::single(Value::Unit), ColumnValue::Units(1));
    }

    #[test]
    fn test_cartesian_product_no_filter() {
        // {"a": [1,2], "b": [3,4]}, no filter → full 2×2 product.
        // Keys sorted: ["a","b"].  Strides: a=2, b=1.
        // Row 0: a[0]=1, b[0]=3 | Row 1: a[0]=1, b[1]=4
        // Row 2: a[1]=2, b[0]=3 | Row 3: a[1]=2, b[1]=4
        let data = HashMap::from([
            ("a".to_string(), ColumnValue::Ints(vec![1, 2])),
            ("b".to_string(), ColumnValue::Ints(vec![3, 4])),
        ]);
        let result = ColumnValue::cartesian_product(data);
        assert_eq!(
            result,
            ColumnValue::Records(HashMap::from([
                ("a".to_string(), ColumnValue::Ints(vec![1, 1, 2, 2])),
                ("b".to_string(), ColumnValue::Ints(vec![3, 4, 3, 4])),
            ]))
        );
    }

    #[test]
    fn test_cartesian_product_empty_map() {
        let result = ColumnValue::cartesian_product(HashMap::new());
        assert_eq!(result, ColumnValue::Records(HashMap::new()));
    }

    // --- retain_vec tests ---

    #[test]
    fn test_retain_vec_keep_some() {
        // mask: keep indices 0 and 2, drop index 1.
        // Order is unspecified; sort to compare.
        let mut v = vec![10, 20, 30];
        let mut mask = BitVec::from_elem(3, false);
        mask.set(0, true);
        mask.set(2, true);
        retain_vec(&mut v, &mask);
        v.sort();
        assert_eq!(v, vec![10, 30]);
    }

    #[test]
    fn test_retain_vec_keep_all() {
        let mut v = vec![1, 2, 3];
        let mask = BitVec::from_elem(3, true);
        retain_vec(&mut v, &mask);
        v.sort();
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn test_retain_vec_keep_none() {
        let mut v = vec![1, 2, 3];
        let mask = BitVec::from_elem(3, false);
        retain_vec(&mut v, &mask);
        assert!(v.is_empty());
    }

    // --- ColumnValue::Union retain tests ---

    /// Helper: build a `ColumnValue::Union` from parallel tag/value slices.
    ///
    /// `rows` is `(tag, value)` in source order.  Values for a given tag must
    /// be `Value::Int`; each variant column is `ColumnValue::Ints`.
    fn make_union_cv(rows: &[(usize, i64)], n_variants: usize) -> ColumnValue {
        let tags: Vec<usize> = rows.iter().map(|(t, _)| *t).collect();
        let mut per_variant: Vec<Vec<i64>> = vec![Vec::new(); n_variants];
        for (t, v) in rows {
            per_variant[*t].push(*v);
        }
        ColumnValue::Union {
            tags,
            variants: per_variant.into_iter().map(ColumnValue::Ints).collect(),
        }
    }

    fn mask(bits: &[bool]) -> BitVec {
        let mut bv = BitVec::from_elem(bits.len(), false);
        for (i, &b) in bits.iter().enumerate() {
            bv.set(i, b);
        }
        bv
    }

    /// Keeping all rows leaves the column unchanged.
    #[test]
    fn retain_union_keep_all() {
        // rows: tag0→1, tag1→10, tag0→2, tag1→20
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2), (1, 20)], 2);
        cv.retain(&mask(&[true, true, true, true]));
        assert_eq!(cv, make_union_cv(&[(0, 1), (1, 10), (0, 2), (1, 20)], 2));
    }

    /// Dropping all rows yields empty tags and empty variant columns.
    #[test]
    fn retain_union_drop_all() {
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2)], 2);
        cv.retain(&mask(&[false, false, false]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert!(tags.is_empty());
        assert!(variants.iter().all(|v| v.is_empty()));
    }

    /// Dropping a row from one variant removes only that variant's value,
    /// leaving the other variant's values untouched.
    #[test]
    fn retain_union_drop_one_from_each_variant() {
        // Source order: tag0→1, tag1→10, tag0→2, tag1→20
        // Keep rows 0 and 3 (tag0→1, tag1→20); drop rows 1 and 2.
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2), (1, 20)], 2);
        cv.retain(&mask(&[true, false, false, true]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert_eq!(tags, &[0, 1]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![1]));
        assert_eq!(variants[1], ColumnValue::Ints(vec![20]));
    }

    /// Keeping only rows from one variant empties the other variant's column.
    #[test]
    fn retain_union_keep_only_one_variant() {
        // Source order: tag0→1, tag1→10, tag0→2
        // Keep only the two tag-0 rows.
        let mut cv = make_union_cv(&[(0, 1), (1, 10), (0, 2)], 2);
        cv.retain(&mask(&[true, false, true]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert_eq!(tags, &[0, 0]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![1, 2]));
        assert_eq!(variants[1], ColumnValue::Ints(vec![]));
    }

    /// Retaining consecutive rows from the middle preserves source order within each variant.
    #[test]
    fn retain_union_preserves_variant_order() {
        // Source order: tag0→10, tag0→20, tag1→100, tag0→30, tag1→200
        // Keep rows 1,2,3 (tag0→20, tag1→100, tag0→30); drop first and last.
        let mut cv = make_union_cv(&[(0, 10), (0, 20), (1, 100), (0, 30), (1, 200)], 2);
        cv.retain(&mask(&[false, true, true, true, false]));
        let ColumnValue::Union { tags, variants } = &cv else {
            panic!("expected Union");
        };
        assert_eq!(tags, &[0, 1, 0]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![20, 30]));
        assert_eq!(variants[1], ColumnValue::Ints(vec![100]));
    }

    /// Appending two interleaved `Commit(Int) | Abort(Unit)` union columns
    /// concatenates tags and each per-variant column in order — the fold two
    /// writers' interleaved decision streams merge through. This is the
    /// `ColumnValue::Union` machinery a `Commit | Abort` variant decision
    /// reuses in the commit-`Store` codomain. Variant 0 =
    /// `Commit` (carries an Int write), variant 1 = `Abort` (a unit).
    #[test]
    fn append_union_interleaved_commit_abort() {
        // Writer A's stream: Commit(1), Abort, Commit(2).
        let mut a = ColumnValue::Union {
            tags: vec![0, 1, 0],
            variants: vec![ColumnValue::Ints(vec![1, 2]), ColumnValue::Units(1)],
        };
        // Writer B's stream: Abort, Commit(3).
        let b = ColumnValue::Union {
            tags: vec![1, 0],
            variants: vec![ColumnValue::Ints(vec![3]), ColumnValue::Units(1)],
        };
        a.append(b);
        let ColumnValue::Union { tags, variants } = &a else {
            panic!("expected Union");
        };
        // Tags concatenate in source order; each variant column concatenates too.
        assert_eq!(tags, &[0, 1, 0, 1, 0]);
        assert_eq!(variants[0], ColumnValue::Ints(vec![1, 2, 3]));
        assert_eq!(variants[1], ColumnValue::Units(2));
        // Row-wise read-back: the Commit rows carry their Ints; the Abort rows
        // are units. `index_at` maps a row to its variant-local position.
        assert_eq!(
            a.index_at(0),
            Value::Union {
                tag: 0,
                inner: Box::new(Value::Int(1))
            }
        );
        assert_eq!(
            a.index_at(3),
            Value::Union {
                tag: 1,
                inner: Box::new(Value::Unit)
            }
        );
        assert_eq!(
            a.index_at(4),
            Value::Union {
                tag: 0,
                inner: Box::new(Value::Int(3))
            }
        );
    }
}
