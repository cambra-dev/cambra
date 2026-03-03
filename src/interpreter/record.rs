//! Operators and producers for CCL record construction and field access.
//!
//! This module provides two operators:
//! - [`ConstructRecord`]: builds a record value from a named set of field operators.
//! - [`RecordField`]: projects a single named field out of a record operator.
//!
//! Each operator has a corresponding runtime producer ([`ConstructRecordProducer`],
//! [`RecordFieldProducer`]) created at `subscribe()` time, which carries the actual
//! execution state.

use std::cell::RefCell;
use std::{collections::HashMap, rc::Rc};

use crate::interpreter::{
    ColumnValue, Consumer, Extent, GetResult, Guard, Operator, Producer, Scheduler, VarScope,
};
use crate::pretty_graph::{fmt_extent, InspectNode, VizOptions};

/// An operator that constructs a record from a set of named field operators.
///
/// Each field is computed independently by its own sub-operator; `subscribe()` fans out
/// to all fields and collects their producers into a [`ConstructRecordProducer`].
#[derive(Debug)]
pub struct ConstructRecord {
    /// The child operators keyed by field name, one per record field.
    fields: HashMap<String, Box<dyn Operator>>,
    /// The record extent, computed eagerly from the extents of all fields.
    extent: Extent,
}

impl ConstructRecord {
    /// Creates a new `ConstructRecord` from the given field operators.
    ///
    /// Eagerly computes the record [`Extent`] by collecting each field's extent, so that the
    /// full record type is known before any subscription takes place.
    pub fn new(fields: HashMap<String, Box<dyn Operator>>) -> Self {
        let extent = Extent::record(
            fields
                .iter()
                .map(|(name, op)| (name.clone(), op.extent().clone()))
                .collect(),
        );
        Self { fields, extent }
    }
}

impl Operator for ConstructRecord {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new("ConstructRecord");
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        // Sort for deterministic output.
        let mut fields: Vec<(&String, &Box<dyn Operator>)> = self.fields.iter().collect();
        fields.sort_by_key(|(k, _)| k.as_str());
        for (field, op) in fields {
            desc = desc.child(field.clone(), op.inspect(opts));
        }
        desc
    }

    /// Subscribes to all field operators and wires them into a [`ConstructRecordProducer`].
    ///
    /// The `consumer` is forwarded to exactly one field (the first one consumed from the
    /// iterator); subsequent fields receive a no-op consumer. This works correctly only when
    /// the intent guard is universal and all fields produce aligned, same-length outputs.
    fn subscribe(
        &mut self,
        // TODO handle intent guard
        _intent_guard: Guard,
        mut consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        let consumer_wrapper = Rc::new(RefCell::new(move || {
            consumer.notify();
        }));
        let producers = self
            .fields
            .iter_mut()
            .map(|(field, op)| {
                (
                    field.clone(),
                    op.subscribe(
                        Guard::Universal,
                        Box::new(consumer_wrapper.clone()),
                        var_scope.clone(),
                        scheduler,
                    ),
                )
            })
            .collect();

        Box::new(ConstructRecordProducer::new(producers))
    }
}

/// Runtime producer for [`ConstructRecord`].
///
/// Drives all field producers in lockstep and assembles their outputs into a
/// [`ColumnData::Records`] value on each [`Producer::get`] call.
#[derive(Debug)]
struct ConstructRecordProducer {
    /// One producer per record field, keyed by field name.
    field_producers: HashMap<String, Box<dyn Producer>>,
}

impl ConstructRecordProducer {
    fn new(field_producers: HashMap<String, Box<dyn Producer>>) -> Self {
        Self { field_producers }
    }
}

impl Producer for ConstructRecordProducer {
    /// Polls all field producers and zips their results into a single record column.
    ///
    /// If some fields are scalar and others are vectors, scalar fields are broadcast
    /// (repeated) to match the vector length so all fields are aligned.
    fn get(&mut self) -> GetResult {
        let num_fields = self.field_producers.len();
        let mut inputs: HashMap<String, GetResult> = self
            .field_producers
            .iter_mut()
            .map(|(name, producer)| (name.clone(), producer.get()))
            .collect();
        let mut output_data = HashMap::with_capacity(num_fields);
        let mut output_yield_guards = HashMap::with_capacity(num_fields);

        let length = inputs
            .values()
            .map(|r| r.column_value.len())
            .max()
            .expect("Empty records not supported");

        for (field, get_result) in inputs.drain() {
            output_yield_guards.insert(field.clone(), get_result.yield_guard.clone());
            let data = get_result.column_value;
            output_data.insert(
                field.clone(),
                if data.is_scalar() && length > 1 {
                    data.repeat(length)
                } else {
                    data
                },
            );
        }
        GetResult {
            column_value: ColumnValue::Records(output_data),
            yield_guard: Guard::Record(output_yield_guards),
        }
    }

    /// Propagates `obsolete_guard` to each field producer using the per-field sub-guard.
    ///
    /// A universal or empty guard is forwarded uniformly; a `Guard::Record` is split
    /// and each field receives only its own sub-guard.
    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        match &obsolete_guard {
            g if g.is_empty() => {}
            g if g.is_universal() => self.field_producers.values_mut().for_each(|input| {
                input.release(Guard::Universal);
            }),
            Guard::Record(m) => self.field_producers.iter_mut().for_each(|(field, input)| {
                m.get(field).map(|g| input.release(g.clone()));
            }),
            _ => panic!("Unexpected guard {obsolete_guard:?}"),
        };
        obsolete_guard
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new("ConstructRecordProducer");
        // Sort for deterministic output.
        let mut producers: Vec<(&String, &Box<dyn Producer>)> =
            self.field_producers.iter().collect();
        producers.sort_by_key(|(k, _)| k.as_str());
        for (field, producer) in producers {
            desc = desc.child(field.clone(), producer.inspect(opts));
        }
        desc
    }
}

/// An operator that projects a single named field out of a record-typed operator.
///
/// At `subscribe()` time, wraps the intent guard in a `Guard::Record` so the upstream
/// record operator knows which field is actually needed. The remaining fields receive a
/// `Guard::Universal` intent, meaning the subscriber doesn't restrict them further.
#[derive(Debug)]
pub struct RecordField {
    /// The upstream record operator whose output will be projected.
    input: Box<dyn Operator>,
    /// The name of the field to extract.
    field: String,
    /// The extent of the extracted field, taken from the input record's extent at construction.
    extent: Extent,
}

impl RecordField {
    /// Creates a new `RecordField` that extracts `field` from `input`.
    ///
    /// Panics if `input` does not have a `Record` extent or if `field` is not a field
    /// of that record.
    pub fn new(input: Box<dyn Operator>, field: &str) -> Self {
        let extent = input
            .extent()
            .record_fields()
            .unwrap_or_else(|| panic!("Field ref on non-record type {:?}", input.extent()))
            .get(field)
            .unwrap_or_else(|| panic!("No field {field} in {:?}", input.extent()))
            .clone();
        Self {
            input,
            field: field.to_string(),
            extent,
        }
    }
}

impl Operator for RecordField {
    fn extent(&self) -> &Extent {
        &self.extent
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        let mut desc = InspectNode::new(format!("RecordField(\"{}\")", self.field));
        if opts.show_extents {
            desc = desc.annotate(format!(": {}", fmt_extent(&self.extent)));
        }
        desc.child("input", self.input.inspect(opts))
    }

    /// Subscribes to the input record operator, requesting only the target field's intent.
    ///
    /// Builds a `Guard::Record` where the target field carries the caller's `intent_guard`
    /// and all other fields receive `Guard::Empty` (unneeded). Also installs a
    /// forwarding consumer that translates `Yield(Guard::Record(…))` notifications to the
    /// per-field yield guard before forwarding to the downstream consumer.
    fn subscribe(
        &mut self,
        intent_guard: Guard,
        consumer: Box<dyn Consumer>,
        var_scope: Option<Rc<VarScope>>,
        scheduler: &mut Scheduler,
    ) -> Box<dyn Producer> {
        let producer_intent_guard = Guard::Record(
            self.input
                .extent()
                .record_fields()
                .expect("Expected Record input Extent in RecordField::subscribe")
                .keys()
                .map(|field| {
                    if *field == self.field {
                        (field.clone(), intent_guard.clone())
                    } else {
                        (field.clone(), Guard::Empty)
                    }
                })
                .collect(),
        );

        Box::new(RecordFieldProducer::new(
            self.input
                .subscribe(producer_intent_guard, consumer, var_scope, scheduler),
            self.field.clone(),
        ))
    }
}

/// Runtime producer for [`RecordField`].
///
/// Wraps the underlying record producer and, on each [`Producer::get`] call, extracts
/// the target field's data from the returned `ColumnData::Records`.
#[derive(Debug)]
struct RecordFieldProducer {
    /// The upstream record producer.
    record: Box<dyn Producer>,
    /// The name of the field to extract from each record batch.
    field: String,
}

impl RecordFieldProducer {
    fn new(record: Box<dyn Producer>, field: String) -> Self {
        Self { record, field }
    }
}

impl Producer for RecordFieldProducer {
    /// Fetches the record batch and returns only the target field's column.
    ///
    /// Also extracts the per-field yield guard from the record-level yield guard, so the
    /// caller sees a plain (non-record) guard appropriate to the field's type.
    fn get(&mut self) -> GetResult {
        let record_get_result = self.record.get();

        let output_data = match record_get_result.column_value {
            ColumnValue::Records(mut m) => m.remove(&self.field).unwrap(),
            _ => panic!("Expected input records"),
        };

        let output_yield_guard = match record_get_result.yield_guard {
            g if g.is_empty() || g.is_universal() => g,
            Guard::Record(m) => m.get(&self.field).unwrap().clone(),
            g => panic!("Unexpected yield guard {g:?}"),
        };
        GetResult {
            column_value: output_data,
            yield_guard: output_yield_guard,
        }
    }

    /// Releases interest in the upstream record producer.
    ///
    /// This producer cannot express partial per-field release to the record producer, so
    /// any non-universal obsolete guard is treated as `Empty`. This is conservative but
    /// correct: we release the whole record once we are completely done with the field.
    ///
    /// TODO: to do a more fine-grained release, we need to be able to get the record schema
    /// here and construct a `Guard::Record` with the appropriate sub-guard for the target field and
    /// `Guard::Universal` for the other fields.
    fn release(&mut self, obsolete_guard: Guard) -> Guard {
        match &self.record.release(obsolete_guard.to_universal_or_empty()) {
            g if g.is_empty() || g.is_universal() => g.clone(),
            Guard::Record(m) if m.contains_key(&self.field) => m[&self.field].clone(),
            g => panic!("Unexpected yield guard {g:?}"),
        }
    }

    fn inspect(&self, opts: &VizOptions) -> InspectNode {
        InspectNode::new(format!("RecordFieldProducer(\"{}\")", self.field))
            .child("record", self.record.inspect(opts))
    }
}

pub fn tuple_field(index: usize) -> String {
    format!("_{}", index)
}
