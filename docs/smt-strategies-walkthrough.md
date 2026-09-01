# Problem

Suppose we have a recursive function `sum` on lists of Ints.

And then we have `append`, for which we have verified the following refinement type:

```
append(x:List(Int), y:Int) => {List(Int) where sum(_) == sum(x) + y}:
    ...
```

We want a program that adds an Int and its negative to the list, and
we want to show that the overall sum is unchanged.

```
double_entry(x:List(Int), y:Int) => {List(Int) where sum(_) == sum(x)}:
    a = append(x,y)
    b = append(a,-y)
    b
```

How does type inference proceed?

# Inline!

In the inline approach, we are checking that:

```
∀x:List(Int). ∀y:Int. sum(append(append(x,y), -y)) == sum(x)
```

But this can only be successful if we assume the refinement type of
`append` as an axiom:

```
not (∀n:List(Int). ∀m:Int. sum(append(n,m)) == sum(n) + m)

or

∀x:List(Int). ∀y:Int. sum(append(append(x,y), -y)) == sum(x)
```

The quantifiers in the goal are okay, but the ones in the axiom take
us out of any decidable logic fragment.

```
(declare-sort ListInt 0)
(declare-fun append (ListInt Int) ListInt)
(declare-fun sum (ListInt) Int)

; axiom
(assert
  (forall ((n ListInt) (m Int))
    (= (sum (append n m)) (+ (sum n) m))))

; negated conclusion
(assert
  (exists ((x ListInt) (y Int))
    (not (= (sum (append (append x y) (- y))) (sum x)))))

(check-sat)
(get-model)
```

Two problems with undecidability:

1. Less predictable, scalable solving times.
2. Hard to get a counterexample when solving fails.

# Liquid Types

In the Liquid Types approach, we avoid the quantifier problem by
withholding the axiom from the solver. This means that the solver
can't prove the goal, because it doesn't know anything about the
input/output behavior of `append`. And so we must simplify the goal by
removing reference to `append`.

```
double_entry(x:List(Int), y:Int) => {List(Int) where sum(_) == sum(x)}:
    a: κ1 = append(x,y)
    b: κ2 = -y
    c: κ3 = append(a,b)
    c
    # whole body is z: κ4
```

Create some type vars a:κ1, b:κ2, c:κ3, and κ4 for the body, and add
constraints:

* κ1 can only talk about [x,y]
* κ2 can only talk about [x,y,a]
* κ3 can only talk about [x,y,a,b]
* κ4 can only talk about [x,y]
...
* κ3 <: κ4
...

```
double_entry(x:List(Int), y:Int) => {List(Int) where sum(_) == sum(x)}:
    a: {sum(_) == sum(x) + y}             = append(x,y)
    b: {_ == -y}                          = -y
    c: {sum(_) == sum(a) + b}             = append(a,b)
    c
    # whole body is z: {sum(_) == sum(x)}
```

And this produces a system of equations to solve, with only top-level
∀ quantifiers.

```
∀x,y,z,a,b,c.
      sum(a) == sum(x) + y
    ∧ b      == -y
    ∧ sum(c) == sum(a) + b
    ∧ sum(z) == sum(x)
```

Top-level ∀ quantifiers don't cause a problem because they are treated as constant declarations in the negated SMT query.

```
(declare-const x ListInt)
...
(declare-const c ListInt)

assert (not ([equations converted to SMT]))

(check-sat)
```
