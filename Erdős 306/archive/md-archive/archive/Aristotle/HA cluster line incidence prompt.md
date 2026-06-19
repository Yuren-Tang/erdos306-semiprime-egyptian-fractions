# Aristotle prompt: reciprocal cluster line-incidence bookkeeping

Copy this to Aristotle after `AdaptiveClusterSelection.lean`, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This task is **not** to prove SBEE, prime estimates, incidence bounds, or
entropy estimates. It formalizes the algebraic bridge from reciprocal-cluster
congruences to integer line incidence and determinant relations.

Create a new file:

```text
RequestProject/ClusterLineIncidence.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.AdaptiveClusterSelection
```

## Goal 1: line incidence predicate

Work over integers.

Define a predicate saying that the point `(y,z)` lies on the line of slope `p`
and intercept `c`:

```lean
def LiesOnLine (p c y z : Int) : Prop :=
  z = p * y + c
```

Define the seed point predicate:

```lean
def SeedPoint (q M y z : Int) : Prop :=
  ∃ x : Int, x ≠ 0 ∧ |x| ≤ M ∧ |y| ≤ M ∧ z = q * x
```

If useful, use `Int.natAbs` or an explicit bounded predicate instead of `| |`
syntax, depending on what is easiest in Lean.

## Goal 2: congruence-to-line identity

Formalize the elementary bridge:

If

```lean
q * x = p * y + c
```

then `(y, q*x)` lies on the line `(p,c)`.

Also formalize the converse in the seed-point setting:

if `(y,z)` is a seed point for `q`, and lies on line `(p,c)`, then there exists
`x` such that

```lean
z = q * x
q * x = p * y + c
```

This is only algebra. No primality or size estimate is needed.

## Goal 3: three-point collinearity determinant

Define the three-point determinant expression:

```lean
def det3 (y1 z1 y2 z2 y3 z3 : Int) : Int :=
  z1 * (y2 - y3) + z2 * (y3 - y1) + z3 * (y1 - y2)
```

Prove:

```lean
theorem det3_eq_zero_of_same_line
    {p c y1 z1 y2 z2 y3 z3 : Int}
    (h1 : LiesOnLine p c y1 z1)
    (h2 : LiesOnLine p c y2 z2)
    (h3 : LiesOnLine p c y3 z3) :
    det3 y1 z1 y2 z2 y3 z3 = 0
```

Then prove the seed-prime expanded version:

```lean
theorem factorable_relation_of_three_seedpoints_on_line
    {p c q1 q2 q3 x1 x2 x3 y1 y2 y3 : Int}
    (h1 : q1 * x1 = p * y1 + c)
    (h2 : q2 * x2 = p * y2 + c)
    (h3 : q3 * x3 = p * y3 + c) :
    q1 * x1 * (y2 - y3)
      + q2 * x2 * (y3 - y1)
      + q3 * x3 * (y1 - y2) = 0
```

Any associativity/commutativity-normalized equivalent statement is fine.

## Goal 4: four-point slope equality

Prove the exact four-point relation for points on the same line:

```lean
theorem four_point_factorable_relation_of_same_line
    {p c q1 q2 q3 q4 x1 x2 x3 x4 y1 y2 y3 y4 : Int}
    (h1 : q1 * x1 = p * y1 + c)
    (h2 : q2 * x2 = p * y2 + c)
    (h3 : q3 * x3 = p * y3 + c)
    (h4 : q4 * x4 = p * y4 + c) :
    (q1 * x1 - q2 * x2) * (y3 - y4)
      = (q3 * x3 - q4 * x4) * (y1 - y2)
```

This is just subtracting the line equations:

```text
q1*x1 - q2*x2 = p*(y1-y2)
q3*x3 - q4*x4 = p*(y3-y4)
```

and cross-multiplying.

## Goal 5: paper-language aliases

Define optional aliases:

```lean
def SameLineSeedTriple ...
def FactorableThreeRelation ...
def FactorableFourRelation ...
```

and prove bridges from `SameLineSeedTriple` to the factorable relations.

## Expected result

- `RequestProject/ClusterLineIncidence.lean` compiles with no `sorry`.
- No new axioms beyond standard Mathlib/classical ones.
- No number theory, no primality, no asymptotics.

Paper-side meaning:

$$
\text{reciprocal cluster through several seeds}
\Longrightarrow
\text{short factorable collinearity relations}.
$$

The analytic/arithmetic inverse theorem will be handled outside this Lean task.
