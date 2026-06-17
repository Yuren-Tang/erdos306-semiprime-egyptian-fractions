# Aristotle prompt: anchored determinant rank obstruction

Copy this to Aristotle after `AnchoredSelectionPipeline.lean`.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is an exact algebra task, and you should feel free to be somewhat
ambitious. It is **not** to prove any asymptotic estimate, entropy estimate, or
SBEE. The goal is to formalize the determinant obstruction behind the
reference-anchored primitive concentration problem.

Create a new file:

```text
RequestProject/AnchoredDeterminantRank.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.AnchoredCRTLattice
```

## Mathematical background

An anchored hit has equations

$$
q_i x_i-q_0x_0=p\,y_i
\qquad(1\le i\le4).
$$

If two anchored hits for the same $p,q_0,q_i$ are

$$
(x_0,x_i,y_i)
\qquad\text{and}\qquad
(z_0,z_i,w_i),
$$

then multiplying the first equation by $z_0$, the second by $x_0$, and
subtracting gives

$$
q_i(x_i z_0-z_i x_0)=p(y_i z_0-w_i x_0).
$$

If $p$ is coprime to $q_i$, then

$$
p\mid x_i z_0-z_i x_0.
$$

If additionally

$$
|x_i z_0-z_i x_0|<|p|,
$$

then

$$
x_i z_0=z_i x_0.
$$

This is the fixed-$p$ projective-rank test: in a sufficiently small box, two
short hits for the same residual prime are projectively proportional.

## Goal 1: two-hit structure

Define a structure bundling two anchored cluster witnesses with the same
ambient parameters. Suggested:

```lean
structure TwoAnchoredHits where
  p q0 q1 q2 q3 q4 : Int
  x0 x1 x2 x3 x4 : Int
  z0 z1 z2 z3 z4 : Int
  y1 y2 y3 y4 : Int
  w1 w2 w3 w4 : Int
  hx1 : q1 * x1 - q0 * x0 = p * y1
  ...
  hz4 : q4 * z4 - q0 * z0 = p * w4
```

You may instead define a predicate if that is cleaner.

## Goal 2: determinant identity

Define

```lean
def detRef (xi zi x0 z0 : Int) : Int := xi * z0 - zi * x0
def detY (yi wi x0 z0 : Int) : Int := yi * z0 - wi * x0
```

Prove four identities:

```lean
theorem det_identity_1 (W : TwoAnchoredHits) :
  W.q1 * detRef W.x1 W.z1 W.x0 W.z0 =
    W.p * detY W.y1 W.w1 W.x0 W.z0
```

and similarly for `2,3,4`.

Use `ring`, `linarith`, or `linear_combination` as convenient.

## Goal 3: determinant divisibility

Prove that if `Int.Coprime W.p W.qi`, then

```lean
W.p ∣ detRef W.xi W.zi W.x0 W.z0
```

for each `i`.

If the exact `Int.Coprime` API is annoying, prove a version with the hypothesis

```lean
∀ a, W.p ∣ W.qi * a -> W.p ∣ a
```

or define a helper predicate `PrimeDoesNotDivideFactor p qi`.

## Goal 4: small determinant vanishing

Prove a general integer lemma:

```lean
theorem eq_zero_of_dvd_of_abs_lt
    {p d : Int} (hp : 0 < |p|) (hdvd : p ∣ d) (hlt : |d| < |p|) :
    d = 0
```

or any equivalent Mathlib-friendly form.

Then prove:

```lean
theorem det_eq_zero_of_small_1
    (W : TwoAnchoredHits)
    (hcop : Int.Coprime W.p W.q1)
    (hsmall : |detRef W.x1 W.z1 W.x0 W.z0| < |W.p|) :
    detRef W.x1 W.z1 W.x0 W.z0 = 0
```

and similarly for `2,3,4`.

## Goal 5: projective proportionality predicate

Define a paper-facing predicate:

```lean
def SameRefProjective
    (x0 x1 x2 x3 x4 z0 z1 z2 z3 z4 : Int) : Prop :=
  x1 * z0 = z1 * x0 ∧
  x2 * z0 = z2 * x0 ∧
  x3 * z0 = z3 * x0 ∧
  x4 * z0 = z4 * x0
```

Prove that the four small determinant conclusions imply
`SameRefProjective`.

Optional stronger result: if both five-coordinate vectors are primitive and
`x0,z0` have the same sign or one normalized coordinate is fixed, then the two
vectors are equal up to sign. This may be API-heavy; attempt it if feasible, but
do not get stuck.

## Goal 6: factorable relation from one anchored witness

From an `AnchoredClusterWitness`, prove the pairwise elimination identity:

$$
q_i x_i y_j-q_j x_j y_i+q_0x_0(y_i-y_j)=0.
$$

Define a predicate:

```lean
def FactorableAnchoredRelation
    (q0 qi qj x0 xi xj yi yj : Int) : Prop :=
  qi * xi * yj - qj * xj * yi + q0 * x0 * (yi - yj) = 0
```

Prove it for all pairs among `1,2,3,4`, or at least for pairs `(1,2)`,
`(1,3)`, `(1,4)` with clear names.

## Goal 7: optional inverse-language shell

If time permits, define a structure bundling many pairwise factorable
relations, for example:

```lean
structure AnchoredFactorableShell where
  q0 q1 q2 q3 q4 : Int
  x0 x1 x2 x3 x4 : Int
  y1 y2 y3 y4 : Int
  rel12 : FactorableAnchoredRelation q0 q1 q2 x0 x1 x2 y1 y2
  ...
```

and prove that every `AnchoredClusterWitness` produces this shell.

## Expected result

- `RequestProject/AnchoredDeterminantRank.lean` compiles with no `sorry`.
- Main goals are 1--5 and at least one version of Goal 6.
- Goal 7 and primitive up-to-sign uniqueness are optional stretch goals.
- No number theory beyond elementary divisibility/coprimality; no asymptotics.

Paper-side meaning:

$$
\text{two fixed-}p\text{ anchored rays}
\Longrightarrow
\text{projective proportionality or a small determinant divisible by }p.
$$

This is the first exact algebraic sublemma in the weighted anchored primitive
inverse theorem.
