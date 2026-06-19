# Aristotle prompt: anchored CRT lattice interface

Copy this to Aristotle after `ValidCRTLattice.lean`, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is a larger interface-building task. It is **not** to prove prime
estimates, equidistribution, entropy bounds, or SBEE. The goal is to formalize
the exact reference-anchored algebraic interface for reciprocal clusters.

Create a new file:

```text
RequestProject/AnchoredCRTLattice.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.ValidCRTLattice
```

## Background

`ValidCRTLattice.lean` formalizes the unanchored normalized equations

$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3).
$$

For the actual reciprocal cluster, the line intercept is not arbitrary. It is

$$
c=q_0x_0
$$

where $q_0$ is the reference seed prime. Thus the full anchored equations are:

$$
q_i x_i-q_0x_0=p\,y_i
\qquad(1\le i\le4).
$$

After using $q_4$ as base and setting $a_i=y_i-y_4$, these become

$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3),
$$

together with the reference-anchor equation

$$
q_4x_4-q_0x_0=p\,y_4.
$$

Please formalize this anchored interface.

## Goal 1: anchored cluster witness

Define a structure bundling the original anchored equations:

```lean
structure AnchoredClusterWitness where
  p q0 q1 q2 q3 q4 : Int
  x0 x1 x2 x3 x4 : Int
  y1 y2 y3 y4 : Int
  h1 : q1 * x1 - q0 * x0 = p * y1
  h2 : q2 * x2 - q0 * x0 = p * y2
  h3 : q3 * x3 - q0 * x0 = p * y3
  h4 : q4 * x4 - q0 * x0 = p * y4
```

Define base differences:

```lean
def aa1 (W : AnchoredClusterWitness) : Int := W.y1 - W.y4
def aa2 (W : AnchoredClusterWitness) : Int := W.y2 - W.y4
def aa3 (W : AnchoredClusterWitness) : Int := W.y3 - W.y4
```

Use names different from `a1/a2/a3` if those already conflict.

## Goal 2: anchored normalized lattice

Define:

```lean
structure AnchoredCRTProductHit where
  p q0 q1 q2 q3 q4 : Int
  x0 x4 x1 x2 x3 : Int
  y4 a1 a2 a3 : Int
  h1 : q1 * x1 - q4 * x4 = p * a1
  h2 : q2 * x2 - q4 * x4 = p * a2
  h3 : q3 * x3 - q4 * x4 = p * a3
  h4 : q4 * x4 - q0 * x0 = p * y4
```

Also define a predicate version:

```lean
def InAnchoredCRTLattice
    (p q0 q1 q2 q3 q4 x0 x4 x1 x2 x3 y4 a1 a2 a3 : Int) : Prop := ...
```

with the four displayed equations.

## Goal 3: bidirectional bridge

Prove:

```lean
theorem anchoredCRTProductHit_of_anchoredClusterWitness
    (W : AnchoredClusterWitness) : AnchoredCRTProductHit
```

using $a_i=y_i-y_4$.

Prove the converse:

```lean
theorem anchoredClusterWitness_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit) : AnchoredClusterWitness
```

by setting

$$
y_i=a_i+y_4
\qquad(1\le i\le3).
$$

Any field-normalized equivalent is fine.

## Goal 4: anchored implies unanchored valid hit

Prove that an anchored hit gives the existing unanchored `ValidCRTProductHit`
from `ValidCRTLattice.lean` by forgetting `q0,x0,y4,h4`.

Suggested theorem:

```lean
theorem validCRTProductHit_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit) : ValidCRTProductHit
```

or an equivalent constructor theorem.

## Goal 5: local CRT congruences, including the anchor

For the first three equations, reuse or mirror the valid-hit bridge to
`CRTProductHit`.

For the anchor equation, define/prove the fourth local residue:

If

$$
q_4x_4-q_0x_0=p\,y_4,
$$

and $y_4$ has inverse `inv4` modulo `q4`, then

$$
p\equiv -q_0x_0\,y_4^{-1}\pmod {q_4}.
$$

Suggested predicate:

```lean
def AnchoredCRTProductHit
    (q0 q1 q2 q3 q4 p x0 x4 a1 a2 a3 y4
      inv1 inv2 inv3 inv4 : Int) : Prop := ...
```

This can include the existing three local residues plus the fourth anchor
residue. Choose a different name if it conflicts with the structure above.

The exact packaging is flexible. The important theorem is:

```lean
theorem anchoredCRTResidues_of_anchoredCRTProductHit
    ...
```

stating that an anchored valid hit plus inverse witnesses for
`a1,a2,a3,y4` gives all four local congruences.

## Goal 6: homogeneous scaling

Prove that the anchored lattice is homogeneous in all short variables:

```lean
theorem inAnchoredCRTLattice_smul
    {p q0 q1 q2 q3 q4 x0 x4 x1 x2 x3 y4 a1 a2 a3 lam : Int}
    (h : InAnchoredCRTLattice p q0 q1 q2 q3 q4
          x0 x4 x1 x2 x3 y4 a1 a2 a3) :
    InAnchoredCRTLattice p q0 q1 q2 q3 q4
      (lam * x0) (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * y4) (lam * a1) (lam * a2) (lam * a3)
```

Also prove the corresponding constructor for `AnchoredCRTProductHit`.

## Goal 7: primitive anchored ray

Define a primitive predicate for the nine short coordinates:

```lean
def PrimitiveAnchoredCRTRay
    (x0 x4 x1 x2 x3 y4 a1 a2 a3 : Int) : Prop := ...
```

Use the same style as `PrimitiveCRTRay` from `ValidCRTLattice.lean`: no
integer divisor with absolute value greater than `1` divides all coordinates.

Prove:

- scaling by `lam` with `|lam| > 1` destroys primitivity of a nonzero anchored
  ray;
- if a scaled anchored ray is primitive, then `|lam| ≤ 1`.

If this is API-heavy, keep the predicate and prove the easier direction first.

## Goal 8: optional zero diagnostics

Prove simple diagnostics:

- if $q_i\ne0$, $q_4\ne0$, and an anchored equation degenerates with the
  corresponding difference variable zero in the legal short-prime regime, then
  the relevant $x$-coordinate must be zero;
- projection/divisibility lemmas for all four equations.

This is optional but useful for paper-side exception handling.

## Expected result

- `RequestProject/AnchoredCRTLattice.lean` compiles with no `sorry`.
- Goals 1--6 are the main target.
- Goal 7 is strongly preferred.
- Goal 8 is optional.
- No number theory, no asymptotics, no SBEE.

Paper-side meaning:

$$
\text{actual reciprocal cluster through four seeds}
\Longleftrightarrow
\text{short point in the reference-anchored lattice}.
$$

The remaining hard theorem is the reference-anchored primitive concentration
estimate.
