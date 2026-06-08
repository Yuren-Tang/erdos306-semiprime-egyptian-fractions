# Aristotle prompt: valid CRT hits and lattice rays

Copy this to Aristotle after `ReciprocalCRTProduct.lean`, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is a larger interface-building task. It is **not** to prove prime
estimates, equidistribution, entropy bounds, or SBEE. The goal is to strengthen
the algebraic interface from bare local CRT product hits to **valid quotient
hits** and the associated homogeneous lattice/ray structure.

Create a new file:

```text
RequestProject/ValidCRTLattice.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.ReciprocalCRTProduct
```

## Background

`ReciprocalCRTProduct.lean` proves that a four-seed line witness gives local
CRT product congruences:

$$
p\equiv x_4(-q_4a_i^{-1})\pmod {q_i}.
$$

For the paper, a bare CRT product hit is only a necessary condition. The actual
cluster witness also requires the quotient variables

$$
x_i=\frac{p\,a_i+q_4x_4}{q_i}
$$

to be nonzero and short. Algebraically, this means the variables lie in the
homogeneous lattice

$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3).
$$

Please formalize this valid-hit and lattice-ray interface.

## Goal 1: valid CRT hit structure

Define a structure bundling the valid quotient data:

```lean
structure ValidCRTProductHit where
  p q1 q2 q3 q4 : Int
  x4 x1 x2 x3 : Int
  a1 a2 a3 : Int
  h1 : q1 * x1 - q4 * x4 = p * a1
  h2 : q2 * x2 - q4 * x4 = p * a2
  h3 : q3 * x3 - q4 * x4 = p * a3
```

No bounds are needed yet. This is pure algebra.

Also define a paper-facing predicate version if useful:

```lean
def IsValidCRTProductHit
    (p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 : Int) : Prop := ...
```

## Goal 2: bridge from four-seed line witness

Prove that a `FourSeedLineWitness` from `ReciprocalCRTProduct.lean` produces a
`ValidCRTProductHit` using the base differences

$$
a_i=y_i-y_4.
$$

Suggested theorem:

```lean
theorem validCRTProductHit_of_fourSeedLineWitness
    (W : FourSeedLineWitness) : ValidCRTProductHit
```

or an equivalent theorem with fields filled explicitly.

Also prove the converse bridge. Given a `ValidCRTProductHit`, construct a
`FourSeedLineWitness` by taking

$$
y_4=0,\qquad c=q_4x_4,\qquad y_i=a_i\quad(1\le i\le3).
$$

Indeed the valid-hit equations imply

$$
q_i x_i=p\,a_i+q_4x_4
$$

for $1\le i\le3$, and the fourth equation is

$$
q_4x_4=p\cdot0+q_4x_4.
$$

Suggested theorem:

```lean
theorem fourSeedLineWitness_of_validCRTProductHit
    (V : ValidCRTProductHit) : FourSeedLineWitness
```

Any field-normalized equivalent is fine.

## Goal 3: valid hit implies bare CRT hit under inverse witnesses

Prove that a valid hit, together with inverse witnesses for `a1`, `a2`, `a3`
modulo `q1`, `q2`, `q3`, implies the existing `CRTProductHit`.

Suggested theorem:

```lean
theorem crtProductHit_of_validCRTProductHit
    (V : ValidCRTProductHit)
    (inv1 inv2 inv3 : Int)
    (hInv1 : InvModWitness V.a1 V.q1 inv1)
    (hInv2 : InvModWitness V.a2 V.q2 inv2)
    (hInv3 : InvModWitness V.a3 V.q3 inv3) :
    CRTProductHit V.q1 V.q2 V.q3 V.q4 V.p V.x4
      V.a1 V.a2 V.a3 inv1 inv2 inv3
```

Use `local_residue_of_baseDivides` or reprove the short algebra if easier.

## Goal 4: homogeneous lattice predicate

Define the lattice predicate:

```lean
def InCRTLattice
    (p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 : Int) : Prop :=
  q1 * x1 - q4 * x4 = p * a1 ∧
  q2 * x2 - q4 * x4 = p * a2 ∧
  q3 * x3 - q4 * x4 = p * a3
```

Bridge:

```lean
theorem inCRTLattice_of_validCRTProductHit ...
theorem validCRTProductHit_of_inCRTLattice ...
```

or equivalent constructor/projection theorems.

## Goal 5: scaling/ray property

Prove that the lattice is homogeneous in the short variables:

```lean
theorem inCRTLattice_smul
    {p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 lam : Int}
    (h : InCRTLattice p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3) :
    InCRTLattice p q1 q2 q3 q4
      (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * a1) (lam * a2) (lam * a3)
```

Also prove the corresponding theorem for `ValidCRTProductHit`, producing a new
valid hit with all short variables multiplied by `lam`.

## Goal 6: zero-coordinate diagnostics

Formalize simple diagnostics that help exclude false-positive CRT hits:

1. If `p = q4`, `a_i = -x4`, and `q_i ≠ 0`, then the equation
   `q_i*x_i - q4*x4 = p*a_i` forces `x_i = 0`.
2. More generally, prove projection lemmas:

```lean
theorem xi_eq_div_numer_of_validHit ...
```

or a divisibility statement saying `q_i ∣ p*a_i + q4*x4`.

Do whatever is cleanest in Lean. The goal is to make the difference between a
bare CRT hit and a valid quotient hit explicit.

## Goal 7: optional primitive-ray predicate

If feasible, define a primitive predicate by absence of a common integer divisor
larger than `1` among the seven short coordinates:

```lean
def PrimitiveCRTRay
    (x4 x1 x2 x3 a1 a2 a3 : Int) : Prop := ...
```

Possible formulation:

```lean
∀ d : Int, 1 < |d| →
  (d ∣ x4 ∧ d ∣ x1 ∧ d ∣ x2 ∧ d ∣ x3 ∧
   d ∣ a1 ∧ d ∣ a2 ∧ d ∣ a3) → False
```

Then prove:

- scaling by `lam` with `|lam| > 1` makes a nonzero ray non-primitive;
- if a primitive ray is scaled and remains primitive, then `|lam| = 1`.

This goal is optional. Do not get stuck on gcd API issues.

## Expected result

- `RequestProject/ValidCRTLattice.lean` compiles with no `sorry`.
- Goals 1--6 are the main target.
- Goal 7 is optional but valuable.
- No number theory, no asymptotics, no SBEE.

Paper-side meaning:

$$
\text{four cluster incidences}
\Longleftrightarrow
\text{valid short point in }L_p(T),
$$

and the remaining hard theorem is a primitive-ray concentration estimate for
these homogeneous lattices, summed over residual primes.
