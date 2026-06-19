# Aristotle prompt: reciprocal CRT product interface

Copy this to Aristotle after `ClusterLineIncidence.lean`, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is a larger interface-building task. It is still **not** to prove prime
estimates, entropy bounds, equidistribution, or SBEE. The goal is to formalize
the algebraic reduction:

$$
\text{four seed points on one reciprocal-cluster line}
\Longrightarrow
\text{CRT product congruence for }p.
$$

Create a new file:

```text
RequestProject/ReciprocalCRTProduct.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.ClusterLineIncidence
```

## Mathematical background

Suppose four seed equations lie on the same line:

$$
q_i x_i=p\,y_i+c
\qquad(1\le i\le4).
$$

Use the fourth seed as a base and set

$$
a_i=y_i-y_4
\qquad(1\le i\le3).
$$

Then

$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3).
$$

In particular, modulo $q_i$,

$$
p\,a_i\equiv -q_4x_4\pmod {q_i}.
$$

When $a_i$ is invertible modulo $q_i$, this becomes

$$
p\equiv x_4(-q_4a_i^{-1})\pmod {q_i}.
$$

This is the exact algebraic bridge to the CRT product concentration statement.

## Goal 1: base-difference witness

Define a structure bundling the four same-line equations over integers:

```lean
structure FourSeedLineWitness where
  p c : Int
  q1 q2 q3 q4 : Int
  x1 x2 x3 x4 : Int
  y1 y2 y3 y4 : Int
  h1 : q1 * x1 = p * y1 + c
  h2 : q2 * x2 = p * y2 + c
  h3 : q3 * x3 = p * y3 + c
  h4 : q4 * x4 = p * y4 + c
```

Define:

```lean
def a1 (W : FourSeedLineWitness) : Int := W.y1 - W.y4
def a2 (W : FourSeedLineWitness) : Int := W.y2 - W.y4
def a3 (W : FourSeedLineWitness) : Int := W.y3 - W.y4
```

Prove the base-difference equalities:

```lean
theorem base_diff_1 (W : FourSeedLineWitness) :
  W.q1 * W.x1 - W.q4 * W.x4 = W.p * a1 W
```

and similarly for `2` and `3`.

## Goal 2: divisibility and modular forms

Define integer divisibility predicates:

```lean
def BaseDivides (q p a q4 x4 : Int) : Prop :=
  q ∣ p * a + q4 * x4
```

Prove that a base-difference equality implies:

```lean
BaseDivides W.q1 W.p (a1 W) W.q4 W.x4
```

and similarly for `2`, `3`.

Also prove the equivalent modular statement using `Int.ModEq` if convenient:

```lean
(W.p * a1 W + W.q4 * W.x4) ≡ 0 [ZMOD W.q1]
```

or a comparable theorem. Either divisibility or `Int.ModEq` is acceptable, but
having both is preferred.

## Goal 3: invertible local residue form

Use `ZMod n` or `Int.ModEq` with Bezout witnesses, whichever is easier.

Formalize the statement:

If `a` is invertible modulo `q`, and

$$
q\mid p a+q_4x,
$$

then

$$
p\equiv x(-q_4a^{-1})\pmod q.
$$

A flexible Lean version is fine. For example, define:

```lean
def InvModWitness (a q ainv : Int) : Prop :=
  a * ainv ≡ 1 [ZMOD q]
```

and prove:

```lean
theorem local_residue_of_baseDivides
    {q p a q4 x ainv : Int}
    (hinv : InvModWitness a q ainv)
    (hdiv : BaseDivides q p a q4 x) :
    p ≡ x * (-q4 * ainv) [ZMOD q]
```

Any sign-normalized equivalent is fine.

## Goal 4: three local CRT congruences from a four-seed witness

Bundle the local residue target:

```lean
structure ThreeLocalCRTResidues where
  q1 q2 q3 q4 p x4 : Int
  a1 a2 a3 : Int
  inv1 inv2 inv3 : Int
  hInv1 : InvModWitness a1 q1 inv1
  hInv2 : InvModWitness a2 q2 inv2
  hInv3 : InvModWitness a3 q3 inv3
  hRes1 : p ≡ x4 * (-q4 * inv1) [ZMOD q1]
  hRes2 : p ≡ x4 * (-q4 * inv2) [ZMOD q2]
  hRes3 : p ≡ x4 * (-q4 * inv3) [ZMOD q3]
```

Prove that a `FourSeedLineWitness`, together with inverse witnesses for
`a1 W`, `a2 W`, `a3 W`, produces `ThreeLocalCRTResidues`.

## Goal 5: product-set language

Define a paper-facing predicate:

```lean
def CRTProductHit
    (q1 q2 q3 q4 p x a1 a2 a3 inv1 inv2 inv3 : Int) : Prop :=
  InvModWitness a1 q1 inv1 ∧
  InvModWitness a2 q2 inv2 ∧
  InvModWitness a3 q3 inv3 ∧
  p ≡ x * (-q4 * inv1) [ZMOD q1] ∧
  p ≡ x * (-q4 * inv2) [ZMOD q2] ∧
  p ≡ x * (-q4 * inv3) [ZMOD q3]
```

Prove the bridge theorem:

```lean
theorem crtProductHit_of_fourSeedLineWitness
    ...
```

with whatever arguments are needed, saying that a four-seed line witness plus
three inverse witnesses implies `CRTProductHit`.

## Goal 6: optional exact CRT object

If Mathlib's CRT interface is convenient, define the unique residue modulo
`q1*q2*q3` when the moduli are pairwise coprime. This is optional.

It is enough to keep the result as three local congruences. Do not get stuck on
global CRT uniqueness.

## Expected result

- `RequestProject/ReciprocalCRTProduct.lean` compiles with no `sorry`.
- Goals 1--5 are the main target.
- Goal 6 is optional.
- No primality, no asymptotic estimates, no SBEE.

Paper-side meaning:

$$
\text{four reciprocal-cluster incidences}
\Longrightarrow
p\in x\cdot\mathcal B_T \pmod {q_1q_2q_3}
$$

in local CRT form. The remaining hard theorem is an arithmetic concentration
bound for this product set.
