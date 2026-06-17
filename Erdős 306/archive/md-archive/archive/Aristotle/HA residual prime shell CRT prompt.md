# Aristotle prompt: residual-prime shell CRT interface

Copy this to Aristotle after `PrimitiveProjectiveNormalization.lean`.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is a larger exact-algebra interface task. It is **not** to prove the final
asymptotic CRT interval estimate, SBEE, entropy bounds, or analytic number
theory. The goal is to formalize the precise bridge from anchored primitive
rays to the six-variable CRT interval object which is now the remaining
paper-side arithmetic problem.

Create a new file:

```text
RequestProject/ResidualPrimeShellCRT.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.AnchoredCRTLattice
import RequestProject.ValidCRTLattice
import RequestProject.ReciprocalCRTProduct
import RequestProject.PrimitiveProjectiveNormalization
```

If `PrimitiveProjectiveNormalization.lean` is not available in the current
project package, omit that import and proceed with the anchored CRT imports.

## Mathematical background

An anchored ray has equations

$$
q_i x_i-q_0x_0=p\,y_i\qquad(1\le i\le4).
$$

Subtracting the fourth equation gives

$$
q_i x_i-q_4x_4=p\,a_i,\qquad a_i=y_i-y_4
\qquad(1\le i\le3),
$$

and the anchor equation is

$$
q_4x_4-q_0x_0=p\,y_4.
$$

When $a_1,a_2,a_3,y_4$ are invertible modulo
$q_1,q_2,q_3,q_4$, respectively, this gives four local CRT congruences:

$$
p\equiv -q_4x_4a_i^{-1}\pmod {q_i}\qquad(1\le i\le3),
$$

and

$$
p\equiv -q_0x_0y_4^{-1}\pmod {q_4}.
$$

The remaining paper theorem is an upper bound for short six-tuples

$$
(x_0,x_4,y_4,a_1,a_2,a_3)
$$

whose CRT residue lies in $[X,2X]$. Your task is to formalize the exact
algebraic bridge to that object.

## Goal 1: six-variable CRT shell definitions

Define a structure or predicate for the six short variables:

```lean
structure SixVarCRTData where
  x0 x4 y4 a1 a2 a3 : Int
```

Define the local invertibility witnesses, using the existing
`InvModWitness` if available:

```lean
structure SixVarInvWitnesses
    (D : SixVarCRTData) (q1 q2 q3 q4 : Int) where
  inv1 inv2 inv3 inv4 : Int
  h1 : InvModWitness D.a1 q1 inv1
  h2 : InvModWitness D.a2 q2 inv2
  h3 : InvModWitness D.a3 q3 inv3
  h4 : InvModWitness D.y4 q4 inv4
```

If names differ in the imported files, adapt them.

Define the six-variable local CRT residue predicate:

```lean
def SixVarLocalCRT
    (p q0 q1 q2 q3 q4 : Int)
    (D : SixVarCRTData)
    (W : SixVarInvWitnesses D q1 q2 q3 q4) : Prop :=
  p ≡ D.x4 * (-q4 * W.inv1) [ZMOD q1] ∧
  p ≡ D.x4 * (-q4 * W.inv2) [ZMOD q2] ∧
  p ≡ D.x4 * (-q4 * W.inv3) [ZMOD q3] ∧
  p ≡ D.x0 * (-q0 * W.inv4) [ZMOD q4]
```

Equivalent sign conventions are fine, provided they match the divisibility
equations.

## Goal 2: anchored hit produces six-variable CRT data

From an `AnchoredCRTProductHit`, define

$$
D=(x_0,x_4,y_4,a_1,a_2,a_3).
$$

Prove that if inverse witnesses for $a_1,a_2,a_3,y_4$ are supplied, then
`SixVarLocalCRT p q0 q1 q2 q3 q4 D W` holds.

Suggested theorem shape:

```lean
theorem sixVarLocalCRT_of_anchoredCRTProductHit
    (H : AnchoredCRTProductHit ...)
    (W : SixVarInvWitnesses (sixVarData_of_anchored H) q1 q2 q3 q4) :
    SixVarLocalCRT p q0 q1 q2 q3 q4 (sixVarData_of_anchored H) W
```

Use the existing divisibility and local residue lemmas from
`AnchoredCRTLattice.lean` when possible.

## Goal 3: converse reconstruction from six-variable divisibility

Define a divisibility version which does not mention inverses:

```lean
def SixVarDivisibility
    (p q0 q1 q2 q3 q4 : Int) (D : SixVarCRTData) : Prop :=
  q1 ∣ p * D.a1 + q4 * D.x4 ∧
  q2 ∣ p * D.a2 + q4 * D.x4 ∧
  q3 ∣ p * D.a3 + q4 * D.x4 ∧
  q4 ∣ p * D.y4 + q0 * D.x0
```

Prove that such data reconstructs normalized anchored coordinates by setting

$$
x_i=\frac{p a_i+q_4x_4}{q_i}\qquad(1\le i\le3),
$$

and

$$
y_i=a_i+y_4.
$$

The target theorem can construct either an `AnchoredCRTProductHit` or an
`InAnchoredCRTLattice` predicate, whichever fits the imported API better.

## Goal 4: zero-denominator cleanup shell

Formalize the simple algebraic obstruction:

If $q_i,q_4$ are coprime, $0<|x_i|<|q_4|$, $0<|x_4|<|q_i|$, and

$$
q_i x_i=q_4x_4,
$$

then contradiction.

Use this to prove paper-facing lemmas of the following kind, with hypotheses
kept explicit if necessary:

- from a short anchored ray, $a_i\ne0$;
- from a short anchored ray, $y_4\ne0$;
- hence the only missing inputs for `SixVarLocalCRT` are modular inverses,
  which follow from nonzero shortness when the moduli are prime.

If primality/gcd API gets heavy, prove the coprime versions and leave
prime-to-coprime conversion as separate small lemmas.

## Goal 5: interval-hit language

Define a paper-facing predicate:

```lean
def SixVarCRTIntervalHit
    (X p q0 q1 q2 q3 q4 : Int)
    (D : SixVarCRTData)
    (W : SixVarInvWitnesses D q1 q2 q3 q4) : Prop :=
  X ≤ p ∧ p ≤ 2 * X ∧
  SixVarLocalCRT p q0 q1 q2 q3 q4 D W
```

Also define a version using strict inequalities or natural-number bounds if
more convenient. The exact interval convention is not important; the bridge is.

Then prove:

```lean
theorem intervalHit_of_anchoredCRTProductHit ...
```

from an anchored hit plus interval hypotheses for $p$.

## Optional Goal 6: fixed-height shell packaging

If time allows, define a height predicate for the six variables and state the
abstract analytic endpoint as a hypothesis:

```lean
def SixVarCRTIntervalBoundStatement : Prop := ...
```

Then prove a theorem showing how this statement implies the corresponding
residual-prime shell bound, assuming the already-formalized fixed-$p$ primitive
normalization/fibre bound as a hypothesis. This can be a clean abstract
dependency theorem, not an analytic proof.

## Expected result

- `RequestProject/ResidualPrimeShellCRT.lean` compiles with no `sorry`.
- Main goals are the definitions and theorems in Goals 1--5.
- Goal 6 is optional but valuable if the interface is going smoothly.
- Do not introduce SBEE or analytic assumptions except as explicitly named
  paper-facing predicates.

Paper-side meaning:

$$
\text{anchored primitive ray}
\Longrightarrow
\text{short six-variable CRT interval hit}.
$$

This is the exact algebraic interface for the remaining residual-prime shell
inverse theorem.
