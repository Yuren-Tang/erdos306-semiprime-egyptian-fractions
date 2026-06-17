# Task A: CRT coverage and extra-sibling counting

Please work in the Lean project under `core-packet/lean`.

Create a new file:

```lean
RequestProject/R2ExtraCRTSibling.lean
```

Suggested imports:

```lean
import RequestProject.R2ExtraMultiGadget
import RequestProject.FiberCount
```

Open the usual namespaces:

```lean
open Finset BigOperators GlobalControl

noncomputable section
namespace CircleMethod
```

## Mathematical target

We need the finite CRT fact used by the terminal extra-minor argument:

Let \(L=b\prod_{s\in P}s\).  Suppose every block prime \(s\in P\) satisfies
\(h\equiv m\pmod{s}\).  If \(h\not\equiv m\pmod L\), then the failure must occur
at a prime divisor \(r\mid b\).  Therefore, provided the selected finite set
`R` contains all prime divisors of `b`, there exists `r ∈ R` such that
\((h : ZMod r) \ne (m : ZMod r)\).

This is the missing "coverage" condition.  The current project only has
`∀ r ∈ D.R, r ∣ b`; it also needs the converse for prime divisors:

```lean
def CoversPrimeDivisors (R : Finset ℕ) (b : ℕ) : Prop :=
  ∀ r, Nat.Prime r → r ∣ b → r ∈ R
```

## Required Lean goals

### Goal A1: definitions

Define:

```lean
def CoversPrimeDivisors (R : Finset ℕ) (b : ℕ) : Prop :=
  ∀ r, Nat.Prime r → r ∣ b → r ∈ R

def BlockSupportCoprimeWith (BS : BlockSystem) (b : ℕ) : Prop :=
  ∀ s ∈ blockSupport BS, Nat.Coprime s b
```

If the second definition is inconvenient, replace it by the equivalent
assumption directly in the theorem statement.

### Goal A2: CRT sibling lemma

Prove a theorem with this mathematical content.  The exact Lean statement may
be adjusted for available APIs, but it should be close to:

```lean
theorem exists_R_mismatch_of_block_eq_not_global
    (BS : BlockSystem) (R : Finset ℕ) (b L h m : ℕ)
    (hL : L = b * ∏ s ∈ blockSupport BS, s)
    (hbpos : 0 < b)
    (hcover : CoversPrimeDivisors R b)
    (hcop : BlockSupportCoprimeWith BS b)
    (hblock : ∀ s ∈ blockSupport BS, (h : ZMod s) = (m : ZMod s))
    (hnot : ¬ (h : ZMod L) = (m : ZMod L)) :
    ∃ r ∈ R, Nat.Prime r ∧ r ∣ b ∧ (h : ZMod r) ≠ (m : ZMod r)
```

Acceptable variant:

- Replace `ZMod L` by `Nat.ModEq L h m`, if easier.
- Replace the conclusion by `¬ Nat.ModEq r h m`.
- Use an intermediate theorem:

```lean
theorem global_modEq_of_block_and_denominator_modEq
```

stating that block congruences plus congruences modulo every prime divisor of
`b` imply congruence modulo `L`.

Proof idea:

1. Assume no such `r` exists.
2. Then for every prime `r ∣ b`, \(h\equiv m\pmod r\).
3. Since \(b\) is squarefree in the final application, or since one may assume
   directly that congruence modulo all prime divisors implies congruence modulo
   `b`, derive \(h\equiv m\pmod b\).
4. The block-support product is coprime to `b`.
5. Combine congruence modulo `b` and modulo `∏ blockSupport` to get congruence
   modulo `L`, contradiction.

If step 3 is API-heavy, state and prove the theorem under the direct hypothesis
`Nat.ModEq b h m` instead, and add a second lemma isolating the squarefree
prime-divisor-to-`b` step.

### Goal A3: finite extra-sibling counting

Use the existing theorem:

```lean
CircleMethod.mainArc_fiber_card_le
```

to prove a clean counting bound saying: for each fixed block assignment/label,
there are at most `b` frequencies in `range L`, hence after excluding the main
representative, at most `b - 1` extra siblings.

A useful theorem shape:

```lean
theorem extra_sibling_card_le_pred_b
    (BS : BlockSystem) (L b : ℕ)
    (hL : L = b * ∏ p ∈ blockSupport BS, p)
    (a : GlobalAssignment BS)
    (main : ℕ)
    (hmain :
      main ∈ (Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)) :
    (((Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)).erase main).card ≤ b - 1
```

If subtraction causes trouble, an acceptable version is:

```lean
... ≤ b
```

plus a separate lemma under `0 < b` proving the `b - 1` version.

## What not to do

- Do not edit `R2FinalAssembly*.lean`.
- Do not build the whole project.
- Do not use `sorry`, `admit`, or new axioms.

## Build target

```bash
lake build RequestProject.R2ExtraCRTSibling
```

