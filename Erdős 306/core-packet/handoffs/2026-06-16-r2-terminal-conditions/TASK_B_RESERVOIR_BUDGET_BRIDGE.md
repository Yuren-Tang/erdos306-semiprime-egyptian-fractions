# Task B: multi-gadget reservoir, budget, and bridge

Please work in the Lean project under `core-packet/lean`.

Create a new file:

```lean
RequestProject/R2ExtraMultiGadgetReservoir.lean
```

Suggested import:

```lean
import RequestProject.R2ExtraMultiGadget
```

Open the usual namespaces:

```lean
open Finset BigOperators GlobalControl

noncomputable section
namespace CircleMethod
```

## Mathematical target

The already proved theorem

```lean
fourierNormWeight_le_multi_gadget_damp
```

shows that one extra frequency \(h\) is damped by

\[
\left(1-\frac{8}{9r^2}\right)^{|G|/2}
\]

provided a finite gadget set \(G\) of primes \(s\) satisfies the sibling
conditions modulo each \(s\) and the denominator-prime mismatch modulo \(r\).

This task packages the reservoir choice and turns it into the abstract data
record:

```lean
R2ExtraMinorMultiGadgetBoundData
```

It is finite bookkeeping, not analytic number theory.

## Required Lean goals

### Goal B1: reservoir structure

Define a finite reservoir structure.  Suggested shape:

```lean
structure R2MultiGadgetReservoir
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra : ℝ) where
  rfun : ℕ → ℕ
  Gset : ℕ → Finset ℕ
  mfun : ℕ → ℤ
  hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R
  hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S
  hGmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    multiGadgetEdges (rfun h) (Gset h) ⊆ D.E
  hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    (h : ZMod s) = (mfun h : ZMod s)
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    2 * |mfun h| < (s : ℤ)
  htheta_lb : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    1 / 3 ≤ W.theta ((rfun h) * s)
  htheta_ub : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    W.theta ((rfun h) * s) ≤ 2 / 3
  hbudget :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) / ((rfun h : ℝ) ^ 2))) ^ (Gset h).card
        ≤ Bextra
```

You may add fields for primality if it makes the bridge simpler, or pull them
from the component supply if you include it as an argument.

### Goal B2: bridge into existing abstract record

Prove a theorem constructing `R2ExtraMinorMultiGadgetBoundData` from the
reservoir.  Suggested shape:

```lean
theorem multiGadgetBoundData_of_reservoir
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ) (Bextra : ℝ)
    (X : R2MultiGadgetReservoir D W N MA Sblock Sextra Bextra)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hθ0 : ∀ e ∈ D.E, 0 ≤ W.theta e)
    (hθ1 : ∀ e ∈ D.E, W.theta e ≤ 1)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (hepos : ∀ e ∈ D.E, 0 < e)
    (hL : 0 < D.L) :
    R2ExtraMinorMultiGadgetBoundData D W N MA Sblock Sextra Bextra
```

The key field is `hfactorMulti`; prove it by applying:

```lean
fourierNormWeight_le_multi_gadget_damp
```

with:

- `r := X.rfun h`
- `G := X.Gset h`
- `m := X.mfun h`
- `hr := hRprime _ (X.hRmem h hh)`
- `hs := fun s hs => hSprime s (X.hSmem h hh hs)`
- `hrs` follows from `hlt`: if `r < s`, then `r ≠ s`.
- `hGmem := X.hGmem h hh`
- theta bounds from `X.htheta_lb`, `X.htheta_ub`
- congruence and smallness from `X.hm_s`, `X.hm_r`, `X.hm_small`
- global theta/period/positivity assumptions from theorem arguments.

Then set:

```lean
damp h := Real.sqrt (1 - (8 / 9) / ((X.rfun h : ℝ) ^ 2))
```

and use `X.hbudget`.

### Goal B3: simple cardinal budget lemma

Also prove the generic finite budget lemma:

```lean
theorem sum_pow_le_of_pointwise_le
    {A : Finset ℕ} {d : ℕ → ℝ} {G : ℕ → Finset ℕ} {B : ℝ}
    (hpt : ∀ h ∈ A, d h ^ (G h).card ≤ B / A.card)
    ... :
    ∑ h ∈ A, d h ^ (G h).card ≤ B
```

You may choose a cleaner statement, e.g. avoid division:

```lean
theorem sum_pow_le_of_pointwise_le_division_free
    {A : Finset ℕ} {d : ℕ → ℝ} {G : ℕ → Finset ℕ} {C B : ℝ}
    (hcard : (A.card : ℝ) * C ≤ B)
    (hpt : ∀ h ∈ A, d h ^ (G h).card ≤ C) :
    ∑ h ∈ A, d h ^ (G h).card ≤ B
```

This division-free version is preferred.

## What not to do

- Do not edit `R2FinalAssembly*.lean`.
- Do not build the whole project.
- Do not use `sorry`, `admit`, or new axioms.

## Build target

```bash
lake build RequestProject.R2ExtraMultiGadgetReservoir
```

