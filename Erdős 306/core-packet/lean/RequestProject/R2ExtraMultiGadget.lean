import RequestProject.R2FourierFactor

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor multi-gadget interface

The earlier one-gadget extra lane is useful locally, but the terminal R2
argument needs several gadget factors for each extra frequency.  This file
records the correct budget interface without yet choosing the gadgets.
-/

/-- Multi-gadget extra-minor data after the pointwise product damping has been
proved.  The field `Gset h` is the finite set of block-side gadget primes used
for frequency `h`, while `damp h` is the per-frequency damping base. -/
structure R2ExtraMinorMultiGadgetBoundData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra : ℝ) where
  rfun : ℕ → ℕ
  Gset : ℕ → Finset ℕ
  mfun : ℕ → ℤ
  damp : ℕ → ℝ
  hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R
  hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S
  hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    (h : ZMod s) = (mfun h : ZMod s)
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    2 * |mfun h| < (s : ℤ)
  hfactorMulti : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    fourierNormWeight D.E W.theta b D.L h ≤ damp h ^ (Gset h).card
  hbudget :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra, damp h ^ (Gset h).card ≤ Bextra

/-- Multi-gadget extra data gives the extra-minor norm-sum budget. -/
theorem r2_extra_minor_budget_of_multiGadgetBoundData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ) (Bextra : ℝ)
    (X : R2ExtraMinorMultiGadgetBoundData D W N MA Sblock Sextra Bextra) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra := by
  exact le_trans (Finset.sum_le_sum X.hfactorMulti) X.hbudget

end CircleMethod

end
