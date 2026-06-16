import RequestProject.R2ExtraMultiGadgetReservoir

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor reservoir selection

This file packages the finite per-frequency reservoir selection needed by the
multi-gadget extra-minor endpoint.
-/

/-- Prepared per-frequency data for the multi-gadget extra-minor reservoir.

This record deliberately contains only the choices and the arithmetic/budget
facts that do not follow automatically from `D` and `W`.  The theorem below
fills edge membership and theta bounds from `D.gadgetEdges_subset_E` and
`W.hlb`/`W.hub`.
-/
structure R2ExtraPreparedReservoirChoice
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
  hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    (h : ZMod s) = (mfun h : ZMod s)
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    2 * |mfun h| < (s : ℤ)
  hbudget :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) / ((rfun h : ℝ) ^ 2))) ^ (Gset h).card
        ≤ Bextra

/-- Prepared per-frequency data gives the concrete multi-gadget reservoir. -/
def r2MultiGadgetReservoir_of_preparedChoice
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra : ℝ)
    (X : R2ExtraPreparedReservoirChoice D W N MA Sblock Sextra Bextra) :
    R2MultiGadgetReservoir D W N MA Sblock Sextra Bextra := by
  sorry

/-- Division-free constructor for the `hbudget` field of
`R2ExtraPreparedReservoirChoice`.

This is useful when the selected gadget sets have been made uniformly large
enough that every damped power is at most `C`.
-/
theorem extraPreparedReservoirBudget_of_pointwise_bound
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (rfun : ℕ → ℕ) (Gset : ℕ → Finset ℕ)
    (C Bextra : ℝ)
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) / ((rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) / ((rfun h : ℝ) ^ 2))) ^ (Gset h).card
        ≤ Bextra := by
  sorry

end CircleMethod

end

