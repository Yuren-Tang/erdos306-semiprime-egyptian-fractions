import RequestProject.R2ExtraReservoirSelection

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor reservoir: uniform-budget constructor

This optional companion to `R2ExtraReservoirSelection` packages the
uniform-budget shortcut: when every extra frequency has a gadget set whose
damped power is at most a single constant `C`, and `extraPart.card * C ≤ Bextra`,
the finite damping budget required by `R2ExtraPreparedReservoirChoice` follows
automatically.
-/

/-- Uniform-budget constructor for `R2ExtraPreparedReservoirChoice`.

Given the per-frequency choices together with the CRT sibling congruences and
small-label bounds, plus a *uniform* pointwise damping bound `C` and the linear
budget inequality `extraPart.card * C ≤ Bextra`, we obtain the prepared choice
record.  The finite budget field is discharged by
`extraPreparedReservoirBudget_of_pointwise_bound`. -/
def preparedChoice_of_pointwise_budget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (C Bextra : ℝ)
    (rfun : ℕ → ℕ) (Gset : ℕ → Finset ℕ) (mfun : ℕ → ℤ)
    (hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R)
    (hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S)
    (hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      (h : ZMod s) = (mfun h : ZMod s))
    (hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h)))
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      2 * |mfun h| < (s : ℤ))
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) / ((rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    R2ExtraPreparedReservoirChoice D W N MA Sblock Sextra Bextra :=
  { rfun := rfun
    Gset := Gset
    mfun := mfun
    hRmem := hRmem
    hSmem := hSmem
    hm_s := hm_s
    hm_r := hm_r
    hm_small := hm_small
    hbudget :=
      extraPreparedReservoirBudget_of_pointwise_bound
        D W N MA Sblock Sextra rfun Gset C Bextra hcard hpt }

/-- Composing the uniform-budget prepared choice with the reservoir constructor
gives a concrete `R2MultiGadgetReservoir` directly from the per-frequency data
and the uniform pointwise damping bound. -/
def r2MultiGadgetReservoir_of_pointwise_budget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (C Bextra : ℝ)
    (rfun : ℕ → ℕ) (Gset : ℕ → Finset ℕ) (mfun : ℕ → ℤ)
    (hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R)
    (hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S)
    (hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      (h : ZMod s) = (mfun h : ZMod s))
    (hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h)))
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      2 * |mfun h| < (s : ℤ))
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) / ((rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    R2MultiGadgetReservoir D W N MA Sblock Sextra Bextra :=
  r2MultiGadgetReservoir_of_preparedChoice D W N MA Sblock Sextra Bextra
    (preparedChoice_of_pointwise_budget D W N MA Sblock Sextra C Bextra
      rfun Gset mfun hRmem hSmem hm_s hm_r hm_small hcard hpt)

end CircleMethod

end
