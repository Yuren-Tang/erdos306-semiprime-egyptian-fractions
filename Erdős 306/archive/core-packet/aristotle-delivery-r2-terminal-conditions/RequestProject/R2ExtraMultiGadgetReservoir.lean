import RequestProject.R2ExtraMultiGadget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor multi-gadget reservoir task

This file is an Aristotle task file.  Please replace the `sorry`s below by
proofs, without adding axioms.
-/

/-- Finite reservoir data sufficient to build the existing abstract
`R2ExtraMinorMultiGadgetBoundData`. -/
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

/-- Division-free finite budget wrapper. -/
theorem sum_pow_le_of_pointwise_le_division_free
    {A : Finset ℕ} {d : ℕ → ℝ} {G : ℕ → Finset ℕ} {C B : ℝ}
    (hcard : (A.card : ℝ) * C ≤ B)
    (hpt : ∀ h ∈ A, d h ^ (G h).card ≤ C) :
    ∑ h ∈ A, d h ^ (G h).card ≤ B := by
  sorry

/-- Convert a concrete reservoir into the already-existing abstract multi-gadget
extra-minor bound data.  The key proof field is obtained from
`fourierNormWeight_le_multi_gadget_damp`. -/
def multiGadgetBoundData_of_reservoir
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
    R2ExtraMinorMultiGadgetBoundData D W N MA Sblock Sextra Bextra := by
  sorry

end CircleMethod

end
