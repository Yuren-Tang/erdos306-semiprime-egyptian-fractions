import RequestProject.R2MinorEndgameGadget
import RequestProject.R2ComponentCoreSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor gadget choices

This leaf removes another artificial field from the extra-minor endgame.  If the
per-frequency gadget primes are chosen from the concrete denominator set `R` and
block-support set `S`, then semiprimality, distinctness, and edge membership in
`D.E` follow from the component supply package.
-/

/-- Extra-minor gadget data before the finite-set edge-membership bookkeeping is
filled in from `R2ComponentScaleCoreSupply`. -/
structure R2ExtraMinorGadgetChoiceData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra : ℝ) where
  rfun : ℕ → ℕ
  sfun : ℕ → ℕ
  mfun : ℕ → ℤ
  Dmp : ℝ
  hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R
  hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, sfun h ∈ D.S
  hθlb : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, 1 / 3 ≤ W.theta (rfun h * sfun h)
  hθub : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, W.theta (rfun h * sfun h) ≤ 2 / 3
  hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (sfun h)) = (mfun h : ZMod (sfun h))
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    2 * |mfun h| < (sfun h : ℤ)
  hDmp : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    Real.sqrt (1 - (8 / 9) / (rfun h : ℝ) ^ 2) ≤ Dmp
  hbudget : ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * Dmp ≤ Bextra

/-- A chosen pair `r ∈ D.R`, `s ∈ D.S` gives an actual concrete R2 edge. -/
lemma r2_gadget_product_mem_E_of_mem
    {T : Finset ℕ} {b r s : ℕ}
    (D : R2ConcreteData T b)
    (hr : r ∈ D.R) (hs : s ∈ D.S) :
    r * s ∈ D.E := by
  exact D.gadgetEdges_subset_E (mem_gadgetEdges.mpr ⟨r, hr, s, hs, rfl⟩)

/-- Fill the `R2ExtraMinorGadgetMemData` fields from component-supply
bookkeeping plus explicit per-frequency choices in `R` and `S`. -/
def r2_extraMinorGadgetMemData_of_choiceData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra ρ : ℝ)
    (S : R2ComponentScaleCoreSupply D N ρ)
    (X : R2ExtraMinorGadgetChoiceData D W N MA Sblock Sextra Bextra) :
    R2ExtraMinorGadgetMemData D W N MA Sblock Sextra Bextra where
  rfun := X.rfun
  sfun := X.sfun
  mfun := X.mfun
  Dmp := X.Dmp
  hr := fun h hh => S.hRprime (X.rfun h) (X.hRmem h hh)
  hs := fun h hh => S.hSprime (X.sfun h) (X.hSmem h hh)
  hrs := fun h hh => ne_of_lt (S.hlt (X.rfun h) (X.hRmem h hh) (X.sfun h) (X.hSmem h hh))
  hmem := fun h hh => r2_gadget_product_mem_E_of_mem D (X.hRmem h hh) (X.hSmem h hh)
  hθlb := X.hθlb
  hθub := X.hθub
  hm_s := X.hm_s
  hm_r := X.hm_r
  hm_small := X.hm_small
  hDmp := X.hDmp
  hbudget := X.hbudget

end CircleMethod

end
