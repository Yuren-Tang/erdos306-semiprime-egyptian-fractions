import RequestProject.R2MinorReadyArc
import RequestProject.R2ExtraGadgetChoice

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor endgame from concrete gadget choices

This terminal wrapper consumes the most concrete extra-minor data currently
available: per-frequency choices `r_h ∈ R`, `s_h ∈ S`, and the sibling residue
`m_h`.  Prime/distinct/edge-membership bookkeeping is supplied by the component
package.
-/

/-- Endgame lanes where the extra-minor side supplies concrete choices from
`D.R` and `D.S`. -/
structure R2MinorEndgameChoiceLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail ρ : ℝ)
    (Cls : R2MinorClassificationData D W N) where
  component : R2ComponentScaleCoreSupply D N ρ
  block : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2BlockFiberTailData D W N MA (Cls.Sblock MA) Bblock η Ctail
  extra : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2ExtraMinorGadgetChoiceData D W N MA (Cls.Sblock MA) (Cls.Sextra MA) Bextra

/-- Convert concrete choice lanes into gadget-membership lanes. -/
def r2_minorEndgameGadgetLanes_of_choiceLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail ρ : ℝ)
    (Cls : R2MinorClassificationData D W N)
    (Lanes : R2MinorEndgameChoiceLanes D W N Bblock Bextra η Ctail ρ Cls) :
    R2MinorEndgameGadgetLanes D W N Bblock Bextra η Ctail Cls where
  block := Lanes.block
  extra := fun MA =>
    r2_extraMinorGadgetMemData_of_choiceData D W N MA
      (Cls.Sblock MA) (Cls.Sextra MA) Bextra ρ Lanes.component (Lanes.extra MA)

/-- G7 plus block lanes and concrete extra choices produce the final minor
support-budget record. -/
theorem exists_r2_minorSupportBudget_from_choice_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Bblock Bextra ρ : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameChoiceLanes D W N Bblock Bextra η Ctail ρ Cls →
      Nonempty (R2MinorSupportBudgetData D W N Bblock Bextra) := by
  obtain ⟨k0min, Ctail, hCtail, hminor⟩ :=
    exists_r2_minorSupportBudget_from_gadget_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Bblock Bextra ρ Cls hk0 hadm Lanes
  exact hminor D W N Bblock Bextra Cls hk0 hadm
    (r2_minorEndgameGadgetLanes_of_choiceLanes D W N Bblock Bextra η Ctail ρ Cls Lanes)

/-- Concrete choice lanes with scaled constants produce minor-ready data. -/
theorem exists_r2_minorReady_from_choice_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Ablock Aextra ρ : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameChoiceLanes D W N
        (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) η Ctail ρ Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      Nonempty (R2MinorReadyData D W N) := by
  obtain ⟨k0min, Ctail, hCtail, hready⟩ :=
    exists_r2_minorReady_from_gadget_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Ablock Aextra ρ Cls hk0 hadm Lanes hscaled
  exact hready D W N Ablock Aextra Cls hk0 hadm
    (r2_minorEndgameGadgetLanes_of_choiceLanes D W N
      (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) η Ctail ρ Cls Lanes)
    hscaled

end CircleMethod

end
