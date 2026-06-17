import RequestProject.R2MinorReady
import RequestProject.R2ExtraMultiGadgetReservoir
import RequestProject.R2ComponentCoreSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor endgame with multi-gadget extra data

This is the terminal minor-arc package using the multi-gadget extra reservoir.
It parallels `R2MinorEndgameGadget`, but the extra lane is discharged by
`R2ExtraMinorMultiGadgetBoundData` rather than a single selected gadget factor.
-/

/-- Endgame lanes where the extra-minor side supplies a finite multi-gadget
reservoir for every main arc. -/
structure R2MinorEndgameMultiGadgetLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail ρ : ℝ)
    (Cls : R2MinorClassificationData D W N) where
  component : R2ComponentScaleCoreSupply D N ρ
  block : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2BlockFiberTailData D W N MA (Cls.Sblock MA) Bblock η Ctail
  extra : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2MultiGadgetReservoir D W N MA (Cls.Sblock MA) (Cls.Sextra MA) Bextra

/-- G7 plus block lanes and multi-gadget extra lanes produce the final minor
support-budget record. -/
theorem exists_r2_minorSupportBudget_from_multiGadget_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Bblock Bextra ρ : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameMultiGadgetLanes D W N Bblock Bextra η Ctail ρ Cls →
      Nonempty (R2MinorSupportBudgetData D W N Bblock Bextra) := by
  obtain ⟨k0min, Ctail, hCtail, hblockG7⟩ :=
    exists_r2_block_minor_budget_from_fiber_tail_g7 eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Bblock Bextra ρ Cls hk0 hadm Lanes
  refine ⟨r2_minorSupportBudget_of_classification_and_budgetLanes D W N
    Bblock Bextra Cls ?_⟩
  refine {
    hblock := ?_
    hextra := ?_
  }
  · intro MA
    let X := Lanes.block MA
    exact hblockG7 D W N MA (Cls.Sblock MA) Bblock X.C X.K X.Qextra
      hk0 hadm X.hC X.hK X.heL X.he0 X.hL X.hQE X.hnotmain X.hfiber X.hbudget
  · intro MA
    let X : R2ExtraMinorMultiGadgetBoundData D W N MA
        (Cls.Sblock MA) (Cls.Sextra MA) Bextra :=
      multiGadgetBoundData_of_reservoir D W N MA
        (Cls.Sblock MA) (Cls.Sextra MA) Bextra (Lanes.extra MA)
        Lanes.component.hRprime Lanes.component.hSprime Lanes.component.hlt
        (fun e he => by
          have hle := W.hlb e he
          norm_num at hle ⊢
          linarith)
        (fun e he => by
          have hle := W.hub e he
          norm_num at hle ⊢
          linarith)
        (Lanes.block MA).heL (Lanes.block MA).he0 (Lanes.block MA).hL
    exact r2_extra_minor_budget_of_multiGadgetBoundData D W N MA
      (Cls.Sblock MA) (Cls.Sextra MA) Bextra X

/-- Multi-gadget lanes with scaled block/extra constants produce minor-ready
data. -/
theorem exists_r2_minorReady_from_multiGadget_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Ablock Aextra ρ : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameMultiGadgetLanes D W N
        (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) η Ctail ρ Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      Nonempty (R2MinorReadyData D W N) := by
  obtain ⟨k0min, Ctail, hCtail, hminor⟩ :=
    exists_r2_minorSupportBudget_from_multiGadget_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Ablock Aextra ρ Cls hk0 hadm Lanes hscaled
  obtain ⟨MB⟩ := hminor D W N
    (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) ρ Cls hk0 hadm Lanes
  refine ⟨{
    Bblock := Ablock / sigmaCtrl D.BS
    Bextra := Aextra / sigmaCtrl D.BS
    MB := MB
    hminorCtrl := ?_
  }⟩
  exact r2_minor_ctrl_from_scaled_budgets_admissible D
    (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) Ablock Aextra
    hadm le_rfl le_rfl hscaled

end CircleMethod

end
