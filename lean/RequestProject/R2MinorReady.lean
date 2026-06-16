import RequestProject.R2MinorEndgameLanes
import RequestProject.R2MinorBudgetNumerics

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor ready package

This leaf packages the exact data the final construction sockets need from the
minor-arc analysis: concrete block/extra budgets, the support-budget record,
and the strict main-term domination inequality.
-/

/-- Minor-arc data ready for insertion into the final R2 construction socket. -/
structure R2MinorReadyData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) where
  Bblock : ℝ
  Bextra : ℝ
  MB : R2MinorSupportBudgetData D W N Bblock Bextra
  hminorCtrl :
    Bblock + Bextra <
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS

/-- Endgame lanes with scaled constants below the main-term constant produce
minor-ready data. -/
theorem exists_r2_minorReady_from_endgame_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Ablock Aextra : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameLanes D W N
        (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) η Ctail Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      Nonempty (R2MinorReadyData D W N) := by
  obtain ⟨k0min, Ctail, hCtail, hminor⟩ :=
    exists_r2_minorSupportBudget_from_endgame_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Ablock Aextra Cls hk0 hadm Lanes hscaled
  obtain ⟨MB⟩ := hminor D W N
    (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) Cls hk0 hadm Lanes
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
