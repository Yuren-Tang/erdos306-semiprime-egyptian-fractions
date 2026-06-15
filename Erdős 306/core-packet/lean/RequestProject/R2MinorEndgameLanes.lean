import RequestProject.R2BlockMinorLane
import RequestProject.R2ExtraMinorLane
import RequestProject.R2MinorSupportPipeline

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor endgame lanes

This leaf packages the final minor-arc endgame:

* a classification chooses block and extra frequency supports;
* the block support is discharged by the G7/fiber-tail lane;
* the extra support is discharged by per-frequency gadget witnesses.

The output is exactly the `R2MinorSupportBudgetData` consumed by the final R2
assembly sockets.
-/

/-- Per-main-arc block-minor data for the G7/fiber-tail budget. -/
structure R2BlockFiberTailData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock : Finset ℕ) (Bblock η Ctail : ℝ) where
  C : ℝ
  K : ℝ
  Qextra : ℕ → ℝ
  hC : 1 ≤ C
  hK : 0 ≤ K
  heL : ∀ e ∈ D.E, e ∣ D.L
  he0 : ∀ e ∈ D.E, 0 < e
  hL : 0 < D.L
  hQE : ∀ h ∈ blockMinorPart MA.Sm Sblock,
    Qctrl D.BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE D.E h
  hnotmain : ∀ h ∈ blockMinorPart MA.Sm Sblock,
    (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) ∉ mainArc D.BS C
  hfiber : ∀ a : GlobalAssignment D.BS,
    ∑ h ∈ (blockMinorPart MA.Sm Sblock).filter
      (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) = a),
      Real.exp (-(16 / 9 : ℝ) * Qextra h) ≤ K
  hbudget :
    K * ((η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl D.BS)
      ≤ Bblock

/-- The two analytic minor lanes for a fixed classification. -/
structure R2MinorEndgameLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail : ℝ)
    (Cls : R2MinorClassificationData D W N) where
  block : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2BlockFiberTailData D W N MA (Cls.Sblock MA) Bblock η Ctail
  extra : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2ExtraMinorWitnessData D W N MA (Cls.Sblock MA) (Cls.Sextra MA) Bextra

/-- G7 plus the packaged block/extra lanes produce the final minor support
budget record. -/
theorem exists_r2_minorSupportBudget_from_endgame_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Bblock Bextra : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameLanes D W N Bblock Bextra η Ctail Cls →
      Nonempty (R2MinorSupportBudgetData D W N Bblock Bextra) := by
  obtain ⟨k0min, Ctail, hCtail, hblockG7⟩ :=
    exists_r2_block_minor_budget_from_fiber_tail_g7 eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Bblock Bextra Cls hk0 hadm Lanes
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
    exact r2_extra_minor_budget_of_witnessData D W N MA
      (Cls.Sblock MA) (Cls.Sextra MA) Bextra (Lanes.extra MA)

end CircleMethod

end
