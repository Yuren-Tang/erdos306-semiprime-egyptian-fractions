import RequestProject.R2MinorReady
import RequestProject.R2FourierFactor

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor endgame with concrete gadget extra data

This file is the same terminal minor-arc package as `R2MinorEndgameLanes`, but
with the extra-minor side expressed in the newer `R2ExtraMinorGadgetMemData`
interface.  The single-factor Fourier bridge is filled automatically from
`R2FourierFactor`.
-/

/-- Endgame lanes where the extra-minor side only supplies concrete gadget
membership data, not an opaque Fourier-factor bound. -/
structure R2MinorEndgameGadgetLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail : ℝ)
    (Cls : R2MinorClassificationData D W N) where
  block : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2BlockFiberTailData D W N MA (Cls.Sblock MA) Bblock η Ctail
  extra : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2ExtraMinorGadgetMemData D W N MA (Cls.Sblock MA) (Cls.Sextra MA) Bextra

/-- Convert the concrete gadget-lane package into the older endgame-lane
package consumed by `R2MinorReady`. -/
def r2_minorEndgameLanes_of_gadgetLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail : ℝ)
    (Cls : R2MinorClassificationData D W N)
    (Lanes : R2MinorEndgameGadgetLanes D W N Bblock Bextra η Ctail Cls) :
    R2MinorEndgameLanes D W N Bblock Bextra η Ctail Cls where
  block := Lanes.block
  extra := fun MA =>
    r2_extraMinorWitnessData_of_gadgetMemData D W N MA
      (Cls.Sblock MA) (Cls.Sextra MA) Bextra
      (Lanes.block MA).heL (Lanes.block MA).he0 (Lanes.block MA).hL
      (Lanes.extra MA)

/-- G7 plus block lanes and concrete gadget extra lanes produce the final minor
support-budget record. -/
theorem exists_r2_minorSupportBudget_from_gadget_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Bblock Bextra : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameGadgetLanes D W N Bblock Bextra η Ctail Cls →
      Nonempty (R2MinorSupportBudgetData D W N Bblock Bextra) := by
  obtain ⟨k0min, Ctail, hCtail, hready⟩ :=
    exists_r2_minorSupportBudget_from_endgame_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Bblock Bextra Cls hk0 hadm Lanes
  exact hready D W N Bblock Bextra Cls hk0 hadm
    (r2_minorEndgameLanes_of_gadgetLanes D W N Bblock Bextra η Ctail Cls Lanes)

/-- Concrete gadget lanes with scaled block/extra constants produce
minor-ready data. -/
theorem exists_r2_minorReady_from_gadget_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Ablock Aextra : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameGadgetLanes D W N
        (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) η Ctail Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      Nonempty (R2MinorReadyData D W N) := by
  obtain ⟨k0min, Ctail, hCtail, hready⟩ :=
    exists_r2_minorReady_from_endgame_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Ablock Aextra Cls hk0 hadm Lanes hscaled
  exact hready D W N Ablock Aextra Cls hk0 hadm
    (r2_minorEndgameLanes_of_gadgetLanes D W N
      (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS) η Ctail Cls Lanes)
    hscaled

end CircleMethod

end
