import RequestProject.R2MinorEndgameGadget
import RequestProject.R2MassBatchWeights

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# From minor-ready data to `ArcConstruction`

This file connects the minor-arc endgame package to the existing final
`ArcConstruction` sockets.  The point is to consume `R2MinorReadyData` directly,
instead of repeatedly passing its two fields (`MB`, `hminorCtrl`) by hand.
-/

/-- Component/mass endpoint consuming `R2MinorReadyData` directly. -/
theorem exists_arcConstruction_of_componentScaleCardMassSupply_autoWeights_minorReady
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b) (hbpos : 0 < b)
    (D : R2ConcreteData T b) (N : ℤ)
    (ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hρle : ρ ≤ 1 / 10)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (S : R2ComponentScaleCardSupply D N ρ K)
    (QB : R2MassBatchSupply D)
    (hNscale :
      (1 : ℝ) / Real.sqrt (sigmaE2 D.E (QB.weights hbpos).theta) ≤ (N : ℝ))
    (MR : R2MinorReadyData D (QB.weights hbpos) N)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_componentScaleCardMassSupply_autoWeights hb hbpos D N
    MR.Bblock MR.Bextra ρ K hadm hρle hK hNL S QB hNscale MR.MB
    hextraLight MR.hminorCtrl

/-- Selected-`Q` endpoint consuming `R2MinorReadyData` directly. -/
theorem exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_minorReady
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b) (hbpos : 0 < b)
    (D : R2ConcreteData T b) (Q : Finset ℕ) (N : ℤ)
    (ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hρle : ρ ≤ 1 / 10)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ ((D.withQ Q).L : ℤ))
    (S : R2ComponentScaleCoreSupply D N ρ)
    (hcomponentCard :
      ((ctrlEdges D.BS).card + Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (QB : R2MassBatchSupply (D.withQ Q))
    (hNscale :
      (1 : ℝ) / Real.sqrt (sigmaE2 (D.withQ Q).E (QB.weights hbpos).theta)
        ≤ (N : ℝ))
    (MR : R2MinorReadyData (D.withQ Q) (QB.weights hbpos) N)
    (hextraLight :
      ∑ e ∈ (D.withQ Q).E \ ctrlEdges (D.withQ Q).BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl (D.withQ Q).BS) ^ 2) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_selectedQ_coreSupply_autoWeights hb hbpos D Q N
    MR.Bblock MR.Bextra ρ K hadm hρle hK hNL S hcomponentCard QB hNscale
    MR.MB hextraLight MR.hminorCtrl

/-- Selected-`Q` endpoint whose minor arc is supplied by concrete gadget lanes. -/
theorem exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_gadgetMinor
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (_hb : 3 ≤ b) (hbpos : 0 < b)
      (D : R2ConcreteData T b) (Q : Finset ℕ) (N : ℤ)
      (Ablock Aextra ρ K : ℝ)
      (QB : R2MassBatchSupply (D.withQ Q))
      (Cls : R2MinorClassificationData (D.withQ Q) (QB.weights hbpos) N),
      k0min ≤ (D.withQ Q).BS.k0 →
      admissibleGlobalRange (D.withQ Q).BS →
      ρ ≤ 1 / 10 →
      K * 100000 * ρ ^ 3 ≤ 1 / 10 →
      2 * N + 1 ≤ ((D.withQ Q).L : ℤ) →
      R2ComponentScaleCoreSupply D N ρ →
      ((ctrlEdges D.BS).card + Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K →
      (1 : ℝ) / Real.sqrt (sigmaE2 (D.withQ Q).E (QB.weights hbpos).theta)
        ≤ (N : ℝ) →
      R2MinorEndgameGadgetLanes (D.withQ Q) (QB.weights hbpos) N
        (Ablock / sigmaCtrl (D.withQ Q).BS)
        (Aextra / sigmaCtrl (D.withQ Q).BS) η Ctail Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      (∑ e ∈ (D.withQ Q).E \ ctrlEdges (D.withQ Q).BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl (D.withQ Q).BS) ^ 2) →
      Nonempty (ArcConstruction T b) := by
  obtain ⟨k0min, Ctail, hCtail, hminor⟩ :=
    exists_r2_minorReady_from_gadget_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b hb hbpos D Q N Ablock Aextra ρ K QB Cls hk0 hadm hρle hK hNL
    S hcomponentCard hNscale Lanes hscaled hextraLight
  obtain ⟨MR⟩ := hminor (D.withQ Q) (QB.weights hbpos) N Ablock Aextra Cls
    hk0 hadm Lanes hscaled
  exact exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_minorReady hb hbpos
    D Q N ρ K hadm hρle hK hNL S hcomponentCard QB hNscale MR hextraLight

end CircleMethod

end
