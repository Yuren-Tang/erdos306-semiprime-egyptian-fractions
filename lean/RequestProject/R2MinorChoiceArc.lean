import RequestProject.R2MinorEndgameChoice

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 choice-lane endpoint for `ArcConstruction`

This file keeps the final `ArcConstruction` socket separate from the
minor-lane construction files.  It consumes the most concrete current terminal
minor package: block lanes plus explicit extra-gadget choices.
-/

/-- Selected-`Q` endpoint whose minor arc is supplied by concrete extra-gadget
choices. -/
theorem exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_choiceMinor
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
      R2MinorEndgameChoiceLanes (D.withQ Q) (QB.weights hbpos) N
        (Ablock / sigmaCtrl (D.withQ Q).BS)
        (Aextra / sigmaCtrl (D.withQ Q).BS) η Ctail ρ Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      (∑ e ∈ (D.withQ Q).E \ ctrlEdges (D.withQ Q).BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl (D.withQ Q).BS) ^ 2) →
      Nonempty (ArcConstruction T b) := by
  obtain ⟨k0min, Ctail, hCtail, hminor⟩ :=
    exists_r2_minorReady_from_choice_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b hb hbpos D Q N Ablock Aextra ρ K QB Cls hk0 hadm hρle hK hNL
    S hcomponentCard hNscale Lanes hscaled hextraLight
  obtain ⟨MR⟩ := hminor (D.withQ Q) (QB.weights hbpos) N Ablock Aextra ρ Cls
    hk0 hadm Lanes hscaled
  exact exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_minorReady hb hbpos
    D Q N ρ K hadm hρle hK hNL S hcomponentCard QB hNscale MR hextraLight

end CircleMethod

end
