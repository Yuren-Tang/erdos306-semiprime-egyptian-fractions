import RequestProject.R2MassBatchWeights
import RequestProject.R2MinorBudgetNumerics

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass-batch endpoint with scaled minor budgets

This leaf keeps the final auto-weight sockets stable while exposing the form
produced by the block/extra minor lanes: separate constants `Ablock`, `Aextra`
above `Bblock * sigmaCtrl`, `Bextra * sigmaCtrl`, whose sum beats the main-term
constant.
-/

/-- Component/mass socket with auto weights and scaled minor budgets. -/
theorem exists_arcConstruction_of_componentScaleCardMassSupply_autoWeights_scaledBudget
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b) (hbpos : 0 < b)
    (D : R2ConcreteData T b) (N : ℤ)
    (Bblock Bextra Ablock Aextra ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hρle : ρ ≤ 1 / 10)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (S : R2ComponentScaleCardSupply D N ρ K)
    (QB : R2MassBatchSupply D)
    (hNscale :
      (1 : ℝ) / Real.sqrt (sigmaE2 D.E (QB.weights hbpos).theta) ≤ (N : ℝ))
    (MB : R2MinorSupportBudgetData D (QB.weights hbpos) N Bblock Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hblockBudget : Bblock ≤ Ablock / sigmaCtrl D.BS)
    (hextraBudget : Bextra ≤ Aextra / sigmaCtrl D.BS)
    (hscaled : Ablock + Aextra < r2MinorMainCtrlConstant) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_componentScaleCardMassSupply_autoWeights hb hbpos D N
    Bblock Bextra ρ K hadm hρle hK hNL S QB hNscale MB hextraLight
    (r2_minor_ctrl_from_scaled_budgets_admissible D Bblock Bextra Ablock Aextra
      hadm hblockBudget hextraBudget hscaled)

/-- Selected-`Q` endpoint with auto weights and scaled minor budgets. -/
theorem exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_scaledBudget
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b) (hbpos : 0 < b)
    (D : R2ConcreteData T b) (Q : Finset ℕ) (N : ℤ)
    (Bblock Bextra Ablock Aextra ρ K : ℝ)
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
    (MB : R2MinorSupportBudgetData (D.withQ Q) (QB.weights hbpos) N Bblock Bextra)
    (hextraLight :
      ∑ e ∈ (D.withQ Q).E \ ctrlEdges (D.withQ Q).BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl (D.withQ Q).BS) ^ 2)
    (hblockBudget : Bblock ≤ Ablock / sigmaCtrl (D.withQ Q).BS)
    (hextraBudget : Bextra ≤ Aextra / sigmaCtrl (D.withQ Q).BS)
    (hscaled : Ablock + Aextra < r2MinorMainCtrlConstant) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_selectedQ_coreSupply_autoWeights hb hbpos D Q N
    Bblock Bextra ρ K hadm hρle hK hNL S hcomponentCard QB hNscale MB
    hextraLight
    (r2_minor_ctrl_from_scaled_budgets_admissible (D.withQ Q)
      Bblock Bextra Ablock Aextra hadm hblockBudget hextraBudget hscaled)

end CircleMethod

end
