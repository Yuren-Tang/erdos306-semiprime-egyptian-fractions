import RequestProject.R2ComponentMassReady
import RequestProject.R2ComponentCoreSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 selected-Q ready socket

After the residual mass-batch selector chooses `Q`, the stable control/gadget
component data from the pre-selection concrete datum can be transported to
`D.withQ Q`.  This file is the downstream socket for that workflow.
-/

theorem exists_arcConstruction_of_selectedQ_coreSupply
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (Q : Finset ℕ)
    (W : R2ConcreteData.Weights (D.withQ Q)) (N : ℤ)
    (Bblock Bextra ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale :
      (1 : ℝ) / Real.sqrt (sigmaE2 (D.withQ Q).E W.theta) ≤ (N : ℝ))
    (hρle : ρ ≤ 1 / 10)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ ((D.withQ Q).L : ℤ))
    (S : R2ComponentScaleCoreSupply D N ρ)
    (hcomponentCard :
      ((ctrlEdges D.BS).card + Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (QB : R2MassBatchSupply (D.withQ Q))
    (MB : R2MinorSupportBudgetData (D.withQ Q) W N Bblock Bextra)
    (hextraLight :
      ∑ e ∈ (D.withQ Q).E \ ctrlEdges (D.withQ Q).BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl (D.withQ Q).BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) /
          sigmaCtrl (D.withQ Q).BS) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_componentScaleCardMassSupply hb (D.withQ Q) W
    N Bblock Bextra ρ K (by simpa [R2ConcreteData.withQ] using hadm)
    hNscale hρle hK hNL
    (S.toScaleCardSupply_withQ Q hcomponentCard) QB MB hextraLight hminorCtrl

end CircleMethod

end
