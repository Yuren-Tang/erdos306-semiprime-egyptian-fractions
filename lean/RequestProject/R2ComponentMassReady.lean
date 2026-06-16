import RequestProject.R2ComponentSupplyReady
import RequestProject.R2MassBatchScale

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 component and mass-batch ready socket

This leaf combines the packaged component scale/cardinality data with the
mass-batch structural package.  The `Q` edge-scale hypothesis is no longer a
separate input: it follows from `R2MassBatchSupply.hQpair` and the same bottom
block-support scale used for control edges.
-/

theorem exists_arcConstruction_of_componentScaleCardMassSupply
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hρle : ρ ≤ 1 / 10)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (S : R2ComponentScaleCardSupply D N ρ K)
    (QB : R2MassBatchSupply D)
    (MB : R2MinorSupportBudgetData D W N Bblock Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_componentScaleCardSupply hb D W N Bblock
    Bextra ρ K hadm hNscale hρle hK hNL S QB
    (massBatchEdges_scale_of_k0_square QB N ρ S.hρ S.hctrlScale)
    MB hextraLight hminorCtrl

end CircleMethod

end
