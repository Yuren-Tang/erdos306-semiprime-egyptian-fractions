import RequestProject.R2MassBatchSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 component supply packages

This file packages the remaining control-edge and gadget-edge hypotheses for
the final R2 socket.  The goal is to make the endgame theorem consume a small
number of coherent supply records rather than a long list of component fields.
-/

/-- Supply data for the control-edge component. -/
structure R2ControlSupply
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ) where
  hctrledge : ∀ e ∈ ctrlEdges D.BS, (N : ℝ) ≤ ρ * (e : ℝ)
  hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T

/-- Supply data for the gadget-edge component. -/
structure R2GadgetSupply
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ) where
  hRprime : ∀ r ∈ D.R, Nat.Prime r
  hSprime : ∀ s ∈ D.S, Nat.Prime s
  hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s
  hgadgetedge : ∀ e ∈ gadgetEdges D.R D.S, (N : ℝ) ≤ ρ * (e : ℝ)
  hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T
  hRdvd : ∀ r ∈ D.R, r ∣ b
  hSblock : D.S ⊆ blockSupport D.BS

/-- Final R2 socket with control, gadget, mass-batch, and minor-budget lanes
packaged as records. -/
theorem exists_arcConstruction_of_componentSupplies
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hρnonneg : 0 ≤ ρ)
    (hρle : ρ ≤ 1 / 10)
    (hcomponentCard :
      ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (CS : R2ControlSupply D N ρ)
    (GS : R2GadgetSupply D N ρ)
    (QB : R2MassBatchSupply D)
    (hQedge : ∀ e ∈ D.Q, (N : ℝ) ≤ ρ * (e : ℝ))
    (MB : R2MinorSupportBudgetData D W N Bblock Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_massBatchSupply hb D W N Bblock Bextra ρ K
    hadm hNscale hρnonneg hρle
    CS.hctrledge hQedge GS.hgadgetedge
    hcomponentCard hK hNL
    GS.hRprime GS.hSprime GS.hlt CS.hctrlAvoid GS.hgadgetAvoid
    GS.hRdvd GS.hSblock QB MB hextraLight hminorCtrl

end CircleMethod

end
