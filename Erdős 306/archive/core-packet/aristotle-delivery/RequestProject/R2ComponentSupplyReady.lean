import RequestProject.R2ComponentScaleCard

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 component supplies from scale/cardinality data

This file is a thin socket: it turns the finite scale and cardinality facts for
control/gadget components into the packaged component supplies consumed by the
final R2 assembly.
-/

/-- Scale/cardinality data sufficient for the control and gadget component
records, plus the combined component-cardinality budget. -/
structure R2ComponentScaleCardSupply
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ K : ℝ) where
  hρ : 0 ≤ ρ
  hctrlScale : (N : ℝ) ≤ ρ * ((2 ^ D.BS.k0 * 2 ^ D.BS.k0 : ℕ) : ℝ)
  hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T
  r0 : ℕ
  s0 : ℕ
  hgadgetScale : (N : ℝ) ≤ ρ * ((r0 * s0 : ℕ) : ℝ)
  hRlow : ∀ r ∈ D.R, r0 ≤ r
  hSlow : ∀ s ∈ D.S, s0 ≤ s
  hRprime : ∀ r ∈ D.R, Nat.Prime r
  hSprime : ∀ s ∈ D.S, Nat.Prime s
  hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s
  hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T
  hRdvd : ∀ r ∈ D.R, r ∣ b
  hSblock : D.S ⊆ blockSupport D.BS
  hcomponentCard :
    ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K

/-- The control supply extracted from finite scale/cardinality data. -/
def R2ComponentScaleCardSupply.controlSupply
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b} {N : ℤ} {ρ K : ℝ}
    (S : R2ComponentScaleCardSupply D N ρ K) :
    R2ControlSupply D N ρ :=
  r2ControlSupply_of_k0_square D N ρ S.hρ S.hctrlScale S.hctrlAvoid

/-- The gadget supply extracted from finite scale/cardinality data. -/
def R2ComponentScaleCardSupply.gadgetSupply
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b} {N : ℤ} {ρ K : ℝ}
    (S : R2ComponentScaleCardSupply D N ρ K) :
    R2GadgetSupply D N ρ :=
  r2GadgetSupply_of_mul_scale D N ρ S.r0 S.s0 S.hρ S.hgadgetScale
    S.hRlow S.hSlow S.hRprime S.hSprime S.hlt S.hgadgetAvoid S.hRdvd
    S.hSblock

/-- Final R2 socket using the finite scale/cardinality component package. -/
theorem exists_arcConstruction_of_componentScaleCardSupply
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
    (hQedge : ∀ e ∈ D.Q, (N : ℝ) ≤ ρ * (e : ℝ))
    (MB : R2MinorSupportBudgetData D W N Bblock Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_componentSupplies hb D W N Bblock Bextra ρ K
    hadm hNscale S.hρ hρle S.hcomponentCard hK hNL
    S.controlSupply S.gadgetSupply QB hQedge MB hextraLight hminorCtrl

end CircleMethod

end
