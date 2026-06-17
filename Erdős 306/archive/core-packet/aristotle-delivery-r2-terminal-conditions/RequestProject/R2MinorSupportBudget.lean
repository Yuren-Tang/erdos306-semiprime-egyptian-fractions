import RequestProject.R2ComponentNumericAssembly

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor support/budget package

This thin downstream leaf packages the minor-support data consumed by the final
R2 assembly.  It is deliberately only a record/wrapper layer: the actual block
and extra analytic estimates can be proved independently and then inserted as
fields.
-/

/-- Packaged minor support and norm-sum budgets for a fixed concrete R2 setup. -/
structure R2MinorSupportBudgetData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra : ℝ) where
  Sblock : MainArcFields D.E W.theta b D.L N → Finset ℕ
  Sextra : MainArcFields D.E W.theta b D.L N → Finset ℕ
  hcover : ∀ MA : MainArcFields D.E W.theta b D.L N,
    MA.Sm ⊆ Sblock MA ∪ Sextra MA
  hblock : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
      fourierNormWeight D.E W.theta b D.L h ≤ Bblock
  hextra : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra

/-- Current strongest final R2 socket with the minor support/budget lane
packaged as one record. -/
theorem exists_arcConstruction_of_component_rho_numeric_minor_budget
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hρnonneg : 0 ≤ ρ)
    (hρle : ρ ≤ 1 / 10)
    (hctrlpos : ∀ e ∈ ctrlEdges D.BS, 0 < e)
    (hctrledge : ∀ e ∈ ctrlEdges D.BS, (N : ℝ) ≤ ρ * (e : ℝ))
    (hQpos : ∀ e ∈ D.Q, 0 < e)
    (hQedge : ∀ e ∈ D.Q, (N : ℝ) ≤ ρ * (e : ℝ))
    (hgadgetpos : ∀ e ∈ gadgetEdges D.R D.S, 0 < e)
    (hgadgetedge : ∀ e ∈ gadgetEdges D.R D.S, (N : ℝ) ≤ ρ * (e : ℝ))
    (hcomponentCard :
      ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hQsemi : ∀ e ∈ D.Q, IsSemiprime e)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hQavoid : ∀ e ∈ D.Q, e ∉ T)
    (hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T)
    (hQne : D.Q.Nonempty)
    (hQdvd : ∀ e ∈ D.Q, e ∣ D.L)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS)
    (hloadDisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))
    (hloadLower :
      3 / (2 * (b : ℝ)) ≤ D.baseLoad + R2ConcreteData.recipLoad D.Q)
    (hloadUpper :
      D.baseLoad + R2ConcreteData.recipLoad D.Q < 3 / (b : ℝ))
    (MB : R2MinorSupportBudgetData D W N Bblock Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_component_rho_numeric_minor_sets hb D W N
    Bblock Bextra ρ K hadm hNscale hρnonneg hρle
    hctrlpos hctrledge hQpos hQedge hgadgetpos hgadgetedge
    hcomponentCard hK hNL hQsemi hRprime hSprime hlt hctrlAvoid hQavoid
    hgadgetAvoid hQne hQdvd hRdvd hSblock hloadDisj hloadLower hloadUpper
    MB.Sblock MB.Sextra MB.hcover MB.hblock MB.hextra hextraLight hminorCtrl

end CircleMethod

end
