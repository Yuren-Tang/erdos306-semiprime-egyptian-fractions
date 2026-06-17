import RequestProject.R2ComponentNumeric

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# Component numeric assembly socket

This thin downstream leaf combines the component-numeric helpers with the final
component assembly socket.  Its main purpose is to replace two numeric
hypotheses per component,

* `10 * N <= e`,
* `|m / e| <= rho`,

by one stronger and more natural scale hypothesis `N <= rho * e`, together with
`rho <= 1/10`.
-/

namespace R2ConcreteData

variable {T : Finset ℕ} {b : ℕ}

/-- If `N <= rho * e` and `rho <= 1/10`, then the main-window lower bound
`10*N <= e` follows. -/
lemma edge_lower_tenth_of_rho_edge_lower (Edges : Finset ℕ) (N : ℤ) (ρ : ℝ)
    (hρle : ρ ≤ 1 / 10)
    (hepos : ∀ e ∈ Edges, 0 < e)
    (hedge : ∀ e ∈ Edges, (N : ℝ) ≤ ρ * (e : ℝ)) :
    ∀ e ∈ Edges, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ) := by
  intro e he
  have he_nonneg : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast (hepos e he).le
  have h10ρ : (10 : ℝ) * ρ ≤ 1 := by nlinarith
  have hscale : (10 : ℝ) * (N : ℝ) ≤ (10 * ρ) * (e : ℝ) := by
    nlinarith [hedge e he]
  have htop : (10 * ρ) * (e : ℝ) ≤ (e : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right h10ρ he_nonneg
  exact le_trans hscale htop

end R2ConcreteData

/-- Final component assembly where component numeric bounds are supplied as
`N <= rho * e`, plus a component-cardinality cubic bound. -/
theorem exists_arcConstruction_of_component_rho_numeric_minor_sets
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
    (Sblock Sextra : MainArcFields D.E W.theta b D.L N → Finset ℕ)
    (hcover : ∀ MA : MainArcFields D.E W.theta b D.L N,
      MA.Sm ⊆ Sblock MA ∪ Sextra MA)
    (hblock : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
        fourierNormWeight D.E W.theta b D.L h ≤ Bblock)
    (hextra : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
        fourierNormWeight D.E W.theta b D.L h ≤ Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  have hcard : (D.E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10 :=
    D.cubic_card_bound_of_component_card_bound ρ K hρnonneg hcomponentCard hK
  exact exists_arcConstruction_of_component_numeric_minor_sets hb D W N Bblock Bextra ρ
    hadm hNscale
    (R2ConcreteData.edge_lower_tenth_of_rho_edge_lower
      (ctrlEdges D.BS) N ρ hρle hctrlpos hctrledge)
    (R2ConcreteData.edge_lower_tenth_of_rho_edge_lower
      D.Q N ρ hρle hQpos hQedge)
    (R2ConcreteData.edge_lower_tenth_of_rho_edge_lower
      (gadgetEdges D.R D.S) N ρ hρle hgadgetpos hgadgetedge)
    hρnonneg
    (R2ConcreteData.ratio_bound_on_edgeSet
      (ctrlEdges D.BS) N ρ hctrlpos hctrledge)
    (R2ConcreteData.ratio_bound_on_edgeSet
      D.Q N ρ hQpos hQedge)
    (R2ConcreteData.ratio_bound_on_edgeSet
      (gadgetEdges D.R D.S) N ρ hgadgetpos hgadgetedge)
    hcard hNL hQsemi hRprime hSprime hlt hctrlAvoid hQavoid hgadgetAvoid
    hQne hQdvd hRdvd hSblock hloadDisj hloadLower hloadUpper
    Sblock Sextra hcover hblock hextra hextraLight hminorCtrl

end CircleMethod

end
