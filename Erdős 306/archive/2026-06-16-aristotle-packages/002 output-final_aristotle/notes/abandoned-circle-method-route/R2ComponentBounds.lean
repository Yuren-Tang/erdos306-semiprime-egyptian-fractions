import RequestProject.R2FinalAssemblyRaw

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# Component-wise R2 bounds

This thin leaf turns hypotheses on the three concrete pieces of the R2 edge set
into hypotheses over `D.E`.  It keeps future parameter-selection and task
delegation away from the `r2Edges = ctrl ∪ Q ∪ gadget` bookkeeping.
-/

namespace R2ConcreteData

variable {T : Finset ℕ} {b : ℕ}

/-- Prove a property on all concrete R2 edges by proving it separately on the
control edges, the residual mass batch, and the gadget edges. -/
lemma forall_E_of_components (D : R2ConcreteData T b) {P : ℕ → Prop}
    (hctrl : ∀ e ∈ ctrlEdges D.BS, P e)
    (hQ : ∀ e ∈ D.Q, P e)
    (hgadget : ∀ e ∈ gadgetEdges D.R D.S, P e) :
    ∀ e ∈ D.E, P e := by
  intro e he
  rw [E, r2Edges, Finset.mem_union] at he
  rcases he with hctrlQ | hg
  · rw [Finset.mem_union] at hctrlQ
    rcases hctrlQ with hc | hq
    · exact hctrl e hc
    · exact hQ e hq
  · exact hgadget e hg

/-- Uniform edge lower bounds over components imply the final edge lower bound. -/
lemma edge_lower_of_components (D : R2ConcreteData T b) (N : ℤ)
    (hctrl : ∀ e ∈ ctrlEdges D.BS, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hQ : ∀ e ∈ D.Q, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hgadget : ∀ e ∈ gadgetEdges D.R D.S, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ)) :
    ∀ e ∈ D.E, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ) :=
  D.forall_E_of_components hctrl hQ hgadget

/-- Uniform ratio bounds over components imply the final ratio bound. -/
lemma ratio_bound_of_components (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ)
    (hctrl : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ ctrlEdges D.BS,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hQ : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.Q,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hgadget : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ gadgetEdges D.R D.S,
      |(m : ℝ) / (e : ℝ)| ≤ ρ) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ ρ := by
  intro m hm
  exact D.forall_E_of_components (hctrl m hm) (hQ m hm) (hgadget m hm)

end R2ConcreteData

/-- Raw final assembly with numeric bounds supplied component-wise. -/
theorem exists_arcConstruction_of_component_numeric_minor_sets
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hctrlEdge : ∀ e ∈ ctrlEdges D.BS, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hQEdge : ∀ e ∈ D.Q, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hgadgetEdge : ∀ e ∈ gadgetEdges D.R D.S, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hρnonneg : 0 ≤ ρ)
    (hctrlRatio : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ ctrlEdges D.BS,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hQRatio : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.Q,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hgadgetRatio : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ gadgetEdges D.R D.S,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hcard : (D.E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10)
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
  exact exists_arcConstruction_of_componentData_raw_numeric_minor_sets hb D W N
    Bblock Bextra ρ hadm hNscale
    (D.edge_lower_of_components N hctrlEdge hQEdge hgadgetEdge)
    hρnonneg
    (D.ratio_bound_of_components N ρ hctrlRatio hQRatio hgadgetRatio)
    hcard hNL hQsemi hRprime hSprime hlt hctrlAvoid hQavoid hgadgetAvoid
    hQne hQdvd hRdvd hSblock hloadDisj hloadLower hloadUpper
    Sblock Sextra hcover hblock hextra hextraLight hminorCtrl

end CircleMethod

end
