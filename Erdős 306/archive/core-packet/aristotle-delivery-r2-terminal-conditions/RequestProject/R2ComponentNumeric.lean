import RequestProject.R2ComponentBounds

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 component numeric / cardinality helpers

This thin downstream leaf makes the numeric hypotheses of

```
CircleMethod.exists_arcConstruction_of_component_numeric_minor_sets
```

easier to supply from component-level parameter choices.  It provides:

* generic "absolute-value over edge ⇒ ratio bound" helpers,
* component ratio wrappers (control / mass-batch / gadget) that feed
  `R2ConcreteData.ratio_bound_of_components`,
* a cardinality bound for the R2 edge set and its real-valued cubic
  consequence,
* an optional lightweight package of the numeric data.

Nothing thick upstream is modified.
-/

namespace R2ConcreteData

variable {T : Finset ℕ} {b : ℕ}

/-! ## 1. Generic ratio bounds -/

/-- Pointwise ratio bound: from `|m| ≤ N` and `N ≤ ρ·e` with `0 < e` we get
`|m / e| ≤ ρ`. -/
lemma ratio_bound_pointwise {m N e ρ : ℝ}
    (hepos : 0 < e) (hm : |m| ≤ N) (hedge : N ≤ ρ * e) :
    |m / e| ≤ ρ := by
  rw [abs_div, abs_of_pos hepos, div_le_iff₀ hepos]
  exact hm.trans hedge

/-- Ratio bound over an arbitrary edge set: from edge positivity and a uniform
edge lower bound `N ≤ ρ·e` we get `|m / e| ≤ ρ` for all labels `m` in the symmetric
window `[-N, N]`. -/
lemma ratio_bound_on_edgeSet (Edges : Finset ℕ) (N : ℤ) (ρ : ℝ)
    (hepos : ∀ e ∈ Edges, 0 < e)
    (hedge : ∀ e ∈ Edges, (N : ℝ) ≤ ρ * (e : ℝ)) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ Edges,
      |(m : ℝ) / (e : ℝ)| ≤ ρ := by
  intro m hm e he
  rw [Finset.mem_Icc] at hm
  have h1 : (-(N : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hm.1
  have h2 : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm.2
  have hmabs : |(m : ℝ)| ≤ (N : ℝ) := abs_le.mpr ⟨h1, h2⟩
  have hepos' : (0 : ℝ) < (e : ℝ) := by exact_mod_cast hepos e he
  exact ratio_bound_pointwise hepos' hmabs (hedge e he)

/-- The `ρ = 1/10` specialization driven directly by the `10·N ≤ e` edge lower
bound used by the final assembly. -/
lemma ratio_bound_tenth_on_edgeSet (Edges : Finset ℕ) (N : ℤ)
    (hepos : ∀ e ∈ Edges, 0 < e)
    (hedge : ∀ e ∈ Edges, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ)) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ Edges,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10 := by
  refine ratio_bound_on_edgeSet Edges N (1 / 10) hepos ?_
  intro e he
  have := hedge e he
  linarith

/-! ## 2. Component ratio wrappers -/

/-- Assemble the final ratio bound over `D.E` from positivity and the uniform
edge lower bound `N ≤ ρ·e` on each of the three components. -/
lemma ratio_bound_of_component_edges (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ)
    (hctrlpos : ∀ e ∈ ctrlEdges D.BS, 0 < e)
    (hctrledge : ∀ e ∈ ctrlEdges D.BS, (N : ℝ) ≤ ρ * (e : ℝ))
    (hQpos : ∀ e ∈ D.Q, 0 < e)
    (hQedge : ∀ e ∈ D.Q, (N : ℝ) ≤ ρ * (e : ℝ))
    (hgadgetpos : ∀ e ∈ gadgetEdges D.R D.S, 0 < e)
    (hgadgetedge : ∀ e ∈ gadgetEdges D.R D.S, (N : ℝ) ≤ ρ * (e : ℝ)) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ ρ :=
  D.ratio_bound_of_components N ρ
    (ratio_bound_on_edgeSet (ctrlEdges D.BS) N ρ hctrlpos hctrledge)
    (ratio_bound_on_edgeSet D.Q N ρ hQpos hQedge)
    (ratio_bound_on_edgeSet (gadgetEdges D.R D.S) N ρ hgadgetpos hgadgetedge)

/-- The `ρ = 1/10` component wrapper, taking the `10·N ≤ e` edge lower bounds on
each component directly. -/
lemma ratio_bound_tenth_of_component_edges (D : R2ConcreteData T b) (N : ℤ)
    (hctrlpos : ∀ e ∈ ctrlEdges D.BS, 0 < e)
    (hctrledge : ∀ e ∈ ctrlEdges D.BS, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hQpos : ∀ e ∈ D.Q, 0 < e)
    (hQedge : ∀ e ∈ D.Q, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hgadgetpos : ∀ e ∈ gadgetEdges D.R D.S, 0 < e)
    (hgadgetedge : ∀ e ∈ gadgetEdges D.R D.S, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ)) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10 :=
  D.ratio_bound_of_components N (1 / 10)
    (ratio_bound_tenth_on_edgeSet (ctrlEdges D.BS) N hctrlpos hctrledge)
    (ratio_bound_tenth_on_edgeSet D.Q N hQpos hQedge)
    (ratio_bound_tenth_on_edgeSet (gadgetEdges D.R D.S) N hgadgetpos hgadgetedge)

/-! ## 3. Cardinality bounds -/

/-- The R2 edge set has at most as many elements as the sum of the cardinalities
of its three components. -/
lemma r2Edges_card_le_components (D : R2ConcreteData T b) :
    D.E.card ≤
      (ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card := by
  have h1 : D.E = ctrlEdges D.BS ∪ D.Q ∪ gadgetEdges D.R D.S := rfl
  rw [h1]
  refine (Finset.card_union_le _ _).trans ?_
  have h2 := Finset.card_union_le (ctrlEdges D.BS) D.Q
  omega

/-- Real-valued cardinality bound for `D.E`. -/
lemma r2Edges_card_le_components_real (D : R2ConcreteData T b) :
    (D.E.card : ℝ) ≤
      ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) := by
  exact_mod_cast D.r2Edges_card_le_components

/-- The cubic card condition transferred from the component card bound: if the
sum of component cardinalities is `≤ K` and `K·100000·ρ³ ≤ 1/10`, then the same
cubic bound holds for `D.E.card`. -/
lemma cubic_card_bound_of_component_card_bound (D : R2ConcreteData T b) (ρ K : ℝ)
    (hρnonneg : 0 ≤ ρ)
    (hcard :
      ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10) :
    (D.E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10 := by
  have hcardE : (D.E.card : ℝ) ≤ K := D.r2Edges_card_le_components_real.trans hcard
  have hfac : (0 : ℝ) ≤ 100000 * ρ ^ 3 := by positivity
  calc (D.E.card : ℝ) * 100000 * ρ ^ 3
      = (D.E.card : ℝ) * (100000 * ρ ^ 3) := by ring
    _ ≤ K * (100000 * ρ ^ 3) := mul_le_mul_of_nonneg_right hcardE hfac
    _ = K * 100000 * ρ ^ 3 := by ring
    _ ≤ 1 / 10 := hK

end R2ConcreteData

end CircleMethod

end
