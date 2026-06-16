import RequestProject.ArcConstruction

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2: σ_E ≍ σ_ctrl comparison (the `hbeat` quantitative input)

The minor-arc bound (`minor_arc_bound_fiber_tail`) is measured against `sigmaCtrl BS`,
while the main term (`main_re_lower`) is measured against `√(sigmaE2 E θ) = σ_E`.  The
`hbeat` separation `Bm < c₃/σ_E` therefore needs `σ_E ≲ σ_ctrl`.

The key elementary facts proved here:
* `sigmaE2_le_quarter_sum_inv_sq`: `σ_E² ≤ ¼ ∑_{e∈E} 1/e²` (since `θ(1-θ) ≤ ¼`).
* `sum_inv_sq_ctrlEdges_eq_sigmaCtrl_sq`: `∑_{e∈ctrlEdges} 1/e² = σ_ctrl²`
  (reindex by the injective product map `(p,q) ↦ pq`).
* `sigmaE2_le_of_ctrlEdges_subset`: for `ctrlEdges BS ⊆ E`,
  `σ_E² ≤ ¼(σ_ctrl² + ∑_{extra} 1/e²)`.

Hence whenever the extra (mass/gadget) edges carry `∑ 1/e² ≤ 3 σ_ctrl²`, we get
`σ_E² ≤ σ_ctrl²`, i.e. `σ_E ≤ σ_ctrl` — exactly what `hbeat` consumes.
-/

/-- `θ(1-θ) ≤ 1/4` for every real `θ`, so the per-edge variance is at most a quarter
of the inverse-square weight. -/
lemma sigmaE2_le_quarter_sum_inv_sq (E : Finset ℕ) (θ : ℕ → ℝ) :
    sigmaE2 E θ ≤ (1 / 4 : ℝ) * ∑ e ∈ E, 1 / (e : ℝ) ^ 2 := by
  unfold sigmaE2
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e _ => ?_)
  have h1 : θ e * (1 - θ e) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ e - 1 / 2)]
  have h2 : (0 : ℝ) ≤ 1 / (e : ℝ) ^ 2 := by positivity
  rw [div_eq_mul_one_div (θ e * (1 - θ e)) ((e : ℝ) ^ 2)]
  exact mul_le_mul_of_nonneg_right h1 h2

/-- The control-edge inverse-square sum equals `σ_ctrl²` (reindex the control pairs by
their injective product map). -/
lemma sum_inv_sq_ctrlEdges_eq_sigmaCtrl_sq (BS : BlockSystem) :
    ∑ e ∈ ctrlEdges BS, 1 / (e : ℝ) ^ 2 = (sigmaCtrl BS) ^ 2 := by
  rw [sigmaCtrl, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  rw [ctrlEdges, Finset.sum_image
    (fun a ha b hb hab => ctrlPairs_prod_injOn BS ha hb hab)]
  refine Finset.sum_congr rfl (fun pq _ => ?_)
  rw [Nat.cast_mul]

/-- **σ_E² in terms of σ_ctrl² plus the extra-edge inverse-square mass.**  For any edge
set containing the control edges, `σ_E² ≤ ¼(σ_ctrl² + ∑_{extra} 1/e²)`. -/
lemma sigmaE2_le_of_ctrlEdges_subset (BS : BlockSystem) (E : Finset ℕ) (θ : ℕ → ℝ)
    (hsub : ctrlEdges BS ⊆ E) :
    sigmaE2 E θ ≤ (1 / 4 : ℝ) *
      ((sigmaCtrl BS) ^ 2 + ∑ e ∈ E \ ctrlEdges BS, 1 / (e : ℝ) ^ 2) := by
  have hsplit : ∑ e ∈ E, 1 / (e : ℝ) ^ 2
      = (∑ e ∈ ctrlEdges BS, 1 / (e : ℝ) ^ 2)
        + ∑ e ∈ E \ ctrlEdges BS, 1 / (e : ℝ) ^ 2 := by
    rw [← Finset.sum_sdiff hsub]; ring
  calc sigmaE2 E θ ≤ (1 / 4 : ℝ) * ∑ e ∈ E, 1 / (e : ℝ) ^ 2 :=
        sigmaE2_le_quarter_sum_inv_sq E θ
    _ = (1 / 4 : ℝ) * ((∑ e ∈ ctrlEdges BS, 1 / (e : ℝ) ^ 2)
          + ∑ e ∈ E \ ctrlEdges BS, 1 / (e : ℝ) ^ 2) := by rw [hsplit]
    _ = (1 / 4 : ℝ) * ((sigmaCtrl BS) ^ 2 + ∑ e ∈ E \ ctrlEdges BS, 1 / (e : ℝ) ^ 2) := by
        rw [sum_inv_sq_ctrlEdges_eq_sigmaCtrl_sq]

/-- **σ_E ≤ σ_ctrl when the extra edges are light.**  If the mass/gadget edges satisfy
`∑_{extra} 1/e² ≤ 3 σ_ctrl²`, then `σ_E ≤ σ_ctrl`.  This is the clean form fed to the
`hbeat` parameter chase (the ratio `σ_E/σ_ctrl ≤ 1`). -/
lemma sigmaE_le_sigmaCtrl_of_extra_light (BS : BlockSystem) (E : Finset ℕ) (θ : ℕ → ℝ)
    (hsub : ctrlEdges BS ⊆ E)
    (hextra : ∑ e ∈ E \ ctrlEdges BS, 1 / (e : ℝ) ^ 2 ≤ 3 * (sigmaCtrl BS) ^ 2) :
    Real.sqrt (sigmaE2 E θ) ≤ sigmaCtrl BS := by
  have hσ2 : sigmaE2 E θ ≤ (sigmaCtrl BS) ^ 2 := by
    have := sigmaE2_le_of_ctrlEdges_subset BS E θ hsub
    nlinarith [this, hextra]
  calc Real.sqrt (sigmaE2 E θ)
      ≤ Real.sqrt ((sigmaCtrl BS) ^ 2) := Real.sqrt_le_sqrt hσ2
    _ = sigmaCtrl BS := by
        rw [Real.sqrt_sq (sigmaCtrl_nonneg BS)]

end CircleMethod

end
