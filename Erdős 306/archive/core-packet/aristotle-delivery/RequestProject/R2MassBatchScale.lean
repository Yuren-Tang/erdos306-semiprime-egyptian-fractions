import RequestProject.R2ComponentScaleCard

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass-batch scale bounds

The residual mass batch `Q` is selected from block-support prime products.  Once
the bottom block-support product scale dominates `N / ρ`, every selected `Q`
edge automatically satisfies the same edge-scale hypothesis used by the final
R2 assembly.
-/

lemma massBatchEdge_ge_k0_square
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b}
    (QB : R2MassBatchSupply D) {e : ℕ} (he : e ∈ D.Q) :
    2 ^ D.BS.k0 * 2 ^ D.BS.k0 ≤ e := by
  obtain ⟨p, q, hp, hq, _hpq, rfl⟩ := QB.hQpair e he
  exact Nat.mul_le_mul (blockSupport_ge_pow_k0 D.BS hp)
    (blockSupport_ge_pow_k0 D.BS hq)

theorem massBatchEdges_scale_of_k0_square
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b}
    (QB : R2MassBatchSupply D) (N : ℤ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hscale : (N : ℝ) ≤ ρ * ((2 ^ D.BS.k0 * 2 ^ D.BS.k0 : ℕ) : ℝ)) :
    ∀ e ∈ D.Q, (N : ℝ) ≤ ρ * (e : ℝ) := by
  intro e he
  refine le_trans hscale ?_
  have : ((2 ^ D.BS.k0 * 2 ^ D.BS.k0 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast massBatchEdge_ge_k0_square QB he
  exact mul_le_mul_of_nonneg_left this hρ

end CircleMethod

end
