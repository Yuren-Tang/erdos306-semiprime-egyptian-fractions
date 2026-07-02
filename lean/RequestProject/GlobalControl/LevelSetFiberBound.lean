import RequestProject.GlobalControl.Encoding.Fibers
import RequestProject.GlobalControl.LevelSetParameters
import RequestProject.GlobalPeierlsBookkeeping

/-!
# Level-set fiber bounds

Product bounds for individual fibers and the shell partition-function
estimate.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### RHS ε-budget assembly (note 40 §5) -/

/-- Per-fiber product bound: given the per-block count bound (from
    `hot_block_count`/`fixed_label_block_count`), a fiber's cardinality is at most the product of
    `exp(2ε(v k+1))` over the blocks. -/
lemma fiber_prod_bound (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ)
    (eps : ℝ)
    (hcnt : ∀ k ∈ Finset.Icc BS.k0 BS.K,
        ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
            QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
            (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter
                (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card : ℝ)
          ≤ Real.exp (2 * eps * ((v k : ℝ) + 1))) :
    ((fiber BS H B v ℓ).card : ℝ) ≤
      ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
  have h1 := fiber_card_le BS H B v ℓ
  calc ((fiber BS H B v ℓ).card : ℝ)
      ≤ ((∏ k ∈ Finset.Icc BS.k0 BS.K,
          (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
            QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
            (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter
                (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∏ k ∈ Finset.Icc BS.k0 BS.K,
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
            QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
            (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter
                (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card : ℝ) := by
        push_cast; rfl
    _ ≤ ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) :=
        Finset.prod_le_prod (fun k _ => by positivity) hcnt

/-- Shell-sum bound for `admShells`: the sum over admissible shells of the
    per-block `exp(2ε(v k+1))` product is controlled by the verified
    `shell_sum_bound` (after reindexing the `Finset.pi` form to the subtype
    `Fintype.piFinset` form). -/
lemma shell_sum_le (BS : BlockSystem) (c2 R eps : ℝ)
    (H : Finset ℕ) (heps : 0 < eps) (hR0 : 0 ≤ R) :
    (∑ v ∈ admShells BS c2 R H,
        ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)))
      ≤ Real.exp ((2 * eps + eps) * R) *
          Real.exp ((numBlocks BS : ℝ) *
            (2 * eps + Real.log (1 / (1 - Real.exp (-eps))))) := by
  classical
  set c : {x // x ∈ Finset.Icc BS.k0 BS.K} → ℕ → ℝ :=
    fun _ n => Real.exp (2 * eps * ((n : ℝ) + 1)) with hc
  have hcard : Fintype.card {x // x ∈ Finset.Icc BS.k0 BS.K} = numBlocks BS := by
    simp only [Fintype.card_coe, Nat.card_Icc, numBlocks]
  have hshell := GlobalPeierls.shell_sum_bound c (2 * eps) eps R (by linarith) heps hR0
    (fun _ _ => Real.exp_nonneg _) (fun _ _ => le_of_eq (by simp only [hc]))
  rw [hcard] at hshell
  refine le_trans ?_ hshell
  set φ : (ℕ → ℕ) → ({x // x ∈ Finset.Icc BS.k0 BS.K} → ℕ) := fun v k => v k.1 with hφ
  have hsc : ∀ v ∈ admShells BS c2 R H,
      (∀ k : {x // x ∈ Finset.Icc BS.k0 BS.K}, v k.1 < ⌊R⌋₊ + 1) ∧
      (∀ k, k ∉ Finset.Icc BS.k0 BS.K → v k = 0) := by
    intro v hv
    rw [admShells, Finset.mem_filter] at hv
    obtain ⟨hvsc, -⟩ := hv
    rw [shellCarrier, Finset.mem_image] at hvsc
    obtain ⟨p, hp, rfl⟩ := hvsc
    rw [Finset.mem_pi] at hp
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · dsimp only; rw [dif_pos k.2]; exact Finset.mem_range.mp (hp k.1 k.2)
    · dsimp only; rw [dif_neg hk]
  have hAB : (∑ v ∈ admShells BS c2 R H,
        ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)))
      = ∑ w ∈ (admShells BS c2 R H).image φ, ∏ k, c k (w k) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      exact (Finset.prod_coe_sort (Finset.Icc BS.k0 BS.K)
        (fun k => Real.exp (2 * eps * ((v k : ℝ) + 1)))).symm
    · intro v hv v' hv' heq
      funext k
      by_cases hk : k ∈ Finset.Icc BS.k0 BS.K
      · have := congrFun heq ⟨k, hk⟩
        simpa [hφ] using this
      · rw [(hsc v hv).2 k hk, (hsc v' hv').2 k hk]
  rw [hAB]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun k => ?_, ?_⟩
  · rw [Finset.mem_range]; exact (hsc v hv).1 k
  · rw [admShells, Finset.mem_filter] at hv
    have hsum := hv.2.1
    rw [Finset.sum_coe_sort (Finset.Icc BS.k0 BS.K) (fun k => (v k : ℝ))]
    exact hsum

/-- Inner `(v, ℓ)` double sum: given the per-fiber product bound, the sum over
    admissible shells and labels is `≤ |admLabels|·shellBound`. -/
lemma hrhs_inner (BS : BlockSystem) (c2 R eps : ℝ) (H B : Finset ℕ)
    (heps : 0 < eps) (hR0 : 0 ≤ R)
    (hbound : ∀ v ∈ admShells BS c2 R H, ∀ ℓ ∈ admLabels BS c2 R H B,
        ((fiber BS H B v ℓ).card : ℝ) ≤
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1))) :
    (∑ v ∈ admShells BS c2 R H, ∑ ℓ ∈ admLabels BS c2 R H B,
        ((fiber BS H B v ℓ).card : ℝ))
      ≤ ((admLabels BS c2 R H B).card : ℝ) *
          (Real.exp ((2 * eps + eps) * R) *
            Real.exp ((numBlocks BS : ℝ) *
              (2 * eps + Real.log (1 / (1 - Real.exp (-eps)))))) := by
  calc ∑ v ∈ admShells BS c2 R H, ∑ ℓ ∈ admLabels BS c2 R H B,
        ((fiber BS H B v ℓ).card : ℝ)
      ≤ ∑ v ∈ admShells BS c2 R H, ∑ ℓ ∈ admLabels BS c2 R H B,
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
        refine Finset.sum_le_sum (fun v hv => Finset.sum_le_sum (fun ℓ hℓ => hbound v hv ℓ hℓ))
    _ = ∑ v ∈ admShells BS c2 R H, ((admLabels BS c2 R H B).card : ℝ) *
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((admLabels BS c2 R H B).card : ℝ) *
          ∑ v ∈ admShells BS c2 R H,
            ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ ((admLabels BS c2 R H B).card : ℝ) *
          (Real.exp ((2 * eps + eps) * R) *
            Real.exp ((numBlocks BS : ℝ) *
              (2 * eps + Real.log (1 / (1 - Real.exp (-eps)))))) :=
        mul_le_mul_of_nonneg_left (shell_sum_le BS c2 R eps H heps hR0) (by positivity)

end GlobalControl

end
