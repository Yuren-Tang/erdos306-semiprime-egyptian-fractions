import RequestProject.R2MassBatchCandidatePool
import RequestProject.BlockSystemConstruction

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 full pair-pool lower bounds

This leaf connects the `BlockMassPool` product-load estimate for
`blockPrimes k0` to the canonical `blockSupportPairPool` used by the residual
mass-batch selector.
-/

/-- Reciprocal load is monotone under finite-set inclusion. -/
lemma recipLoad_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    R2ConcreteData.recipLoad A ≤ R2ConcreteData.recipLoad B := by
  unfold R2ConcreteData.recipLoad
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB
    (by intro x _hxB _hxA; positivity)

/-- The product image of `blockPrimes k0` ordered pairs has the expected
reciprocal load. -/
lemma blockPrimes_pairImage_recipLoad_eq (k0 : ℕ) :
    R2ConcreteData.recipLoad
        (((blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2)).image
          (fun pq : ℕ × ℕ => pq.1 * pq.2))
      =
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  unfold R2ConcreteData.recipLoad
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl fun pq _hpq => by
      simp [Nat.cast_mul]
  · exact blockPrimes_pair_prod_injOn k0

/-- If `blockPrimes k0` is contained in the support of a block system, then the
product image of its ordered pairs is contained in `blockSupportPairPool`. -/
lemma blockPrimes_pairImage_subset_blockSupportPairPool
    (BS : BlockSystem) (k0 : ℕ)
    (hsub : blockPrimes k0 ⊆ blockSupport BS) :
    ((blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2)).image
        (fun pq : ℕ × ℕ => pq.1 * pq.2)
      ⊆ blockSupportPairPool BS := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  rw [blockSupportPairPool, Finset.mem_image]
  refine ⟨pq, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
  exact ⟨⟨hsub hpq.1.1, hsub hpq.1.2.1, fun h => hpq.1.2.2 h⟩, hpq.2⟩

/-- Bridge a `blockPrimes` product-load lower bound into the full
`blockSupportPairPool` lower bound. -/
theorem blockSupportPairPool_load_ge_of_blockPrimes_subset
    (BS : BlockSystem) (k0 : ℕ)
    (hsub : blockPrimes k0 ⊆ blockSupport BS)
    (hload :
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) :
    (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool BS) := by
  let P :=
    ((blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2)).image
      (fun pq : ℕ × ℕ => pq.1 * pq.2)
  have hPsub : P ⊆ blockSupportPairPool BS :=
    blockPrimes_pairImage_subset_blockSupportPairPool BS k0 hsub
  have hmono : R2ConcreteData.recipLoad P ≤
      R2ConcreteData.recipLoad (blockSupportPairPool BS) :=
    recipLoad_mono hPsub
  have hPeq :
      R2ConcreteData.recipLoad P =
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
    exact blockPrimes_pairImage_recipLoad_eq k0
  linarith

/-- Convenient large-scale corollary from the existing `blockPrimes` load
theorem. -/
theorem blockSupportPairPool_load_ge_half_of_contains_large_blockPrimes
    (BS : BlockSystem) (k1 : ℕ)
    (hlarge : k1 ≤ BS.k0)
    (hsub : blockPrimes BS.k0 ⊆ blockSupport BS)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) :
    (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool BS) := by
  exact blockSupportPairPool_load_ge_of_blockPrimes_subset BS BS.k0 hsub
    (hload BS.k0 hlarge)

/-- Existential form using `blockPrimes_product_load_ge`. -/
theorem exists_k1_blockSupportPairPool_load_ge_half
    (BS : BlockSystem)
    (hsub : blockPrimes BS.k0 ⊆ blockSupport BS) :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ BS.k0 →
      (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool BS)) := by
  obtain ⟨k1, hk15, hload⟩ := blockPrimes_product_load_ge
  exact ⟨k1, hk15, fun hlarge =>
    blockSupportPairPool_load_ge_half_of_contains_large_blockPrimes BS k1
      hlarge hsub hload⟩

end CircleMethod

end
