import RequestProject.R2ForbiddenPoolBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass-batch final budget bridge

This leaf combines the full pair-pool lower bound with the three-piece
forbidden-pool upper budget.  It is the final bookkeeping socket before the
remaining problem becomes purely numeric/asymptotic: make the full pool large
and the obstruction/control/gadget overlaps small enough.
-/

/-- If the full pair pool has load at least `1/2`, and the base residual target
plus the three forbidden budgets is at most `1/2`, then the residual mass batch
exists. -/
theorem exists_massBatchSupply_of_half_fullPool_forbiddenBudget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 0 < b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0))
    (B : R2ForbiddenBudget D)
    (hfull :
      (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS))
    (hbudget :
      (3 / (2 * (b : ℝ)) - D.baseLoad) + (B.FT + B.Fctrl + B.Fgadget)
        ≤ (1 : ℝ) / 2) :
    ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q) := by
  refine exists_massBatchSupply_of_pairPool_separate_bounds D hb hbase hlarge
    ((1 : ℝ) / 2) (B.FT + B.Fctrl + B.Fgadget) hfull ?_ hbudget
  exact residualForbidden_recipLoad_le_budget B

/-- Version using the `blockPrimes` product-load estimate through the already
proved full-pool bridge. -/
theorem exists_massBatchSupply_of_blockPrimes_forbiddenBudget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 0 < b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0))
    (B : R2ForbiddenBudget D)
    (k1 : ℕ)
    (hklarge : k1 ≤ D.BS.k0)
    (hsub : blockPrimes D.BS.k0 ⊆ blockSupport D.BS)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))
    (hbudget :
      (3 / (2 * (b : ℝ)) - D.baseLoad) + (B.FT + B.Fctrl + B.Fgadget)
        ≤ (1 : ℝ) / 2) :
    ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q) := by
  have hfull :
      (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS) :=
    blockSupportPairPool_load_ge_half_of_contains_large_blockPrimes D.BS k1
      hklarge hsub hload
  exact exists_massBatchSupply_of_half_fullPool_forbiddenBudget D hb hbase hlarge
    B hfull hbudget

/-- Existential version using `blockPrimes_product_load_ge`: after choosing a
sufficiently low starting block, the only remaining hypotheses are support
containment, the bottom-scale inequality, and the three-piece forbidden budget. -/
theorem exists_massBatchSupply_of_eventual_blockPrimes_forbiddenBudget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 0 < b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0))
    (B : R2ForbiddenBudget D)
    (hsub : blockPrimes D.BS.k0 ⊆ blockSupport D.BS)
    (hbudget :
      (3 / (2 * (b : ℝ)) - D.baseLoad) + (B.FT + B.Fctrl + B.Fgadget)
        ≤ (1 : ℝ) / 2) :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ D.BS.k0 →
      ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q)) := by
  obtain ⟨k1, hk15, hload⟩ := blockPrimes_product_load_ge
  refine ⟨k1, hk15, ?_⟩
  intro hklarge
  exact exists_massBatchSupply_of_blockPrimes_forbiddenBudget D hb hbase hlarge
    B k1 hklarge hsub hload hbudget

end CircleMethod

end
