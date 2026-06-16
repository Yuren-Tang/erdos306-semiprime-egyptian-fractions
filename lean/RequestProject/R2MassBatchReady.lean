import RequestProject.R2ComponentDisjoint
import RequestProject.R2EventualScale

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass-batch ready wrapper

This leaf combines the completed finite scale and component-disjointness leaves
with the existing forbidden-base-budget theorem.  The only non-finite input left
for this branch is the base-load upper bound.
-/

/-- Eventual mass-batch supply once the base load is small, the denominator-side
gadget primes lie outside the block support, and the block-prime pool is present
in the support. -/
theorem exists_massBatchSupply_of_basePieces_eventual
    {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b) :
    ∃ k0min : ℕ, ∀ (D : R2ConcreteData T b), k0min ≤ D.BS.k0 →
      D.baseLoad < 3 / (2 * (b : ℝ)) →
      (∀ r ∈ D.R, Nat.Prime r) →
      (∀ r ∈ D.R, r ∉ blockSupport D.BS) →
      blockPrimes D.BS.k0 ⊆ blockSupport D.BS →
      ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ D.BS.k0 →
        ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q)) := by
  obtain ⟨k0min, hscale⟩ := exists_k0_scale_for_T_and_b T b
  refine ⟨k0min, ?_⟩
  intro D hk0 hbase hRprime hRout hsub
  have hTsmall : ∀ e ∈ T, e < 2 ^ D.BS.k0 * 2 ^ D.BS.k0 :=
    (hscale D.BS.k0 hk0).1
  have hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0) :=
    (hscale D.BS.k0 hk0).2
  have hdisj : Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S) :=
    r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport D hRprime hRout
  exact exists_massBatchSupply_of_basePieces_forbiddenBudget D hb hbase
    hlarge hTsmall hdisj hsub

end CircleMethod

