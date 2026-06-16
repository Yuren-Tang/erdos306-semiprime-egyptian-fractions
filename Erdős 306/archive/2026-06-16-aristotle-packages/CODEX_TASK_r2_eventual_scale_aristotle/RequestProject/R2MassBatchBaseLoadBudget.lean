import RequestProject.R2MassBatchReady
import RequestProject.R2BaseLoadUpper

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass batch from base-load component budgets
-/

/-- Eventual mass-batch supply from split base-load component budgets. -/
theorem exists_massBatchSupply_of_baseLoadBudget_eventual
    {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b) :
    ∃ k0min : ℕ, ∀ (D : R2ConcreteData T b), k0min ≤ D.BS.k0 →
      (∀ r ∈ D.R, Nat.Prime r) →
      (∀ r ∈ D.R, r ∉ blockSupport D.BS) →
      blockPrimes D.BS.k0 ⊆ blockSupport D.BS →
      R2BaseLoadBudget D →
      ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ D.BS.k0 →
        ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q)) := by
  obtain ⟨k0min, hready⟩ := exists_massBatchSupply_of_basePieces_eventual (T := T) hb
  refine ⟨k0min, ?_⟩
  intro D hk0 hRprime hRout hsub B
  exact hready D hk0 (baseLoad_lt_of_budget D hRprime hRout B) hRprime hRout hsub

end CircleMethod

