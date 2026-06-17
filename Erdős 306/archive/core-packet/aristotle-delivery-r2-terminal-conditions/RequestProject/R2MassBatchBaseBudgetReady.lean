import RequestProject.R2MassBatchBaseLoadBudget
import RequestProject.R2BaseBudgetAssembly

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass batch from assembled base-budget

This thin leaf combines the eventual mass-batch theorem coming from split
base-load component budgets with the base-budget assembly built from a control
budget and a finite gadget scale/cardinality bound.
-/

/-- Eventual mass-batch supply from a control-load budget plus a gadget scale
bound. -/
theorem exists_massBatchSupply_of_gadget_scale_eventual
    {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k0min : ℕ, ∀ (D : R2ConcreteData T b), k0min ≤ D.BS.k0 →
      (∀ r ∈ D.R, Nat.Prime r) →
      (∀ r ∈ D.R, r ∉ blockSupport D.BS) →
      blockPrimes D.BS.k0 ⊆ blockSupport D.BS →
      ∀ r0 s0 : ℕ, 0 < r0 → 0 < s0 →
        (∀ r ∈ D.R, r0 ≤ r) →
        (∀ s ∈ D.S, s0 ≤ s) →
        (ε + ((D.R.card * D.S.card : ℕ) : ℝ) /
            ((r0 * s0 : ℕ) : ℝ) < 3 / (2 * (b : ℝ))) →
        ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ D.BS.k0 →
          ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q)) := by
  obtain ⟨k0mass, hmass⟩ := exists_massBatchSupply_of_baseLoadBudget_eventual (T := T) hb
  obtain ⟨k0ctrl, hctrl⟩ := exists_k0_controlLoad_lt ε hε
  refine ⟨max k0mass k0ctrl, ?_⟩
  intro D hk hRprime hRout hsub r0 s0 hr0 hs0 hRlow hSlow hsum
  have hk_mass : k0mass ≤ D.BS.k0 := le_trans (Nat.le_max_left _ _) hk
  have hk_ctrl : k0ctrl ≤ D.BS.k0 := le_trans (Nat.le_max_right _ _) hk
  have B : R2BaseLoadBudget D :=
    baseLoadBudget_of_control_epsilon_and_gadget_scale D ε r0 s0
      hr0 hs0 (hctrl D.BS hk_ctrl) hRlow hSlow hsum
  exact hmass D hk_mass hRprime hRout hsub B

end CircleMethod

end
