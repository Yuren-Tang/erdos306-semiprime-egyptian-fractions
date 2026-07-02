import RequestProject.GlobalControl.Localization

/-!
# Global level-set Laplace bound

A global level-set cardinality estimate is converted into a bound for the full
Laplace sum. This is the counting-to-partition-function interface.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- Convert the `Set.ncard` level-set hypothesis to the finite-filter form used
by `RequestProject.partition_function_bound_of_level_sets`. -/
private lemma global_levelset_filter_card_bound
    (Cglob eps : ℝ) (BS : BlockSystem)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∀ R : ℝ, 1 ≤ R →
      ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS) := by
  intro R hR
  classical
  have hcard :
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) =
        ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset_setOf]
  simpa [hcard] using hlevel R hR

/-- Step A: full Laplace bound at exponent `c'`. -/
lemma full_laplace_bound_of_global_levelsets
    (c' eps A : ℝ) (hc' : 0 < c') (heps0 : 0 ≤ 8 * eps)
    (hepsc' : 8 * eps < c') (BS : BlockSystem) (hσ : 0 < sigmaCtrl BS)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∑ a : GlobalAssignment BS, Real.exp (-c' * Qctrl BS a) ≤
      Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps) /
        (1 - Real.exp (-(c' - 8 * eps))) ^ 2 *
        (1 + 1 / sigmaCtrl BS) := by
  exact RequestProject.partition_function_bound_of_level_sets
    (fun a : GlobalAssignment BS => Qctrl BS a)
    (fun a => Qctrl_nonneg BS a)
    c' (8 * eps) (Real.exp (A * (numBlocks BS : ℝ))) (sigmaCtrl BS)
    hc' heps0 hepsc' (Real.exp_pos _).le hσ
    (global_levelset_filter_card_bound
      (Real.exp (A * (numBlocks BS : ℝ))) eps BS hlevel)

end GlobalControl

end
