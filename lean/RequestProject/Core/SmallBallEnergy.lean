import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Converting a small-ball counting bound into a quadratic-energy bound. -/

open Finset BigOperators

namespace RequestProject

/-- If at most `B` members of a finite family have size at most `delta`, then
the quadratic energy is at least `(card - B) * delta^2`. -/
theorem sum_sq_lower_bound_of_small_ball
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ) (delta B : ℝ)
    (hdelta : 0 ≤ delta)
    (hsmall : ((S.filter fun i => f i ≤ delta).card : ℝ) ≤ B) :
    ((S.card : ℝ) - B) * delta ^ 2 ≤ ∑ i ∈ S, (f i) ^ 2 := by
  let far := S.filter fun i => delta < f i
  have hpartition :
      far.card + (S.filter fun i => f i ≤ delta).card = S.card := by
    simpa [far, add_comm] using S.card_filter_add_card_filter_not (fun i => f i ≤ delta)
  have hfar : (S.card : ℝ) - B ≤ far.card := by
    have hpartition_real :
        (far.card : ℝ) + (S.filter fun i => f i ≤ delta).card = S.card := by
      exact_mod_cast hpartition
    linarith
  calc
    ((S.card : ℝ) - B) * delta ^ 2
        ≤ (far.card : ℝ) * delta ^ 2 :=
          mul_le_mul_of_nonneg_right hfar (sq_nonneg delta)
    _ = ∑ _i ∈ far, delta ^ 2 := by simp
    _ ≤ ∑ i ∈ far, (f i) ^ 2 := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact pow_le_pow_left₀ hdelta (Finset.mem_filter.mp hi).2.le 2
    _ ≤ ∑ i ∈ S, (f i) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => sq_nonneg _

end RequestProject
