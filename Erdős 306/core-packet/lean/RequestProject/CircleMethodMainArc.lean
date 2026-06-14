import RequestProject.CircleMethodArcs

open Complex Finset BigOperators Real

noncomputable section

namespace CircleMethod

/-!
# Phase C — C3 main arc (Bernoulli Taylor), note 44

Foundation for the positive main term. The per-edge complex Taylor (L1) rests on
the second-order log remainder `log(1−w) = −w − w²/2 + O(w³)` (Mathlib's
`norm_log_sub_logTaylor_le` at order 2, with `logTaylor 3 (−w) = −w − w²/2`).
-/

/-- **Second-order log remainder** (L1 core): for `‖w‖ < 1`,
`‖log(1−w) − (−w − w²/2)‖ ≤ ‖w‖³ · (1−‖w‖)⁻¹ / 3`. -/
lemma log_one_sub_remainder (w : ℂ) (hw : ‖w‖ < 1) :
    ‖Complex.log (1 - w) - (-w - w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by
  have hz : ‖-w‖ < 1 := by rwa [norm_neg]
  have h := norm_log_sub_logTaylor_le 2 hz
  have ht : logTaylor 3 (-w) = -w - w ^ 2 / 2 := by
    have hrfl : logTaylor 3 (-w)
        = ∑ j ∈ Finset.range 3, (-1) ^ (j + 1) * (-w) ^ j / (j : ℂ) := rfl
    rw [hrfl, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num; ring
  rw [ht, show (1 : ℂ) + (-w) = 1 - w by ring, norm_neg] at h
  norm_num at h ⊢
  linarith [h]

end CircleMethod

end
