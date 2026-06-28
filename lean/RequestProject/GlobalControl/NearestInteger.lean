import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section

namespace GlobalControl

/-- Distance from a real number to its nearest integer. -/
def nndist1 (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma nndist1_nonneg (x : ℝ) : 0 ≤ nndist1 x := abs_nonneg _

lemma nndist1_le_half (x : ℝ) : nndist1 x ≤ 1 / 2 := by
  simpa [nndist1] using abs_sub_round x

end GlobalControl
