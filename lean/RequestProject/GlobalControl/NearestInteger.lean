import Mathlib.Analysis.Normed.Group.AddCircle

noncomputable section

namespace GlobalControl

/-- Distance from a real number to its nearest integer. -/
def nndist1 (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- `nndist1` is the canonical norm on the additive circle `ℝ / ℤ`. -/
lemma nndist1_eq_unitAddCircle_norm (x : ℝ) :
    nndist1 x = ‖(x : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  rfl

lemma nndist1_nonneg (x : ℝ) : 0 ≤ nndist1 x := abs_nonneg _

lemma nndist1_le_half (x : ℝ) : nndist1 x ≤ 1 / 2 := by
  simpa [nndist1] using abs_sub_round x

end GlobalControl
