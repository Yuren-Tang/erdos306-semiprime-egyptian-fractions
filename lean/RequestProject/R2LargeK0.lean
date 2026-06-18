import Mathlib

/-!
# Exponential-vs-polynomial scale lemmas for the R2 large-`k₀` regime

Pure-`ℕ` leaf lemmas (no project dependencies, fast to recompile) used to close
the `2N < 2^{2k₀}` / numeric-window estimates in the R2 final assembly.
-/

namespace CircleMethod

/-- `n³ < 2ⁿ` for `n ≥ 10`.  Proved by induction from the base `10³ = 1000 < 1024`,
with step `(n+1)³ ≤ 2·n³` (valid for `n ≥ 10`). -/
lemma cube_lt_two_pow : ∀ n : ℕ, 10 ≤ n → n ^ 3 < 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have hstep : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
      nlinarith [hn, mul_le_mul_right' hn (n ^ 2), mul_le_mul_right' hn n]
    calc (n + 1) ^ 3 ≤ 2 * n ^ 3 := hstep
      _ < 2 * 2 ^ n := mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 2 ^ n * 2 := by ring

/-- `200·n² + 1 < 2ⁿ` for `n ≥ 1000000` (via `200n²+1 < n³ < 2ⁿ`). -/
lemma two_hundred_sq_lt_two_pow (n : ℕ) (hn : 1000000 ≤ n) :
    200 * n ^ 2 + 1 < 2 ^ n := by
  have hcube : n ^ 3 < 2 ^ n := cube_lt_two_pow n (by omega)
  nlinarith [hcube, hn]

end CircleMethod
