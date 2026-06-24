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
      nlinarith [hn, mul_le_mul_left hn (n ^ 2), mul_le_mul_left hn n]
    calc (n + 1) ^ 3 ≤ 2 * n ^ 3 := hstep
      _ < 2 * 2 ^ n := mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 2 ^ n * 2 := by ring

/-- `n⁶ < 2ⁿ` for `n ≥ 35`. -/
lemma six_lt_two_pow : ∀ n : ℕ, 35 ≤ n → n ^ 6 < 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hstep : (n + 1) ^ 6 ≤ 2 * n ^ 6 := by
      nlinarith [hn, mul_le_mul_left hn (n ^ 5), mul_le_mul_left hn (n ^ 4),
        mul_le_mul_left hn (n ^ 3), mul_le_mul_left hn (n ^ 2), mul_le_mul_left hn n]
    calc (n + 1) ^ 6 ≤ 2 * n ^ 6 := hstep
      _ < 2 * 2 ^ n := mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- `10¹²·n⁴ ≤ 2ⁿ` for `n ≥ 10⁶` (via `10¹²n⁴ ≤ n⁶ < 2ⁿ`, using `10¹² ≤ n²`). -/
lemma e12_quartic_le_two_pow (n : ℕ) (hn : 1000000 ≤ n) : 10 ^ 12 * n ^ 4 ≤ 2 ^ n := by
  have h6 : n ^ 6 < 2 ^ n := six_lt_two_pow n (by omega)
  have hnsq : (10 : ℕ) ^ 12 ≤ n ^ 2 := by
    calc (10 : ℕ) ^ 12 = (10 ^ 6) ^ 2 := by ring
      _ ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq : 10 ^ 12 * n ^ 4 ≤ n ^ 6 := by
    calc 10 ^ 12 * n ^ 4 ≤ n ^ 2 * n ^ 4 := Nat.mul_le_mul_right _ hnsq
      _ = n ^ 6 := by ring
  omega

/-- `c·n⁴ ≤ 2ⁿ` whenever `c ≤ n²` and `n ≥ 35` (via `c·n⁴ ≤ n²·n⁴ = n⁶ < 2ⁿ`). -/
lemma quartic_le_two_pow_of_le_sq (c n : ℕ) (hc : c ≤ n ^ 2) (hn : 35 ≤ n) :
    c * n ^ 4 ≤ 2 ^ n := by
  calc c * n ^ 4 ≤ n ^ 2 * n ^ 4 := Nat.mul_le_mul_right _ hc
    _ = n ^ 6 := by ring
    _ ≤ 2 ^ n := le_of_lt (six_lt_two_pow n hn)

/-- `200·n² + 1 < 2ⁿ` for `n ≥ 1000000` (via `200n²+1 < n³ < 2ⁿ`). -/
lemma two_hundred_sq_lt_two_pow (n : ℕ) (hn : 1000000 ≤ n) :
    200 * n ^ 2 + 1 < 2 ^ n := by
  have hcube : n ^ 3 < 2 ^ n := cube_lt_two_pow n (by omega)
  nlinarith [hcube, hn]

end CircleMethod
