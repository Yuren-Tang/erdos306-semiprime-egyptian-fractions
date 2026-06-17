import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Finset BigOperators

noncomputable section

namespace CircleMethod

/-!
# R2 eventual bottom-scale bounds

This leaf isolates the finite large-`k0` bookkeeping needed by the residual
mass-batch construction.  For fixed finite obstruction set `T` and denominator
`b`, the bottom pair scale `2^k0 * 2^k0` eventually dominates both every
element of `T` and the fixed quantity `2*b/3`.
-/

/-- The bottom pair scale is monotone in `k0`. -/
lemma k0_square_mono {k0 k : ℕ} (hk : k0 ≤ k) :
    2 ^ k0 * 2 ^ k0 ≤ 2 ^ k * 2 ^ k := by
  have hpow : 2 ^ k0 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  exact Nat.mul_le_mul hpow hpow

/-- Every fixed natural number is eventually below the bottom pair scale. -/
lemma exists_k0_square_gt_nat (n : ℕ) :
    ∃ k0 : ℕ, n < 2 ^ k0 * 2 ^ k0 := by
  refine ⟨n, ?_⟩
  have hpow : n < 2 ^ n := n.lt_two_pow_self
  have hpos : 0 < 2 ^ n := by positivity
  exact lt_of_lt_of_le hpow (Nat.le_mul_of_pos_right (2 ^ n) hpos)

/-- A finite obstruction set is eventually below the bottom pair scale. -/
lemma eventually_T_lt_k0_square (T : Finset ℕ) :
    ∃ k0min : ℕ, ∀ k0 : ℕ, k0min ≤ k0 →
      ∀ e ∈ T, e < 2 ^ k0 * 2 ^ k0 := by
  classical
  refine Finset.induction_on T ?base ?step
  · refine ⟨0, ?_⟩
    intro k0 _ e he
    simp at he
  · intro a T haT hT
    obtain ⟨ka, hka⟩ := exists_k0_square_gt_nat a
    obtain ⟨kT, hkT⟩ := hT
    refine ⟨max ka kT, ?_⟩
    intro k0 hk0 e he
    rw [Finset.mem_insert] at he
    rcases he with rfl | heT
    · exact lt_of_lt_of_le hka (k0_square_mono (le_trans (Nat.le_max_left ka kT) hk0))
    · exact hkT k0 (le_trans (Nat.le_max_right ka kT) hk0) e heT

/-- For fixed `b`, the inequality `2*b < 3*(2^k0 * 2^k0)` eventually holds. -/
lemma eventually_two_mul_b_lt_three_k0_square (b : ℕ) :
    ∃ k0min : ℕ, ∀ k0 : ℕ, k0min ≤ k0 →
      2 * b < 3 * (2 ^ k0 * 2 ^ k0) := by
  obtain ⟨kb, hkb⟩ := exists_k0_square_gt_nat (2 * b)
  refine ⟨kb, ?_⟩
  intro k0 hk0
  have hsq : 2 ^ kb * 2 ^ kb ≤ 2 ^ k0 * 2 ^ k0 := k0_square_mono hk0
  have hlt : 2 * b < 2 ^ k0 * 2 ^ k0 := lt_of_lt_of_le hkb hsq
  exact lt_of_lt_of_le hlt
    (Nat.le_mul_of_pos_left (2 ^ k0 * 2 ^ k0) (by norm_num : 0 < 3))

/-- Combined finite scale threshold for the residual mass-batch branch. -/
theorem exists_k0_scale_for_T_and_b (T : Finset ℕ) (b : ℕ) :
    ∃ k0min : ℕ, ∀ k0 : ℕ, k0min ≤ k0 →
      (∀ e ∈ T, e < 2 ^ k0 * 2 ^ k0) ∧
      2 * b < 3 * (2 ^ k0 * 2 ^ k0) := by
  obtain ⟨kT, hkT⟩ := eventually_T_lt_k0_square T
  obtain ⟨kb, hkb⟩ := eventually_two_mul_b_lt_three_k0_square b
  refine ⟨max kT kb, ?_⟩
  intro k0 hk0
  exact ⟨hkT k0 (le_trans (Nat.le_max_left kT kb) hk0),
    hkb k0 (le_trans (Nat.le_max_right kT kb) hk0)⟩

end CircleMethod
