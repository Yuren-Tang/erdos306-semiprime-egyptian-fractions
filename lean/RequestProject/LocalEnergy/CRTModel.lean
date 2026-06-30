import RequestProject.BlockCRTEnergy

/-! Finite CRT assignments, centered representatives, quadratic block energy,
and the associated deviation scale. -/

namespace LocalEnergy

/-- A block-energy sublevel set is no larger than the full assignment space;
if every modulus in the block is at most `2X`, its cardinality is at most
`(2X) ^ P.card`. -/
lemma levelset_card_le_pow (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, p ≤ 2 * X) (R : ℝ) :
    ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
      ≤ (2 * (X : ℝ)) ^ P.card := by
  refine' le_trans _ _
  exact (∏ p ∈ P, p : ℝ)
  · refine' le_trans (Nat.cast_le.mpr <| Finset.card_filter_le _ _) _
    simp +decide [Fintype.card_pi]
    conv_rhs => rw [← Finset.prod_attach]
  · exact le_trans
      (Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        fun p hp => Nat.cast_le.mpr (hP p hp))
      (by norm_num)

/-- For a prime block contained in `[X, 2X]`, the block deviation satisfies
`sigmaP P ≤ P.card / X ^ 2`. -/
lemma block_deviation_upper_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) :
    sigmaP P ≤ (P.card : ℝ) / (X : ℝ) ^ 2 := by
  refine Real.sqrt_le_iff.mpr ?_
  refine' ⟨by positivity, le_trans (Finset.sum_le_sum fun pq hpq =>
    one_div_le_one_div_of_le ?_ <| pow_le_pow_left₀ (by positivity)
      (mul_le_mul (Nat.cast_le.mpr <| (hP _ pq.1.2).2.1)
        (Nat.cast_le.mpr <| (hP _ pq.2.2).2.1)
        (by positivity) (by positivity)) 2) _⟩ <;> norm_num
  · positivity
  · field_simp
    exact_mod_cast le_trans (Finset.card_filter_le _ _)
      (by norm_num [sq, Finset.card_product])

end LocalEnergy
