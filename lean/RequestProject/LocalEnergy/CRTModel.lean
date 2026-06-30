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

end LocalEnergy
