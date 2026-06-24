import RequestProject.DyadicBlockDef

open Finset BigOperators

noncomputable section

namespace GlobalControl

/-- Prime-counting upper bound on a dyadic block, from Mathlib's
`primorial_le_4_pow`: the primes in `[2^k, 2^(k+1))` number at most
`2^(k+2)/k`. -/
lemma dyadic_block_card_upper (k : ℕ) (_hk : 1 ≤ k) :
    (k : ℝ) * ((dyadicBlock k).card : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
  have h_card : (dyadicBlock k).card * k ≤ 2 ^ (k + 2) := by
    have h_card : (2 ^ k) ^ (dyadicBlock k).card ≤ 4 ^ (2 ^ (k + 1)) := by
      have h_prod : (∏ p ∈ dyadicBlock k, p) ≤ 4 ^ (2 ^ (k + 1)) := by
        refine le_trans ?_ (primorial_le_4_pow (2 ^ (k + 1)))
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
        · intro x hx
          rw [dyadicBlock, Finset.mem_filter, Finset.mem_Ico] at hx
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by linarith [hx.1.2]), hx.2⟩
        · intro x hx _
          exact Nat.Prime.pos (by
            rw [Finset.mem_filter] at hx
            exact hx.2)
      refine le_trans ?_ h_prod
      calc
        (2 ^ k) ^ (dyadicBlock k).card = ∏ _p ∈ dyadicBlock k, 2 ^ k := by
          rw [Finset.prod_const]
        _ ≤ ∏ p ∈ dyadicBlock k, p :=
          Finset.prod_le_prod' fun x hx => by
          rw [dyadicBlock, Finset.mem_filter, Finset.mem_Ico] at hx
          exact hx.1.1
    convert Nat.pow_le_pow_iff_right (show 1 < 2 by norm_num) |>.1
        (show 2 ^ (k * (dyadicBlock k).card) ≤ 2 ^ (2 ^ (k + 2)) from ?_) using 1 <;>
      ring_nf at *
    exact h_card.trans (by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
      norm_num)
  norm_cast
  linarith

/-- Reciprocal mass of a full dyadic prime block is at most `4 / k`. -/
lemma dyadicBlock_recip_sum_le_four_div (k : ℕ) (hk : 1 ≤ k) :
    ∑ p ∈ dyadicBlock k, (1 : ℝ) / (p : ℝ) ≤ 4 / (k : ℝ) := by
  have hterm : ∀ p ∈ dyadicBlock k, (1 : ℝ) / (p : ℝ) ≤ 1 / ((2 : ℝ) ^ k) := by
    intro p hp
    rw [dyadicBlock, Finset.mem_filter, Finset.mem_Ico] at hp
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hp.1.1)
  have hsum :
      ∑ p ∈ dyadicBlock k, (1 : ℝ) / (p : ℝ)
        ≤ ((dyadicBlock k).card : ℝ) * (1 / ((2 : ℝ) ^ k)) := by
    calc
      ∑ p ∈ dyadicBlock k, (1 : ℝ) / (p : ℝ)
          ≤ ∑ _p ∈ dyadicBlock k, (1 : ℝ) / ((2 : ℝ) ^ k) :=
            Finset.sum_le_sum hterm
      _ = ((dyadicBlock k).card : ℝ) * (1 / ((2 : ℝ) ^ k)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := dyadic_block_card_upper k hk
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hpow : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
  have hcard' : ((dyadicBlock k).card : ℝ) ≤ (2 : ℝ) ^ (k + 2) / (k : ℝ) := by
    rw [le_div_iff₀ hkR]
    nlinarith [hcard]
  calc
    ∑ p ∈ dyadicBlock k, (1 : ℝ) / (p : ℝ)
        ≤ ((dyadicBlock k).card : ℝ) * (1 / ((2 : ℝ) ^ k)) := hsum
    _ ≤ ((2 : ℝ) ^ (k + 2) / (k : ℝ)) * (1 / ((2 : ℝ) ^ k)) := by
        exact mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = 4 / (k : ℝ) := by
        field_simp [hpow.ne', hkR.ne']
        ring

end GlobalControl

end
