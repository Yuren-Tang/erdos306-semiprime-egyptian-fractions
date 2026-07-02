/-
# Cross-block energy

Deterministic reciprocal-phase dispersion and the energy penalty forced by a
label mismatch between consecutive prime blocks.
-/
import RequestProject.GlobalControl.Basic
import RequestProject.Core.PrimeDivisorCount
import RequestProject.LocalEnergy.AdjacentScaleEnergy

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! The local reciprocal-dispersion and fixed-outer-prime energy bounds live in
`LocalEnergy.AdjacentScaleEnergy`. This module specializes them to consecutive
blocks of a `BlockSystem`. -/

/-- Under the label-size bounds, at most one prime from the next dyadic block
can divide the nonzero difference of two consecutive labels. -/
lemma adjacent_block_prime_divisor_count_le_one (BS : BlockSystem) (k N : ℕ)
    (m m' : ℤ) (hmm : m ≠ m') (hN : N ≤ 2 ^ k)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * N)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card)
    (S : Finset ℕ) (hS : S ⊆ BS.P (k + 1)) :
    (S.filter fun q : ℕ => (q : ℤ) ∣ (m' - m)).card ≤ 1 := by
  apply RequestProject.card_filter_prime_dvd_le_one S (2 ^ (k + 1)) (m' - m)
  · exact sub_ne_zero.mpr hmm.symm
  · exact fun q hq => BS.hprime (k + 1) q (hS hq)
  · exact fun q hq => (BS.hwindow (k + 1) q (hS hq)).1
  · have hN' : (N : ℤ) ≤ 2 ^ k := by exact_mod_cast hN
    have hcard' : ((BS.P (k + 1)).card : ℤ) ≤ 2 ^ (k + 1) := by
      exact_mod_cast block_card_le BS (k + 1)
    have hkpos : (0 : ℤ) < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ] at hm' hcard' ⊢
    have hm_upper : 32 * |m| ≤ (2 * 2 ^ k) ^ 2 := by
      calc
        32 * |m| ≤ 2 ^ k * N := hm
        _ ≤ 2 ^ k * 2 ^ k := mul_le_mul_of_nonneg_left hN' hkpos.le
        _ ≤ (2 * 2 ^ k) ^ 2 := by nlinarith
    have hm'_upper : 32 * |m'| ≤ (2 * 2 ^ k) ^ 2 := by
      have hcard'' : ((BS.P (k + 1)).card : ℤ) ≤ 2 * 2 ^ k := by
        simpa only [mul_comm] using hcard'
      calc
        32 * |m'| ≤ 2 ^ k * 2 * (BS.P (k + 1)).card := hm'
        _ = (2 * 2 ^ k) * (BS.P (k + 1)).card := by ring
        _ ≤ (2 * 2 ^ k) * (2 * 2 ^ k) :=
          mul_le_mul_of_nonneg_left hcard''
            (show (0 : ℤ) ≤ 2 * 2 ^ k from mul_nonneg (by norm_num) hkpos.le)
        _ = (2 * 2 ^ k) ^ 2 := by ring
    have hdiff_upper : 32 * |m' - m| ≤ 2 * (2 * 2 ^ k) ^ 2 := by
      calc
        32 * |m' - m| ≤ 32 * (|m'| + |m|) :=
          mul_le_mul_of_nonneg_left (abs_sub m' m) (by norm_num)
        _ = 32 * |m'| + 32 * |m| := by ring
        _ ≤ (2 * 2 ^ k) ^ 2 + (2 * 2 ^ k) ^ 2 :=
          add_le_add hm'_upper hm_upper
        _ = 2 * (2 * 2 ^ k) ^ 2 := by ring
    have hscale_sq_pos : 0 < (2 * 2 ^ k : ℤ) ^ 2 :=
      sq_pos_of_pos (mul_pos (by norm_num) hkpos)
    have hsmall' : |m' - m| < (2 * 2 ^ k : ℤ) ^ 2 := by
      nlinarith [hscale_sq_pos]
    norm_num [Nat.cast_pow, pow_succ]
    convert hsmall' using 1
    ring

/-
**Consecutive-block mismatch penalty with exceptions.** The cold blocks of the
    global level-set argument carry a *bounded* exception set `Eₖ` of vertices
    where the dominant label fails. Reusing
    `LocalEnergy.crt_energy_lower_bound_for_fixed_outer_prime` over the reduced
    sets `Pₖ \ Eₖ` and `Pₖ₊₁ \ Eₖ₊₁` gives the same bipartite penalty with the
    reduced cardinalities. The proof uses `Pₖ \ Eₖ` as the dispersion vertex
    set and draws the good outer vertices from
    `Pₖ₊₁ \ Eₖ₊₁`; at most one of those divides `m'-m`, so at least
    `(Pₖ₊₁ \ Eₖ₊₁).card - 1` are good.

-/
set_option maxHeartbeats 1000000 in
theorem consecutive_block_mismatch_energy_lower_bound (BS : BlockSystem)
    (a : (p : ℕ) → ZMod p) (k : ℕ)
    (m m' : ℤ) (hmm : m ≠ m')
    (Ek Ek1 : Finset ℕ)
    (hlabel_k : ∀ p ∈ BS.P k \ Ek, (a p : ZMod p) = (m : ZMod p))
    (hlabel_k1 : ∀ q ∈ BS.P (k + 1) \ Ek1, (a q : ZMod q) = (m' : ZMod q))
    (hNk : 12 ≤ (BS.P k \ Ek).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k \ Ek).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    (((BS.P (k + 1) \ Ek1).card : ℝ) - 1) * ((BS.P k \ Ek).card : ℝ) ^ 3 /
        (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  let P := BS.P k \ Ek
  let Q := BS.P (k + 1) \ Ek1
  let goodQ := Q.filter fun q : ℕ => ¬ (q : ℤ) ∣ (m' - m)
  let c : ℝ := (P.card : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2)
  have hbad : (Q.filter fun q : ℕ => (q : ℤ) ∣ (m' - m)).card ≤ 1 := by
    apply adjacent_block_prime_divisor_count_le_one BS k P.card m m' hmm
    · exact le_trans (Finset.card_le_card Finset.sdiff_subset) (block_card_le BS k)
    · exact hm
    · exact hm'
    · exact Finset.sdiff_subset
  have hgood_card : (Q.card : ℝ) - 1 ≤ (goodQ.card : ℝ) := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := Q) (fun q : ℕ => (q : ℤ) ∣ (m' - m))
    change (Q.card : ℝ) - 1 ≤
      ((Q.filter fun q : ℕ => ¬ (q : ℤ) ∣ (m' - m)).card : ℝ)
    have hpartition_real :
        ((Q.filter fun q : ℕ => (q : ℤ) ∣ (m' - m)).card : ℝ) +
          ((Q.filter fun q : ℕ => ¬ (q : ℤ) ∣ (m' - m)).card : ℝ) = Q.card := by
      exact_mod_cast hpartition
    have hbad_real :
        ((Q.filter fun q : ℕ => (q : ℤ) ∣ (m' - m)).card : ℝ) ≤ 1 := by
      exact_mod_cast hbad
    linarith
  have hq_energy : ∀ q ∈ goodQ, c ≤
      ∑ p ∈ P, ((Hglob a p q : ℝ) / ((p : ℝ) * q)) ^ 2 := by
    intro q hq
    have hq_data : q ∈ Q ∧ ¬ (q : ℤ) ∣ (m' - m) := by
      simpa only [goodQ, Finset.mem_filter] using hq
    have hqQ : q ∈ Q := hq_data.1
    have hlocal := LocalEnergy.crt_energy_lower_bound_for_fixed_outer_prime
      (2 ^ k) (by positivity) P
      (fun p hp => ⟨BS.hprime k p (Finset.sdiff_subset hp),
        (BS.hwindow k p (Finset.sdiff_subset hp)).1,
        by simpa [pow_succ'] using (BS.hwindow k p (Finset.sdiff_subset hp)).2⟩)
      hNk q (BS.hprime (k + 1) q (Finset.sdiff_subset hqQ))
      (by simpa [pow_succ'] using (BS.hwindow (k + 1) q (Finset.sdiff_subset hqQ)).1)
      (by
        have := (BS.hwindow (k + 1) q (Finset.sdiff_subset hqQ)).2
        norm_num [pow_succ'] at this ⊢
        linarith)
      m m' hq_data.2 hm
    refine (show c ≤ ∑ p ∈ P,
        ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 from ?_).trans_eq ?_
    · norm_num [c, Nat.cast_pow] at hlocal ⊢
      exact hlocal
    · apply Finset.sum_congr rfl
      intro p hp
      simp only [Hglob, hlabel_k p hp, hlabel_k1 q hqQ]
  have hproduct_subset : P ×ˢ goodQ ⊆ bipartitePairs BS k := by
    intro pq hpq
    have hqQ : pq.2 ∈ Q := by
      have hq_data : pq.2 ∈ Q ∧ ¬ (pq.2 : ℤ) ∣ (m' - m) := by
        simpa only [goodQ, Finset.mem_filter] using (Finset.mem_product.mp hpq).2
      exact hq_data.1
    exact Finset.mem_product.mpr
      ⟨Finset.sdiff_subset (Finset.mem_product.mp hpq).1,
        Finset.sdiff_subset hqQ⟩
  have hproduct_energy : (goodQ.card : ℝ) * c ≤
      ∑ pq ∈ P ×ˢ goodQ,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
    rw [Finset.sum_product_right]
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum hq_energy
  calc
    ((Q.card : ℝ) - 1) * (P.card : ℝ) ^ 3 /
        (2 ^ 13 * (2 ^ k : ℝ) ^ 2) = ((Q.card : ℝ) - 1) * c := by
          simp only [c]
          ring
    _ ≤ (goodQ.card : ℝ) * c :=
      mul_le_mul_of_nonneg_right hgood_card (by positivity)
    _ ≤ ∑ pq ∈ P ×ˢ goodQ,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := hproduct_energy
    _ ≤ ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hproduct_subset
        (fun _ _ _ => sq_nonneg _)

end GlobalControl

end
