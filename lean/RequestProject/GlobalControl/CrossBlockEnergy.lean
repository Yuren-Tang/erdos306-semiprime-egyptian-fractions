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
    (S.filter fun q => (q : ℤ) ∣ (m' - m)).card ≤ 1 := by
  apply RequestProject.card_filter_prime_dvd_le_one S (2 ^ (k + 1)) (m' - m)
  · exact sub_ne_zero.mpr hmm.symm
  · exact fun q hq => BS.hprime (k + 1) q (hS hq)
  · exact fun q hq => (BS.hwindow (k + 1) q (hS hq)).1
  · have hN' : (N : ℤ) ≤ 2 ^ k := by exact_mod_cast hN
    have hcard' : ((BS.P (k + 1)).card : ℤ) ≤ 2 ^ (k + 1) := by
      exact_mod_cast block_card_le BS (k + 1)
    have hkpos : (0 : ℤ) < 2 ^ k := pow_pos (by norm_num) k
    rw [pow_succ] at hm' ⊢
    nlinarith [abs_sub m' m,
      mul_le_mul_of_nonneg_left hN' hkpos.le,
      mul_le_mul_of_nonneg_left hcard' (by positivity : (0 : ℤ) ≤ 2 * 2 ^ k)]

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
    (Ek Ek1 : Finset ℕ) (hEk : Ek ⊆ BS.P k)
    (hlabel_k : ∀ p ∈ BS.P k \ Ek, (a p : ZMod p) = (m : ZMod p))
    (hlabel_k1 : ∀ q ∈ BS.P (k + 1) \ Ek1, (a q : ZMod q) = (m' : ZMod q))
    (hNk : 12 ≤ (BS.P k \ Ek).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k \ Ek).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    (((BS.P (k + 1) \ Ek1).card : ℝ) - 1) * ((BS.P k \ Ek).card : ℝ) ^ 3 /
        (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
  rotate_left;
  exact Finset.biUnion ( BS.P ( k + 1 ) \ Ek1 ) fun q => Finset.image ( fun p => ( p, q ) ) ( BS.P k \ Ek ) |> Finset.filter fun pq => ¬ ( q : ℤ ) ∣ ( m' - m );
  · simp +decide [ Finset.subset_iff, bipartitePairs ];
    grind;
  · exact fun _ _ _ => sq_nonneg _;
  · rw [ Finset.sum_biUnion ];
    · refine' le_trans _ ( Finset.sum_le_sum fun q hq => _ );
      rotate_left;
      use fun q => if ¬ ( q : ℤ ) ∣ m' - m then ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) else 0;
      · split_ifs <;> simp_all +decide [ Finset.sum_image ];
        rw [ ← Finset.sum_sdiff hEk ];
        have := LocalEnergy.crt_energy_lower_bound_for_fixed_outer_prime
          ( 2 ^ k ) ( by positivity ) ( BS.P k \ Ek ) ?_ ?_ q ?_ ?_ ?_
          m m' ?_ ?_ <;> norm_num at *;
        any_goals assumption;
        · convert this using 2
          all_goals try rfl
          unfold Hglob
          aesop
        · exact fun p hp hp' => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
        · exact BS.hprime _ _ hq.1;
        · have := BS.hwindow ( k + 1 ) q hq.1; norm_num [ pow_succ' ] at *; linarith;
        · have := BS.hwindow ( k + 1 ) q hq.1; norm_num [ pow_succ' ] at *; linarith;
      · have h_card : (Finset.filter (fun q : ℕ => ¬(q : ℤ) ∣ (m' - m)) (BS.P (k + 1) \ Ek1)).card ≥ (BS.P (k + 1) \ Ek1).card - 1 := by
          have hQ_card :
              (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m))
                (BS.P (k + 1) \\ Ek1)).card ≤ 1 :=
            adjacent_block_prime_divisor_count_le_one BS k (BS.P k \\ Ek).card
              m m' hmm
              (le_trans (Finset.card_le_card Finset.sdiff_subset) (block_card_le BS k))
              hm hm' (BS.P (k + 1) \\ Ek1) Finset.sdiff_subset
          have h_partition := Finset.card_filter_add_card_filter_not
            (s := BS.P (k + 1) \ Ek1) (fun q : ℕ => (q : ℤ) ∣ (m' - m))
          omega
        simp_all +decide [ Finset.sum_ite ];
        convert mul_le_mul_of_nonneg_right ( sub_le_sub_right ( Nat.cast_le.mpr h_card ) 1 ) ( by positivity : 0 ≤ ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) ) using 1 ; ring;
        norm_num [ Finset.filter_image ];
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;

end GlobalControl

end
