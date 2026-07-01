/-
# Cross-block energy

Deterministic reciprocal-phase dispersion and the energy penalty forced by a
label mismatch between consecutive prime blocks.
-/
import RequestProject.GlobalControl.Basic
import RequestProject.LocalEnergy.AdjacentScaleEnergy

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! The local reciprocal-dispersion and fixed-outer-prime energy bounds live in
`LocalEnergy.AdjacentScaleEnergy`. This module specializes them to consecutive
blocks of a `BlockSystem`. -/

/-
**Consecutive-block mismatch penalty.** Two consecutive blocks with *distinct*
    labels `m ≠ m'` contribute bipartite control energy at least
    `Πₖ = N_{k+1}·Nₖ³/(2¹⁶·Xₖ²)`.

    The original statement was false because it omitted these hypotheses:
    `hm`/`hm'` are the required label-size bounds, and
    `hNk`/`hNk1` are the block-density regularity used by the dispersion count.

    It follows from `LocalEnergy.crt_energy_lower_bound_for_fixed_outer_prime`,
    summed over the
    `≥ N_{k+1}/2` good vertices `q ∤ m'-m`.
-/
set_option maxHeartbeats 1000000 in
theorem mismatch_penalty (BS : BlockSystem) (a : (p : ℕ) → ZMod p) (k : ℕ)
    (_hk1 : BS.k0 ≤ k) (_hk2 : k < BS.K)
    (m m' : ℤ) (hmm : m ≠ m')
    (hlabel : (∀ p ∈ BS.P k, (a p : ZMod p) = (m : ZMod p)) ∧
              (∀ q ∈ BS.P (k + 1), (a q : ZMod q) = (m' : ZMod q)))
    (hNk : 12 ≤ (BS.P k).card) (hNk1 : 2 ≤ (BS.P (k + 1)).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    ((BS.P (k + 1)).card : ℝ) * ((BS.P k).card : ℝ) ^ 3 /
        (2 ^ 16 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  -- By definition of $P_k$ and $P_{k+1}$, we know that $P_k \subseteq \{2^k, 2^k + 1, \ldots, 2^{k+1} - 1\}$ and $P_{k+1} \subseteq \{2^{k+1}, 2^{k+1} + 1, \ldots, 2^{k+2} - 1\}$.
  have hP_k_subset : BS.P k ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
    exact fun p hp => Finset.mem_Ico.mpr <| BS.hwindow k p hp
  have hP_k1_subset : BS.P (k + 1) ⊆ Finset.Ico (2 ^ (k + 1)) (2 ^ (k + 2)) := by
    exact fun p hp => Finset.mem_Ico.mpr <| BS.hwindow _ _ hp;
  have h_good_set : ∃ Q : Finset ℕ, Q ⊆ BS.P (k + 1) ∧ Q.card ≥ (BS.P (k + 1)).card / 2 ∧ ∀ q ∈ Q, ¬(q : ℤ) ∣ (m' - m) := by
    have h_bad_set : (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card ≤ 1 := by
      have h_pair : ∀ q q' : ℕ, q ∈ BS.P (k + 1) → q' ∈ BS.P (k + 1) → q ≠ q' → ¬((q : ℤ) ∣ (m' - m)) ∨ ¬((q' : ℤ) ∣ (m' - m)) := by
        intros q q' hq hq' hneq
        by_contra h_contra
        push Not at h_contra
        have h_div : (q * q' : ℤ) ∣ (m' - m) := by
          convert Int.coe_lcm_dvd h_contra.1 h_contra.2 using 1;
          exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( BS.hprime ( k + 1 ) q hq ) ( BS.hprime ( k + 1 ) q' hq' ) ; aesop )
        have h_abs : |m' - m| ≥ (q * q' : ℤ) := by
          exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( Ne.symm hmm ) ) ) ( by simpa )
        have h_abs_le : |m' - m| ≤ |m| + |m'| := by
          cases abs_cases ( m' - m ) <;> cases abs_cases m <;> cases abs_cases m' <;> linarith
        have h_abs_le' : |m| + |m'| < (q * q' : ℤ) := by
          have h_abs_le' : (BS.P k).card ≤ 2 ^ k ∧ (BS.P (k + 1)).card ≤ 2 ^ (k + 1) := by
            have := Finset.card_le_card hP_k_subset; have := Finset.card_le_card hP_k1_subset; simp_all +decide [ pow_succ' ] ;
            exact ⟨ by omega, by omega ⟩;
          have h_abs_le' : (q : ℤ) ≥ 2 ^ (k + 1) ∧ (q' : ℤ) ≥ 2 ^ (k + 1) := by
            exact ⟨ mod_cast Finset.mem_Ico.mp ( hP_k1_subset hq ) |>.1, mod_cast Finset.mem_Ico.mp ( hP_k1_subset hq' ) |>.1 ⟩;
          norm_num [ pow_succ' ] at *;
          nlinarith [ pow_pos ( zero_lt_two' ℤ ) k, Int.mul_ediv_add_emod ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) 32, Int.emod_nonneg ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) ( by norm_num : ( 32 : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) ( by norm_num : ( 32 : ℤ ) > 0 ) ]
        linarith [h_abs, h_abs_le, h_abs_le'];
      refine Finset.card_le_one.mpr ?_
      intro q hq q' hq'
      by_contra hne
      rcases h_pair q q' (Finset.mem_filter.mp hq).1
          (Finset.mem_filter.mp hq').1 hne with hq_bad | hq'_bad
      · exact hq_bad (Finset.mem_filter.mp hq).2
      · exact hq'_bad (Finset.mem_filter.mp hq').2
    have h_good_set : (Finset.filter (fun q : ℕ => ¬(q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card = (BS.P (k + 1)).card - (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card := by
      have h_partition := Finset.card_filter_add_card_filter_not
        (s := BS.P (k + 1)) (fun q : ℕ => (q : ℤ) ∣ (m' - m))
      omega
    simp_all +decide
    grind +qlia;
  obtain ⟨ Q, hQ₁, hQ₂, hQ₃ ⟩ := h_good_set;
  have h_sum_bound : ∑ pq ∈ bipartitePairs BS k, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 ≥ ∑ q ∈ Q, ∑ p ∈ BS.P k, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 := by
    have h_sum_bound : ∑ pq ∈ bipartitePairs BS k, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 ≥ ∑ pq ∈ (BS.P k) ×ˢ Q, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.product_subset_product ( Finset.Subset.refl _ ) hQ₁ ) fun _ _ _ => sq_nonneg _;
    convert h_sum_bound using 1;
    rw [ Finset.sum_product, Finset.sum_comm ];
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [ Hglob, hlabel.1 x hx, hlabel.2 y ( hQ₁ hy ) ] ;
  have h_sum_bound : ∑ q ∈ Q, ∑ p ∈ BS.P k, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 ≥ ∑ q ∈ Q, ((BS.P k).card : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2) := by
    apply Finset.sum_le_sum;
    intro q hq;
    convert LocalEnergy.crt_energy_lower_bound_for_fixed_outer_prime
      ( 2 ^ k ) ( by positivity ) ( BS.P k ) ( fun p hp => ?_ ) hNk q
      ( ?_ ) ( ?_ ) ( ?_ ) m m' ( ?_ ) ( ?_ ) using 1;
    all_goals norm_cast;
    any_goals tauto;
    · exact ⟨ BS.hprime k p hp, by linarith [ Finset.mem_Ico.mp ( hP_k_subset hp ) ], by linarith [ Finset.mem_Ico.mp ( hP_k_subset hp ), pow_succ' 2 k ] ⟩;
    · exact BS.hprime _ _ ( hQ₁ hq );
    · have := hP_k1_subset ( hQ₁ hq ) ; norm_num [ pow_succ' ] at * ; linarith;
    · have := hP_k1_subset ( hQ₁ hq ) ; norm_num [ pow_succ' ] at * ; linarith;
  refine le_trans ?_ ( le_trans h_sum_bound ‹_› );
  norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  field_simp;
  norm_cast ; linarith [ Nat.div_add_mod ( BS.P ( k + 1 ) |> Finset.card ) 2, Nat.mod_lt ( BS.P ( k + 1 ) |> Finset.card ) two_pos ]

/-
**Consecutive-block mismatch penalty with exceptions.** The cold blocks of the
    global level-set argument carry a *bounded* exception set `Eₖ` of vertices
    where the dominant label fails. Reusing
    `LocalEnergy.crt_energy_lower_bound_for_fixed_outer_prime` over the reduced
    sets `Pₖ \ Eₖ` and `Pₖ₊₁ \ Eₖ₊₁` gives the same bipartite penalty with the
    reduced cardinalities.  The no-exception `mismatch_penalty` is the special
    case `Eₖ = Eₖ₊₁ = ∅`.

    Proof: identical to `mismatch_penalty`, with `Pₖ` replaced by `Pₖ \ Eₖ` (the
    dispersion vertex set) and the "good" outer vertices drawn from
    `Pₖ₊₁ \ Eₖ₊₁`; at most one of those divides `m'-m`, so at least
    `(Pₖ₊₁ \ Eₖ₊₁).card - 1` are good.

    (The hypothesis `hEk1 : Eₖ₊₁ ⊆ Pₖ₊₁` is part of note 36's requested
    interface; the finished proof does not actually use it.)
-/
set_option maxHeartbeats 1000000 in
theorem mismatch_penalty_with_exceptions (BS : BlockSystem)
    (a : (p : ℕ) → ZMod p) (k : ℕ)
    (m m' : ℤ) (hmm : m ≠ m')
    (Ek Ek1 : Finset ℕ) (hEk : Ek ⊆ BS.P k) (_hEk1 : Ek1 ⊆ BS.P (k + 1))
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
          have hQ_card : (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1) \ Ek1)).card ≤ 1 := by
            have h_good_outer : ∀ q ∈ (BS.P (k + 1)) \ Ek1, ∀ q' ∈ (BS.P (k + 1)) \ Ek1, q ≠ q' → ¬((q : ℤ) ∣ (m' - m) ∧ (q' : ℤ) ∣ (m' - m)) := by
              intros q hq q' hq' hneq hdiv
              have hprod : (q * q' : ℤ) ∣ (m' - m) := by
                convert Int.coe_lcm_dvd hdiv.1 hdiv.2 using 1;
                exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( BS.hprime ( k + 1 ) q <| Finset.mem_sdiff.mp hq |>.1 ) ( BS.hprime ( k + 1 ) q' <| Finset.mem_sdiff.mp hq' |>.1 ) ; aesop );
              have hprod_le : (q * q' : ℤ) ≤ |m' - m| := by
                exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr hmm.symm ) ) ( by simpa );
              have hprod_ge : (q * q' : ℤ) ≥ 2 ^ (2 * k + 2) := by
                have hprod_ge : (q : ℤ) ≥ 2 ^ (k + 1) ∧ (q' : ℤ) ≥ 2 ^ (k + 1) := by
                  exact ⟨ mod_cast BS.hwindow ( k + 1 ) q ( Finset.mem_sdiff.mp hq |>.1 ) |>.1, mod_cast BS.hwindow ( k + 1 ) q' ( Finset.mem_sdiff.mp hq' |>.1 ) |>.1 ⟩;
                exact le_trans ( by ring_nf; norm_num ) ( mul_le_mul hprod_ge.1 hprod_ge.2 ( by positivity ) ( by positivity ) );
              have hprod_le : (BS.P k \ Ek).card ≤ 2 ^ k ∧ (BS.P (k + 1)).card ≤ 2 ^ (k + 1) := by
                have hprod_le : ∀ k, (BS.P k).card ≤ 2 ^ k := by
                  intros k
                  have hprod_le : (BS.P k).card ≤ Finset.card (Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
                    exact Finset.card_le_card fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx;
                  exact hprod_le.trans ( by norm_num [ pow_succ' ] ; linarith );
                exact ⟨ le_trans ( Finset.card_le_card ( Finset.sdiff_subset ) ) ( hprod_le k ), hprod_le ( k + 1 ) ⟩;
              norm_num [ pow_add, pow_mul' ] at *;
              nlinarith [ abs_sub m' m, pow_pos ( zero_lt_two' ℤ ) k ];
            refine Finset.card_le_one.mpr ?_
            intro q hq q' hq'
            by_contra hne
            exact h_good_outer q (Finset.mem_filter.mp hq).1 q'
              (Finset.mem_filter.mp hq').1 hne
              ⟨(Finset.mem_filter.mp hq).2, (Finset.mem_filter.mp hq').2⟩
          have h_partition := Finset.card_filter_add_card_filter_not
            (s := BS.P (k + 1) \ Ek1) (fun q : ℕ => (q : ℤ) ∣ (m' - m))
          omega
        simp_all +decide [ Finset.sum_ite ];
        convert mul_le_mul_of_nonneg_right ( sub_le_sub_right ( Nat.cast_le.mpr h_card ) 1 ) ( by positivity : 0 ≤ ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) ) using 1 ; ring;
        norm_num [ Finset.filter_image ];
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;

end GlobalControl

end
