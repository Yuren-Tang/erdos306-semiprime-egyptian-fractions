/-
# Cold-block bounds

Energy-budget identities, exception-set control, cold-label bounds, and the
cross-block penalty forced by a boundary between distinct cold labels.
-/
import RequestProject.Core.Asymptotics
import RequestProject.GlobalControl.ColdBlockStructure
import RequestProject.GlobalControl.CrossBlockEnergy
import RequestProject.GlobalControl.EnergyBudget
import RequestProject.GlobalControl.Encoding.DominantLabels
import RequestProject.GlobalControl.Encoding.HotBlockCount
import RequestProject.LocalEnergy.DominantLabel

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-
**Sharper cold-label size bound.**  This is the `/64` specialization of the
parameterized local cold-label principle.
-/
lemma cold_label_bound_div_64 (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1],
          (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) →
          (X : ℝ) / (2 * Real.log X) ≤ P.card →
          ∀ (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
          |m| ≤ (X : ℤ) ^ 2 / 2 →
          (1 - (1/4:ℝ)) * (P.card : ℝ) ≤ ((P.attach.filter
              (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
          QP P a ≤ R → R ≤ c2 * X / (Real.log X) ^ 3 →
            |(m : ℝ)| ≤ (P.card : ℝ) * (X : ℝ) / 64 := by
  simpa using LocalEnergy.cold_label_bound_with_divisor
    (1 / 4) (by norm_num) (by norm_num) 64 (by norm_num) c2 hc2
set_option maxHeartbeats 1600000 in
/-- **Bundled cold-block facts.**  Produces the global cold constants `c2,e0`
    and, for every cold block, (i) a small exception set, (ii) a sharp label
    bound `|coldLabel| ≤ N·X/64`, and (iii) the conforming primes carry the
    label.  This is the per-block input to the boundary penalty. -/
lemma cold_block_facts :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p)) := by
  obtain ⟨c2, X0d, hc2, hX0d, hDom⟩ := cold_isDominant;
  obtain ⟨e0, X0e, he0, hX0e, hExc⟩ := LocalEnergy.cold_exception_count_bound (1/4) (by norm_num) (by norm_num) c2 hc2;
  obtain ⟨X0s6, hX0s6, hSize6⟩ := cold_label_bound_div_64 c2 hc2
  obtain ⟨X0w, _, hRw⟩ := block_energy_threshold_eventually_large 1 c2 hc2;
  refine' ⟨ c2, e0, Max.max X0d ( Max.max X0e ( Max.max X0s6 ( Max.max X0w 16 ) ) ), hc2, he0, _, _ ⟩ <;> norm_num;
  intro BS a k hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8
  have hcold := coldLabel_spec BS a k (hDom BS a k hk3 hk1 hk2 hk8)
  have hcold_size : |coldLabel BS a k| ≤ ((2 ^ k : ℕ) : ℤ) ^ 2 / 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcold.1
  refine' ⟨ _, _, _ ⟩;
  · convert hExc ( 2 ^ k ) ( mod_cast hk4 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
      exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) ( by
      unfold isHot at hk8; norm_num [ Rw ] at hk8; ring_nf at *;
      norm_num [ Real.log_pow ] at *;
      ring_nf at *;
      refine' ⟨ _, le_of_lt hk8 ⟩;
      calc
        1 ≤ Rw c2 k :=
          hRw k (Nat.pos_of_ne_zero (by rintro rfl; linarith [Nat.le_ceil X0d])) hk6
        _ = c2 * (Real.log 2)⁻¹ ^ 3 * (k : ℝ)⁻¹ ^ 3 * 2 ^ k := by
          rw [Rw, Real.log_pow]
          ring
    ) ( by
      convert hSize6 ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
        exact hcold_size ) ( by
        exact hcold.2 ) ( by
        exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
      constructor <;> intro h;
        · convert hSize6 ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
          exact hcold_size ) ( by
          exact hcold.2 ) ( by
          exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
      · refine' le_trans ( h _ ) _;
        · unfold isHot at hk8; norm_num [ Rw ] at hk8;
          norm_num [ Real.log_pow ] at *;
          exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk8 ⟩;
        · gcongr ; norm_num ) ( by
      exact hcold.2 ) using 1;
    convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( excSet_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ) using 1;
  · convert hSize6 ( 2 ^ k ) ( by exact_mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( Max.max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
      exact hcold_size ) ( by
      exact hcold.2 ) ( by
      exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
    norm_num +zetaDelta at *;
    exact ⟨ fun h => fun _ _ => h, fun h => h ( by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith ) ( by unfold isHot at hk8; norm_num [ Rw ] at hk8; linarith ) ⟩;
  · unfold excSet; aesop;

set_option maxHeartbeats 2000000 in
/-- **Note 40 §3d-iii/3d-iv master cold lemma.**  Produces the global cold
    constants and, besides the per-cold-block facts, the boundary penalty floor:
    every mismatch-boundary block contributes bipartite energy `≥ Pifloor`. -/
lemma boundary_penalty_per_k :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p))) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) := by
  obtain ⟨c2, e0, X0cbf, hc2, he0, hX0cbf, hCBF⟩ := cold_block_facts;
  obtain ⟨X0den, hX0den, hden⟩ := RequestProject.eventually_const_mul_log_le_nat (4*e0 + 26);
  use c2, e0, max X0cbf (max X0den 16); norm_num;
  refine' ⟨ hc2, he0, _, _ ⟩;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6; specialize hCBF BS a k hk1 hk2 hk3 hk6; aesop;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6
    set Nk := (BS.P k).card
    set Nk1 := (BS.P (k + 1)).card
    set ck := (BS.P k \ excSet BS a k).card
    set ck1 := (BS.P (k + 1) \ excSet BS a (k + 1)).card
    have hNk : 12 ≤ ck := by
      have hNk : Nk ≥ 2 * e0 + 13 := by
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
        have := hden ( 2 ^ k ) ( mod_cast hk4 ) ; norm_num at *;
        rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ) ) ( Real.log_pos one_lt_two ) ] ;
      have hck : (ck : ℝ) ≥ Nk - e0 := by
        have hck : (ck : ℝ) = Nk - (excSet BS a k).card := by
          exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card ( excSet_subset BS a k )
        generalize_proofs at *; (
        linarith [ hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) |>.1 ]);
      exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith )
    have hm : (32 : ℤ) * |coldLabel BS a k| ≤ (2 ^ k : ℤ) * ck := by
      have hck : (ck : ℝ) ≥ Nk - e0 := by
        have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
          exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
        convert add_le_add_left this.1 ck using 1 ; ring_nf;
        · rw_mod_cast [ ← Finset.card_union_of_disjoint ( Finset.disjoint_sdiff ), Finset.union_sdiff_of_subset ( excSet_subset BS a k ) ];
        · ring;
      have hck : (Nk : ℝ) ≥ 2 * e0 + 13 := by
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
        have := hden ( 2 ^ k ) ( by exact_mod_cast hk4 ) ; norm_num at *;
        rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ], Real.log_pos one_lt_two ];
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
        exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
      rw [ ← @Int.cast_le ℝ ] ; norm_num ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k ]
    have hm' : (32 : ℤ) * |coldLabel BS a (k + 1)| ≤ (2 ^ (k + 1) : ℤ) * Nk1 := by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by
        exact le_trans hk3 ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ( by
        unfold boundarySet at hk6; aesop; );
      rw [ ← @Int.cast_le ℝ ] ; push_cast ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k, pow_succ' ( 2 : ℝ ) k ]
    have hck : (ck : ℝ) ≥ Nk / 2 := by
      have hNk_ge : (Nk : ℝ) ≥ 2 * e0 + 13 := by
        have := hden ( 2 ^ k ) ( by simpa using hk4 ) ; norm_num at *;
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num at *;
        rw [ div_le_iff₀ ] at this <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ show ( 2 : ℝ ) ^ 0 = 1 by norm_num ] ) ) ) ( Real.log_pos one_lt_two ) ] ;
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) ; norm_num at * ; linarith [ show ( ck : ℝ ) = Nk - ( excSet BS a k |> Finset.card ) by exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card <| excSet_subset BS a k ] ;
    have hck1 : (ck1 : ℝ) ≥ Nk1 - e0 := by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by
        exact le_trans hk3 ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ( by
        exact Finset.mem_filter.mp hk6 |>.2.2.1 );
      simp +zetaDelta at *;
      rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a ( k + 1 ) ) ] ; linarith;
      · exact Finset.card_le_card fun x hx => by aesop;
    have hck2 : (ck : ℝ) ≥ Nk - e0 := by
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
        exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
      have hck2 : (ck : ℝ) = Nk - (excSet BS a k).card := by
        exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card <| Finset.filter_subset _ _;
      linarith
    have hck3 : (ck1 : ℝ) - 1 ≥ Nk1 - e0 - 1 := by
      linarith
    have hck4 : ((ck1 : ℝ) - 1) * (ck : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤ Xen BS a k := by
      apply consecutive_block_mismatch_energy_lower_bound BS (toPlain BS a) k
        (coldLabel BS a k) (coldLabel BS a (k + 1)) (by
      unfold boundarySet at hk6; aesop;) (excSet BS a k) (excSet BS a (k + 1)) (by
      exact hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) |>.2.2) (by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : k + 1 ≥ k ) ] ) ( by
        unfold boundarySet at hk6; aesop; ) ; aesop;) hNk hm hm'
    exact (by
    refine le_trans ?_ hck4;
    unfold Pifloor; gcongr;
    · exact pow_nonneg ( sub_nonneg_of_le <| by linarith [ show ( Nk : ℝ ) ≥ 2 * e0 + 13 by
                                                            have := BS.hdensity k hk1 ( by linarith ) ; norm_num at *;
                                                            have := hden ( 2 ^ k ) ( by exact_mod_cast hk4 ) ; norm_num at *;
                                                            rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ) ( Real.log_pos one_lt_two ) ] ] ) _;
    · have := BS.hdensity ( k + 1 ) ( by linarith [ show k + 1 ≥ BS.k0 from by linarith ] ) ( by linarith ) ; norm_num at *;
      refine' Nat.pos_of_ne_zero _;
      intro h; norm_num [ h ] at *;
      have := hden ( 2 ^ ( k + 1 ) ) ( by exact_mod_cast hk4.trans ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ; norm_num at *;
      rw [ div_le_iff₀ ] at * <;> nlinarith [ show 0 < ( k + 1 : ℝ ) * Real.log 2 by positivity, show ( 2 : ℝ ) ^ ( k + 1 ) > 0 by positivity ];
    · have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
      have := hden ( 2 ^ k ) ( mod_cast hk4 ) ; norm_num at *;
      rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ], Real.log_pos one_lt_two, mul_pos ( show ( k : ℝ ) > 0 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ] ) ( Real.log_pos one_lt_two ) ])

end GlobalControl

end
