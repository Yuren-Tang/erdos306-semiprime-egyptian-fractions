import RequestProject.GlobalControl.ColdBlockStructure
import RequestProject.GlobalControl.Encoding.HotBlockCount

/-!
# Cold-block estimates

Uniform exception-count and dominant-label bounds for sufficiently large cold
blocks.
-/

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

end GlobalControl

end
