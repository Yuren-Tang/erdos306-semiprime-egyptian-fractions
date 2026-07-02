import RequestProject.GlobalControl.Encoding.FixedLabelCount
import RequestProject.GlobalControl.LevelSetAdmissibility
import RequestProject.GlobalControl.LevelSetFiberBound
import RequestProject.GlobalControl.LevelSetLabelCharge

/-!
# Cold-fiber counting

Cold-regime dominance, residue-label rigidity, wrapped-label reduction, and
the resulting label-uniform fiber bound.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### Cold dominance and label admissibility -/

/-- **Cold-regime dominance for arbitrary block assignments.**
    At parameter `c2`, eventually every block-assignment of cold energy
    (`< Rw c2 k`) admits a dominant `(1/4)`-label.  This is
    `nondominant_energy_lower_bound` re-routed to `BlockSystem` blocks; it holds
    only for `c2` at most Theorem-B's intrinsic constant, so it is carried as a
    hypothesis through the cold-count chain. -/
def ColdDominance (c2 : ℝ) : Prop :=
  ∃ X1 : ℝ, 0 < X1 ∧ ∀ (BS : BlockSystem) (k : ℕ),
    BS.k0 ≤ k → k ≤ BS.K → X1 ≤ (2:ℝ) ^ k →
    ∀ (b : BlockAssignment (BS.P k)) (Rb : ℝ),
      QP (BS.P k) b ≤ Rb → Rb < Rw c2 k →
      LocalEnergy.HasDominantLabel ((2:ℕ) ^ k) (BS.P k) b (1/4)

/-- `Rw` is monotone in the constant `c2`. -/
lemma Rw_mono_c2 {c2 c2' : ℝ} (hc : c2 ≤ c2') (_hc0 : 0 ≤ c2) (k : ℕ) :
    Rw c2 k ≤ Rw c2' k := by
  have hden : 0 ≤ (Real.log (2 ^ k)) ^ 3 := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ 2 ^ k from one_le_pow₀ (by norm_num))
    positivity
  unfold Rw
  rcases hden.lt_or_eq with hd | hd
  · gcongr
  · rw [← hd]; simp

/-- Coldness only strengthens as `c2` shrinks: `¬ isHot` at the smaller constant
    implies `¬ isHot` at the larger one. -/
lemma not_isHot_mono_cold {c2 c2' : ℝ} (hc : c2 ≤ c2') (hc0 : 0 ≤ c2)
    (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    ¬ isHot BS c2 a k → ¬ isHot BS c2' a k := by
  intro h hHot
  exact h (le_trans (Rw_mono_c2 hc hc0 k) hHot)

/-- The boundary set grows with `c2`. -/
lemma boundarySet_mono {c2 c2' : ℝ} (hc : c2 ≤ c2') (hc0 : 0 ≤ c2)
    (BS : BlockSystem) (a : GlobalAssignment BS) :
    boundarySet BS c2 a ⊆ boundarySet BS c2' a := by
  intro k hk
  rw [boundarySet, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, not_isHot_mono_cold hc hc0 BS a k hk.2.1,
    not_isHot_mono_cold hc hc0 BS a (k+1) hk.2.2.1, hk.2.2.2⟩

/-
**Two-prime label rigidity.**  Two integer labels agreeing modulo at least
    two distinct primes from a window `[X, 2X]`, and differing by less than `X²`,
    must be equal.
-/
lemma two_prime_label_eq (X : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X)
    (m₁ m₂ : ℤ) (S : Finset { x // x ∈ P }) (hScard : 2 ≤ S.card)
    (hagree : ∀ p ∈ S, (m₁ : ZMod (p:ℕ)) = (m₂ : ZMod (p:ℕ)))
    (hbound : |m₁ - m₂| < (X:ℤ)^2) :
    m₁ = m₂ := by
  obtain ⟨ p₁, hp₁, p₂, hp₂, hne ⟩ := Finset.one_lt_card.mp hScard; have := hagree p₁ hp₁; have := hagree p₂ hp₂; simp_all +decide [ ZMod.intCast_eq_intCast_iff ] ;
  -- Since $p₁$ and $p₂$ are distinct primes, their product $p₁ * p₂$ divides $m₁ - m₂$.
  have h_div : (p₁.val * p₂.val : ℤ) ∣ (m₁ - m₂) := by
    convert Int.coe_lcm_dvd ( Int.modEq_iff_dvd.mp ( hagree p₁.1 p₁.2 hp₁ |> Int.ModEq.symm ) ) ( Int.modEq_iff_dvd.mp ( hagree p₂.1 p₂.2 hp₂ |> Int.ModEq.symm ) ) using 1 ; norm_cast;
    exact Eq.symm ( Nat.Coprime.lcm_eq_mul <| by have := Nat.coprime_primes ( hP _ p₁.2 |>.1 ) ( hP _ p₂.2 |>.1 ) ; aesop );
  -- Since $p₁$ and $p₂$ are distinct primes, their product $p₁ * p₂$ is at least $X^2$.
  have h_prod_ge_X2 : (p₁.val * p₂.val : ℤ) ≥ X^2 := by
    exact_mod_cast by nlinarith only [ hP p₁ p₁.2, hP p₂ p₂.2 ] ;
  exact Classical.not_not.1 fun h => by have := Int.le_of_dvd ( abs_pos.2 ( sub_ne_zero_of_ne h ) ) ( by simpa using h_div ) ; linarith [ abs_lt.mp hbound ] ;

/-
**Master cold constants.**  A single triple `(c2,e0,X0)` providing both the
    block-dominance (`HasDominantLabel`) used to read off cold labels and the boundary
    penalty floor.  Both are obtained from `boundary_penalty_per_k` (whose cold
    facts already expose, for the same `c2`, the residue agreement that yields
    dominance for `X0` large).
-/
lemma cold_master_struct :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) := by
  obtain ⟨ c2, e0, X0, hc2, he0, hX0, h ⟩ := boundary_penalty_per_k;
  obtain ⟨X0thr, hX0thr⟩ : ∃ X0thr : ℕ, ∀ X : ℕ, X0thr ≤ X → 16 * e0 * Real.log X ≤ X := by
    have := RequestProject.eventually_const_mul_log_le_nat ( 16 * e0 );
    exact ⟨ ⌈this.choose⌉₊, fun X hX => this.choose_spec.2 X <| Nat.le_of_ceil_le hX ⟩;
  refine' ⟨ c2, e0, Max.max X0 ( Max.max 16 X0thr ), hc2, he0, _, _, _ ⟩ <;> norm_num;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6
    obtain ⟨h_card, h_abs, h_res⟩ := h.left BS a k hk1 hk2 hk3 hk6
    have h_class_count : (classCount BS a k (coldLabel BS a k) : ℝ) ≥ (3 / 4 : ℝ) * (BS.P k).card := by
      have h_class_count : (classCount BS a k (coldLabel BS a k) : ℝ) ≥ (BS.P k).card - (excSet BS a k).card := by
        have h_class_count : (classCount BS a k (coldLabel BS a k) : ℝ) ≥ (BS.P k \ excSet BS a k).card := by
          rw [ conform_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ];
        rw [ Finset.card_sdiff ] at h_class_count;
        rw [ Nat.cast_sub ] at h_class_count;
        · exact le_trans ( sub_le_sub_left ( Nat.cast_le.mpr <| Finset.card_mono <| Finset.inter_subset_left ) _ ) h_class_count;
        · exact Finset.card_le_card fun x hx => by aesop;
      have h_card_bound : (BS.P k).card ≥ (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) := by
        exact BS.hdensity k hk1 hk2;
      have := hX0thr ( 2 ^ k ) ( by exact_mod_cast hk5 ) ; norm_num at *;
      rw [ div_le_iff₀ ] at h_card_bound <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hk4 ) ) ) ( Real.log_pos one_lt_two ) ]
    exact (by
    refine' ⟨ coldLabel BS a k, _, _ ⟩;
    · rw [ le_div_iff₀ ] at * <;> norm_cast at *;
      have h_card_le : (BS.P k).card ≤ 2 ^ k := by
        have h_card_le : (BS.P k).card ≤ Finset.card (Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
          exact Finset.card_le_card fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx;
        exact h_card_le.trans ( by norm_num [ pow_succ' ] ; linarith );
      rw [ Nat.le_iff_lt_or_eq ] at h_card_le ; norm_num at *;
      cases h_card_le <;> nlinarith [ Nat.div_add_mod ( ( 2 ^ k ) ^ 2 ) 2, Nat.mod_lt ( ( 2 ^ k ) ^ 2 ) two_pos ];
    · norm_num
      simpa only [classCount] using h_class_count.le);
  · exact fun BS a k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆ => h.2 BS a k hk₁ hk₂ hk₃ hk₆

/-
**Master cold constants** (with arbitrary-block-assignment cold dominance).
    Strengthens `cold_master_struct` by shrinking `c2` to also lie below
    Theorem-B's intrinsic constant, exposing `ColdDominance c2` in addition to
    the block dominance for restrictions and the boundary penalty floor.
-/
lemma cold_master :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) ∧
      ColdDominance c2 := by
  obtain ⟨c2P, e0, X0P, hc2P, he0, hX0P, hdomR, hpen⟩ := GlobalControl.cold_master_struct
  obtain ⟨c2B, X0B, hc2B, hX0B, HB⟩ := LocalEnergy.nondominant_energy_lower_bound (1/4) (by norm_num) (by norm_num);
  refine' ⟨ Min.min c2P c2B, e0, Max.max X0P ( Max.max X0B 1 ), _, _, _, _, _, _ ⟩ <;> norm_num [ hc2P, he0, hX0P, hc2B, hX0B ];
  · intro BS a k hk1 hk2 hX0P hX0B h1 hnh;
    apply hdomR BS a k hk1 hk2 hX0P;
    exact not_isHot_mono_cold ( min_le_left _ _ ) ( le_of_lt ( lt_min hc2P hc2B ) ) BS a k hnh;
  · intro BS a k hk1 hk2 hX0P hX0B h1 hk; exact hpen BS a k hk1 hk2 hX0P ( boundarySet_mono ( min_le_left _ _ ) ( le_of_lt ( lt_min hc2P hc2B ) ) BS a hk ) ;
  · refine' ⟨ Max.max X0B 1, by positivity, _ ⟩;
    intro BS k hk1 hk2 hk3 b Rb hQ hRb;
    contrapose! HB;
    refine' ⟨ 2 ^ k, _, BS.P k, _, _, _, b, Rb, hQ, HB, _ ⟩ <;> norm_num at *;
    · linarith;
    · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime k p hp ) ⟩;
    · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' ( 2 : ℕ ) k ] ⟩;
    · convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ];
    · refine lt_of_lt_of_le hRb ?_
      calc
        Rw (min c2P c2B) k ≤ Rw c2B k :=
          Rw_mono_c2 (min_le_right c2P c2B) (le_of_lt (lt_min hc2P hc2B)) k
        _ = c2B * 2 ^ k / ((k : ℝ) * Real.log 2) ^ 3 := by
          rw [Rw, Real.log_pow]

/-
**Label admissibility (`hadmL`).**  For `k0` past a uniform threshold, the
    zero-extended cold labels of any sub-`R` assignment lie in `admLabels`.
    This routes `coldLabel_mem_labelFin` (needing `HasDominantLabel` from `cold_master`)
    through every segment start.
-/
lemma hadmL_final (c2 X0 : ℝ) (hc2 : 0 < c2)
    (hdom : ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem), k0min ≤ BS.k0 → X0 ≤ (2:ℝ) ^ BS.k0 →
      ∀ (a : GlobalAssignment BS) (R : ℝ), 0 ≤ R → Qctrl BS a ≤ R →
        extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a)
          ∈ admLabels BS c2 R (hotSet BS c2 a) (boundarySet BS c2 a) := by
  -- Choose k0min such that for all s ≥ k0min, 16 ≤ 2^s, 8 ≤ (BS.P s).card, and 1 ≤ Real.log (2^s).
  obtain ⟨k0min, hk0min⟩ : ∃ k0min : ℕ, ∀ s : ℕ, k0min ≤ s →
      16 ≤ (2:ℕ) ^ s ∧ 8 ≤ (2 ^ s / (2 * Real.log (2 ^ s))) := by
        refine' ⟨ 16, fun s hs => ⟨ _, _ ⟩ ⟩;
        · exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) hs );
        · rw [ le_div_iff₀ ( by exact mul_pos zero_lt_two ( Real.log_pos ( one_lt_pow₀ one_lt_two ( by linarith ) ) ) ) ];
          induction hs <;> norm_num [ pow_succ' ] at *;
          · rw [ show ( 65536 : ℝ ) = 2 ^ 16 by norm_num, Real.log_pow ] ; norm_num ; linarith [ Real.log_le_sub_one_of_pos zero_lt_two ];
          · rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ];
            nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, ( by norm_cast : ( 16 : ℝ ) ≤ ↑‹ℕ› ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ‹16 ≤ _› ];
  use k0min;
  intro BS hBS hX0 a R hR0 hR1;
  apply extLabel_mem_admLabels;
  intro s hs
  have hs1 : BS.k0 ≤ s := by
    exact segStarts_le BS _ _ hs |>.1
  have hs2 : s ≤ BS.K := by
    exact segStarts_le BS _ _ hs |>.2
  have hslog : 1 ≤ Real.log (2 ^ s) := by
    rw [ Real.le_log_iff_exp_le ( by positivity ) ];
    exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ show ( 2 : ℝ ) ^ s ≥ 16 by exact_mod_cast hk0min s ( by linarith ) |>.1 ] )
  have hN8 : 8 ≤ (BS.P s).card := by
    have := BS.hdensity s ( by linarith ) ( by linarith );
    exact_mod_cast this.trans' ( hk0min s ( by linarith ) |>.2 )
  have hσpos : 0 < sigmaP (BS.P s) := by
    apply sigmaP_pos_of_two;
    · exact fun p hp => BS.hprime s p hp;
    · linarith
  have hbR : blockEnergy BS a s ≤ R := by
    exact le_trans ( Finset.single_le_sum ( fun k _ => QP_nonneg ( BS.P k ) ( restrict BS a k ) ) ( Finset.mem_Icc.mpr ⟨ hs1, hs2 ⟩ ) ) ( sum_blockEnergy_le BS a R hR1 )
  have hcold : ¬ isHot BS c2 a s := by
    have := Finset.mem_filter.mp hs; simp_all +decide [ Finset.mem_sdiff ] ;
    exact fun h => this.1 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hs1, hs2 ⟩, h ⟩
  have hdomk : LocalEnergy.HasDominantLabel (2 ^ s) (BS.P s) (restrict BS a s) (1 / 4) := by
    exact hdom BS a s hs1 hs2 ( by exact le_trans hX0 ( pow_le_pow_right₀ ( by norm_num ) hs1 ) ) hcold;
  apply coldLabel_mem_labelFin BS c2 R a s hs1 hs2 hR0 hc2.le (hk0min s (by linarith)).left hN8 hslog hdomk hcold hbR hσpos

/-
Block cardinality lower bound: past a uniform `2^k` threshold the block
    density forces `8 ≤ (BS.P k).card`.  (`2^k/(2 log 2^k) → ∞`.)
-/
lemma block_card_lower :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        8 ≤ (BS.P k).card := by
  -- Choose X0 such that for all k, if 2^k ≥ X0, then (2:ℝ)^k/(2*Real.log (2^k)) ≥ 8.
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, ∀ k ≥ K0, (2 : ℝ) ^ k / (2 * Real.log (2 ^ k)) ≥ 8 := by
    have h_tendsto : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / (2 * Real.log (2 ^ k))) Filter.atTop Filter.atTop := by
      have h_log : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / k) Filter.atTop Filter.atTop := by
        -- We can use the fact that $2^k / k$ grows exponentially.
        have h_exp_growth : Filter.Tendsto (fun k : ℕ => (Real.exp (k * Real.log 2)) / (k : ℝ)) Filter.atTop Filter.atTop := by
          have h_exp_growth : Filter.Tendsto (fun x : ℝ => Real.exp x / x) Filter.atTop Filter.atTop := by
            simpa using Real.tendsto_exp_div_pow_atTop 1;
          have := h_exp_growth.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos one_lt_two ) );
          convert this.const_mul_atTop ( show 0 < Real.log 2 by positivity ) using 2 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        simpa [ Real.exp_nat_mul, Real.exp_log ] using h_exp_growth
      convert h_log.const_mul_atTop ( show 0 < ( 1 / ( 2 * Real.log 2 ) ) by positivity ) using 2 ; norm_num [ Real.log_pow ] ; ring;
    exact Filter.eventually_atTop.mp ( h_tendsto.eventually_ge_atTop 8 );
  refine' ⟨ 2 ^ K0, by positivity, fun BS k hk₁ hk₂ hk₃ => _ ⟩;
  exact_mod_cast le_trans ( hK0 k ( Nat.le_of_not_lt fun hk₄ => not_le_of_gt ( pow_lt_pow_right₀ ( by norm_num ) hk₄ ) hk₃ ) ) ( BS.hdensity k hk₁ hk₂ )

/-
**Non-wrapped huge-label cold count (empty fiber).**  When the label is
    above `fixed_label_block_count`'s window (`N·2^k/16 < |m|`) but below the CRT wrap
    threshold (`|m| ≤ (2^k)²/2`), in the low-energy regime (`n+1 < Rw c2 k`) the
    fiber is EMPTY: by `dominant_label_bound` any `(3/4)`-conforming `b` of energy
    `≤ n+1` would force `|m| ≤ (20/3)√(n+1)/σ_k`, and combined with `block_deviation_lower_bound`
    and the density `N ≥ 2^k/(2 log 2^k)` this contradicts `N·2^k/16 < |m|` once
    `2^k` is large (`2^k` beats every power of `log 2^k`).
-/
lemma cold_count_nonwrap (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ) (n : ℕ),
          (n : ℝ) + 1 < Rw c2 k →
          ((BS.P k).card : ℝ) * (2 ^ k) / 16 < |((m : ℤ) : ℝ)| →
          |((m : ℤ) : ℝ)| ≤ ((2:ℝ) ^ k) ^ 2 / 2 →
          (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card = 0 := by
  -- Let's choose any $X0$ such that $X0 > 0$.
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, 0 < X0 ∧
    ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
      ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1], (∀ p ∈ P, Nat.Prime p ∧ (2:ℕ) ^ k ≤ p ∧ p ≤ 2 * (2:ℕ) ^ k) → (P.card : ℝ) ≥ (2:ℝ) ^ k / (2 * Real.log (2 ^ k)) →
      ∀ (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
        |m| ≤ (2 ^ k : ℤ) ^ 2 / 2 →
        (1 - (1/4:ℝ)) * (P.card : ℝ) ≤ ((P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
          QP P a ≤ R → R ≤ c2 * (2:ℝ) ^ k / (Real.log (2 ^ k)) ^ 3 →
            |(m : ℝ)| ≤ (P.card : ℝ) * (2 ^ k) / 16 := by
              obtain ⟨ X0, hX0_pos, hX0 ⟩ := GlobalControl.cold_label_bound_div_64 c2 hc2;
              use Nat.ceil X0;
              refine' ⟨ Nat.cast_pos.mpr ( Nat.ceil_pos.mpr hX0_pos ), _ ⟩;
              intro BS k hk1 hk2 hk3 P _ hP hP' a m R hR hm hR' hR''; specialize hX0 ( 2 ^ k ) ( by exact le_trans ( Nat.le_ceil _ ) ( mod_cast hk3 ) ) P; simp_all +decide [ Nat.cast_pow ] ;
              exact fun h => le_trans ( hX0 a m R hR hm hR' hR'' h ) ( by gcongr ; norm_num );
  obtain ⟨Xb, hXb⟩ : ∃ Xb : ℝ, 0 < Xb ∧
    ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → Xb ≤ (2:ℝ) ^ k →
      8 ≤ (BS.P k).card := by
        convert GlobalControl.block_card_lower;
  refine' ⟨ Max.max X0 ( Max.max Xb 16 ), _, _ ⟩ <;> norm_num;
  intro BS k hk1 hk2 hk3 hk4 hk5 m n hn hm₁ hm₂ x hx;
  contrapose! hX0;
  intro hX0_pos
  use BS, k, hk1, hk2, hk3, BS.P k, by
    exact fun p => ⟨ Nat.Prime.ne_zero ( BS.hprime k p.1 p.2 ) ⟩, by
    exact fun p hp => ⟨ BS.hprime k p hp, by have := BS.hwindow k p hp; ring_nf at *; linarith, by have := BS.hwindow k p hp; ring_nf at *; linarith ⟩, by
    exact BS.hdensity k hk1 hk2, x, m, n + 1, by
    linarith, by
    exact Int.le_ediv_of_mul_le ( by norm_num ) ( by rw [ ← @Int.cast_le ℝ ] ; push_cast; linarith ), by
    linarith, by
    convert hx using 1, by
    exact hn.le

/-
**Per-assignment small-label extraction with residue agreement.**
    For a cold block-assignment `b` conforming to a (possibly wrapped) label `m`
    on `≥ 3/4·N` primes, Theorem B yields a dominant label `mb` with
    `|mb| ≤ N·2^k/16`, conforming on `≥ 3/4·N` primes, and agreeing with `m`
    modulo `≥ 3/4·N - e0` primes (`e0` absolute).
-/
lemma cold_small_label_agree (c2 : ℝ) (hc2 : 0 < c2) (hdomB : ColdDominance c2) :
    ∃ (e0 X0 : ℝ), 0 < e0 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ) (n : ℕ), (n : ℝ) + 1 < Rw c2 k →
        ∀ (b : BlockAssignment (BS.P k)),
          QP (BS.P k) b ≤ (n : ℝ) + 1 →
          (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
            (((BS.P k).attach.filter (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
          ∃ mb : ℤ,
            |(mb : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16 ∧
            (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter (fun p => b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) ∧
            (3/4 : ℝ) * ((BS.P k).card : ℝ) - e0 ≤
              (((BS.P k).attach.filter
                (fun (p : {x // x ∈ BS.P k}) =>
                  ((m : ℤ) : ZMod (p : ℕ)) = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
  obtain ⟨X1, hX1pos, hdom⟩ := hdomB;
  obtain ⟨X0s, hX0s0, Hsize⟩ := LocalEnergy.cold_label_bound (1/4) (by norm_num) (by norm_num) c2 hc2
  obtain ⟨e0, X0e, he0pos, hX0e0, Hexc⟩ := LocalEnergy.cold_exception_count_bound (1/4) (by norm_num) (by norm_num) c2 hc2;
  refine' ⟨ e0, Max.max X1 ( Max.max X0s ( Max.max X0e 16 ) ), he0pos, _, _ ⟩ <;> norm_num;
  intro BS k hk1 hk2 hk3 hk4 hk5 hk6 m n hn b hQ hconf
  obtain ⟨mb, hmb_abs, hmb_conf⟩ := hdom BS k hk1 hk2 hk3 b ((n:ℝ)+1) hQ hn
  refine' ⟨mb, _, _, _⟩;
  · convert Hsize ( 2 ^ k ) ( mod_cast hk4 ) ( BS.P k ) _ _ b mb ( n + 1 ) _ _ _ _ using 1 <;> norm_num;
    any_goals assumption;
    · exact Or.inl <| le_of_lt <| by simpa [ Rw ] using hn;
    · exact fun p hp => ⟨ BS.hprime k p hp, BS.hwindow k p hp |>.1, by linarith [ BS.hwindow k p hp |>.2, pow_succ' ( 2 : ℕ ) k ] ⟩;
    · convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ];
    · linarith;
  · linarith;
  · have hmb_small : |(mb : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16 := by
      convert Hsize ( 2 ^ k ) _ ( BS.P k ) _ _ b mb ( n + 1 ) _ _ _ _ using 1 <;> norm_num;
      any_goals assumption;
      · exact Or.inl <| le_of_lt <| by simpa [ Rw ] using hn;
      · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' ( 2 : ℕ ) k ] ⟩;
      · convert BS.hdensity k hk1 hk2 using 1 ; ring_nf;
        norm_num [ Real.log_pow ] ; ring;
      · grind +revert;
    have hmb_small : ((Finset.univ.filter (fun q : {x // x ∈ BS.P k} => b q ≠ ((mb : ℤ) : ZMod (q : ℕ)))).card : ℝ) ≤ e0 := by
      convert Hexc ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) _ _ b mb ( n + 1 ) _ _ _ _ _ using 1 <;> norm_num;
      any_goals linarith;
      · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' ( 2 : ℕ ) k ] ⟩;
      · have := BS.hdensity k hk1 hk2;
        simpa [ Real.log_pow ] using this;
      · simpa [Rw, Real.log_pow] using hn.le
    have hmb_small : ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) ≥ ((BS.P k).card : ℝ) - e0 := by
      have hmb_small : ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) + ((Finset.univ.filter (fun q : {x // x ∈ BS.P k} => b q ≠ ((mb : ℤ) : ZMod (q : ℕ)))).card : ℝ) = (BS.P k).card := by
        rw_mod_cast [ Finset.card_filter_add_card_filter_not ];
        simp +decide;
      linarith;
    have hmb_small : ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)) ∧ b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) ≥ ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) + ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) - ((BS.P k).card : ℝ) := by
      have hmb_small : ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)) ∨ b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) ≤ ((BS.P k).card : ℝ) := by
        exact_mod_cast le_trans ( Finset.card_le_univ _ ) ( by norm_num );
      have hmb_small : ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)) ∨ b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) = ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) + ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) - ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)) ∧ b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
        rw [ ← Nat.cast_add, ← Finset.card_union_add_card_inter ];
        simp +decide [ Finset.filter_or, Finset.filter_and ];
      linarith;
    have hmb_small : ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => b p = ((m : ℤ) : ZMod (p : ℕ)) ∧ b p = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) ≤ ((Finset.univ.filter (fun p : {x // x ∈ BS.P k} => ((m : ℤ) : ZMod (p : ℕ)) = ((mb : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
      gcongr;
      exact fun h => h.1.symm.trans h.2;
    linarith!

/-- **Wrapped-label reduction.**
    In the low-energy wrapped regime, the assignments conforming to a large
    wrapped label `m` inject into the fixed-label fiber for one small label `M`.
    This is the Theorem-A-internal dominant-representative extraction and
    transport step; with it, `cold_count_wrap` is just `fixed_label_block_count`.  The cold
    dominance for arbitrary block assignments is supplied via `hdomB`. -/
lemma wrapped_count_le_small_fixed_label (c2 : ℝ) (hc2 : 0 < c2)
    (hdomB : ColdDominance c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ) (n : ℕ),
          (n : ℝ) + 1 < Rw c2 k →
          ((2:ℝ) ^ k) ^ 2 / 2 < |((m : ℤ) : ℝ)| →
          ∃ M : ℤ,
            |(M : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16 ∧
            ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤
            ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((M : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ) := by
  obtain ⟨e0, X0a, he0, hX0a, Hagree⟩ := cold_small_label_agree c2 hc2 hdomB
  obtain ⟨X0c, hX0c0, hlog⟩ := RequestProject.eventually_const_mul_log_le_nat (8 * e0 + 8)
  refine ⟨max X0a (max X0c 16), by positivity, fun BS k hk1 hk2 hk3 m n hn _hwrap => ?_⟩
  have hlogpos : 0 < Real.log ((2:ℝ) ^ k) := by
    apply Real.log_pos
    have : (16:ℝ) ≤ (2:ℝ) ^ k := le_trans (le_max_of_le_right (le_max_right _ _)) hk3
    linarith
  have hNbig : 4 * e0 + 4 ≤ ((BS.P k).card : ℝ) := by
    have hdens : (2:ℝ) ^ k / (2 * Real.log ((2:ℝ) ^ k)) ≤ ((BS.P k).card : ℝ) :=
      BS.hdensity k hk1 hk2
    have hL : (8 * e0 + 8) * Real.log ((2:ℝ) ^ k) ≤ (2:ℝ) ^ k := by
      have := hlog (2 ^ k) (by exact_mod_cast le_trans (le_max_of_le_right (le_max_left _ _)) hk3)
      simpa using this
    rw [div_le_iff₀ (by positivity)] at hdens
    nlinarith [hdens, hL, hlogpos]
  have hNX : ((BS.P k).card : ℤ) ≤ (2 : ℤ) ^ k := by exact_mod_cast GlobalControl.block_card_le BS k
  have hPwin : ∀ p ∈ BS.P k, Nat.Prime p ∧ 2 ^ k ≤ p ∧ p ≤ 2 * 2 ^ k := by
    intro p hp
    refine ⟨BS.hprime k p hp, (BS.hwindow k p hp).1, ?_⟩
    have h := (BS.hwindow k p hp).2
    have h2 : p < 2 * 2 ^ k := by rw [← pow_succ']; exact h
    omega
  classical
  by_cases hfe :
      (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
        QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
        (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
          (((BS.P k).attach.filter (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card = 0
  · refine ⟨0, by simp only [Int.cast_zero, abs_zero]; positivity, ?_⟩
    rw [hfe, Nat.cast_zero]
    exact Nat.cast_nonneg _
  · obtain ⟨b0, hb0mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hfe)
    rw [Finset.mem_filter] at hb0mem
    obtain ⟨M, hM_small, hM_conf, hM_agree⟩ :=
      Hagree BS k hk1 hk2 (le_trans (le_max_left _ _) hk3) m n hn b0 hb0mem.2.1 hb0mem.2.2
    refine ⟨M, hM_small, ?_⟩
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    obtain ⟨mb, hmb_small, hmb_conf, hmb_agree⟩ :=
      Hagree BS k hk1 hk2 (le_trans (le_max_left _ _) hk3) m n hn b hb.2.1 hb.2.2
    set A : Finset {x // x ∈ BS.P k} :=
      (BS.P k).attach.filter (fun p => ((m : ℤ) : ZMod (p : ℕ)) = ((mb : ℤ) : ZMod (p : ℕ))) with hAdef
    set B : Finset {x // x ∈ BS.P k} :=
      (BS.P k).attach.filter (fun p => ((m : ℤ) : ZMod (p : ℕ)) = ((M : ℤ) : ZMod (p : ℕ))) with hBdef
    have hmbM : mb = M := by
      apply two_prime_label_eq (2 ^ k) (BS.P k) hPwin mb M (A ∩ B)
      · have hcards := Finset.card_union_add_card_inter A B
        have hsub : A ∪ B ⊆ (BS.P k).attach :=
          Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hUle := Finset.card_le_card hsub
        rw [Finset.card_attach] at hUle
        have hcardsR : ((A ∪ B).card : ℝ) + ((A ∩ B).card : ℝ)
            = (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcards
        have hUleR : ((A ∪ B).card : ℝ) ≤ ((BS.P k).card : ℝ) := by exact_mod_cast hUle
        have hAc : (3/4 : ℝ) * ((BS.P k).card : ℝ) - e0 ≤ (A.card : ℝ) := by
          simpa only [hAdef] using hmb_agree
        have hBc : (3/4 : ℝ) * ((BS.P k).card : ℝ) - e0 ≤ (B.card : ℝ) := by
          simpa only [hBdef] using hM_agree
        rw [← Nat.cast_le (α := ℝ)]; push_cast
        nlinarith [hUleR, hcardsR, hAc, hBc, hNbig]
      · intro p hp
        rw [Finset.mem_inter, hAdef, hBdef, Finset.mem_filter, Finset.mem_filter] at hp
        exact hp.1.2.symm.trans hp.2.2
      · have hb1 : |(mb : ℝ) - (M : ℝ)| ≤ ((BS.P k).card : ℝ) * 2 ^ k / 8 := by
          have h1 := abs_le.mp hmb_small; have h2 := abs_le.mp hM_small
          rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        have hNle : ((BS.P k).card : ℝ) ≤ (2:ℝ) ^ k := by exact_mod_cast hNX
        have hb2 : |(mb : ℝ) - (M : ℝ)| < ((2:ℝ) ^ k) ^ 2 := by
          have hpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
          nlinarith [hb1, hNle, hpos]
        have e1 : ((|mb - M| : ℤ) : ℝ) = |(mb : ℝ) - (M : ℝ)| := by
          rw [Int.cast_abs]; push_cast; ring_nf
        have e2 : (((2 ^ k : ℤ) ^ 2 : ℤ) : ℝ) = ((2:ℝ) ^ k) ^ 2 := by push_cast; ring
        have hcast : ((|mb - M| : ℤ) : ℝ) < (((2 ^ k : ℤ) ^ 2 : ℤ) : ℝ) := by
          rw [e1, e2]; exact hb2
        exact_mod_cast hcast
    refine ⟨Finset.mem_univ _, hb.2.1, ?_⟩
    rw [← hmbM]; exact hmb_conf

/-- **Wrapped huge-label cold count.**
    For a label beyond the CRT wrap threshold (`(2^k)²/2 < |m|`), the per-block
    conforming count is still `≤ exp(2ε(n+1))`.  The actual wrapped-label work is
    isolated in `wrapped_count_le_small_fixed_label`; this lemma only applies
    `fixed_label_block_count` to the resulting small fixed label. -/
lemma cold_count_wrap (eps : ℝ) (heps : 0 < eps) (_heps1 : eps < 1)
    (c2 : ℝ) (hc2 : 0 < c2) (hdomB : ColdDominance c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ) (n : ℕ),
          (n : ℝ) + 1 < Rw c2 k →
          ((2:ℝ) ^ k) ^ 2 / 2 < |((m : ℤ) : ℝ)| →
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤ Real.exp (2 * eps * ((n : ℝ) + 1)) := by
  obtain ⟨Xr, hXr0, hReduce⟩ := wrapped_count_le_small_fixed_label c2 hc2 hdomB
  obtain ⟨Xc, hXc0, hCold⟩ := fixed_label_block_count (2 * eps) (by positivity)
  refine ⟨max Xr Xc, by positivity, ?_⟩
  intro BS k hk1 hk2 hk3 m n hn hwrap
  obtain ⟨M, hMsmall, hleM⟩ :=
    hReduce BS k hk1 hk2 (le_trans (le_max_left _ _) hk3) m n hn hwrap
  exact le_trans hleM
    (by
      convert hCold BS k hk1 hk2 (le_trans (le_max_right _ _) hk3) M hMsmall n using 1)

/-- **Huge-label cold count in the low-energy
    regime.**  For a cold block (`n+1 < Rw c2 k`) and a label `m` LARGER than
    `fixed_label_block_count`'s window (`|m| > N·2^k/16`), the count of `(3/4)`-conforming
    block-assignments of energy `≤ n+1` is `≤ exp(2ε(n+1))`.  Case split on the CRT
    wrap threshold `(2^k)²/2`: non-wrapped via `cold_count_nonwrap` (empty fiber),
    wrapped via `cold_count_wrap`. -/
lemma cold_count_huge_label (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 : ℝ) (hc2 : 0 < c2) (hdomB : ColdDominance c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ) (n : ℕ),
          (n : ℝ) + 1 < Rw c2 k →
          ((BS.P k).card : ℝ) * (2 ^ k) / 16 < |((m : ℤ) : ℝ)| →
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤ Real.exp (2 * eps * ((n : ℝ) + 1)) := by
  obtain ⟨Xnw, hXnw0, hNW⟩ := cold_count_nonwrap c2 hc2
  obtain ⟨Xw, hXw0, hW⟩ := cold_count_wrap eps heps heps1 c2 hc2 hdomB
  refine ⟨max Xnw Xw, by positivity, fun BS k hk1 hk2 hk3 m n hn hm => ?_⟩
  by_cases hwrap : |((m : ℤ) : ℝ)| ≤ ((2:ℝ) ^ k) ^ 2 / 2
  · rw [hNW BS k hk1 hk2 (le_trans (le_max_left _ _) hk3) m n hn hm hwrap]
    simpa using Real.exp_nonneg (2 * eps * ((n : ℝ) + 1))
  · exact hW BS k hk1 hk2 (le_trans (le_max_right _ _) hk3) m n hn (lt_of_not_ge hwrap)

/-
**Label-uniform per-cold-block count.**  For ANY label `m` (no size bound)
    and ANY shell `n`, the count of `(3/4)`-conforming block-assignments of
    energy `≤ n+1` is `≤ exp(2ε(n+1))`.  Proof by case analysis:
    * if `Rw c2 k ≤ n+1` (energy floor met), the unconstrained count is already
      `≤ exp(2ε(n+1))` via `hot_block_count`;
    * else, if `|m| ≤ N·2^k/16`, the conforming count is `≤ exp(ε(n+1))` via
      `fixed_label_block_count`;
    * else (`|m| > N·2^k/16` and `n+1 < Rw c2 k`) it is `cold_count_huge_label`.
-/
lemma cold_count_large (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 : ℝ) (hc2 : 0 < c2) (hdomB : ColdDominance c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ) (n : ℕ),
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤ Real.exp (2 * eps * ((n : ℝ) + 1)) := by
  obtain ⟨Xh, hXh0, hHot⟩ := hot_block_count eps heps heps1 c2 hc2
  obtain ⟨Xc, hXc0, hCold⟩ := fixed_label_block_count eps heps
  obtain ⟨Xg, hXg0, hHuge⟩ := cold_count_huge_label eps heps heps1 c2 hc2 hdomB
  use max Xh (max Xc Xg);
  refine' ⟨ by positivity, fun BS k hk1 hk2 hk3 m n => _ ⟩;
  by_cases hRw : Rw c2 k ≤ (n : ℝ) + 1;
  · refine' le_trans _ ( hHot BS k hk1 hk2 ( le_trans ( le_max_left _ _ ) hk3 ) n hRw );
    exact_mod_cast Finset.card_le_card fun x hx => by aesop;
  · by_cases hm : |(m : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16;
    · exact le_trans ( hCold BS k hk1 hk2 ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hk3 ) m hm n ) ( Real.exp_le_exp.mpr ( by nlinarith ) );
    · exact hHuge BS k hk1 hk2 ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hk3 ) m n ( not_le.mp hRw ) ( not_le.mp hm )

/-
**Label-uniform per-fiber count.**  The per-fiber
count `∏_k exp(2ε(v_k+1))` holds for every label
    assignment `ℓ`.  Hot blocks use `hot_block_count`; cold blocks use the
    label-uniform `cold_count_large`.
-/
lemma fiber_card_exp_bound (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 : ℝ) (hc2 : 0 < c2) (hdomB : ColdDominance c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ),
        X0 ≤ (2:ℝ) ^ BS.k0 →
        (∀ k ∈ Finset.Icc BS.k0 BS.K, k ∈ H → Rw c2 k ≤ (v k : ℝ) + 1) →
        ((fiber BS H B v ℓ).card : ℝ) ≤
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
  obtain ⟨Xh, hXh0, hHot⟩ := GlobalControl.hot_block_count eps heps heps1 c2 hc2
  obtain ⟨Xc, hXc0, hCold⟩ := GlobalControl.cold_count_large eps heps heps1 c2 hc2 hdomB
  use max Xh Xc
  constructor
  ·
    positivity
  ·
    intro BS H B v ℓ hX hHot';
    apply GlobalControl.fiber_prod_bound;
    intro k hk; by_cases hkH : k ∈ H <;> simp_all +decide ;
    · exact hHot BS k hk.1 hk.2 ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hk.1 ] ) _ ( hHot' k hk.1 hk.2 hkH );
    · exact hCold BS k hk.1 hk.2 ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hk.1 ] ) _ _

end GlobalControl

end
