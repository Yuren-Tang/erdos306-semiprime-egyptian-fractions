/-
# Entropy bounds for block encodings

Cardinality and asymptotic estimates showing that hot-block, cold-label, and
energy-shell data are absorbed by the available energy budget.
-/
import RequestProject.GlobalControl.BlockEncoding
import RequestProject.LocalEnergy.LevelSet

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-
**Hole 11 (`trivial_regime`).**  In the trivial regime `R ≥ Rtriv` the total
    number of global assignments is already `≤ exp(εR)`.  Here
    `Rtriv = ε⁻¹·2^{K+2}·(K+1)`.  (Counts `∏ p ≤ exp(∑_k N_k(k+1)log2)`,
    `N_k ≤ 2^k`.)
-/
lemma trivial_regime (eps : ℝ) (heps : 0 < eps) (BS : BlockSystem) (R : ℝ)
    (hR : eps⁻¹ * 2 ^ (BS.K + 2) * ((BS.K : ℝ) + 1) ≤ R) :
    (Fintype.card (GlobalAssignment BS) : ℝ) ≤ Real.exp (eps * R) := by
  -- We can bound each product term $p \leq 2^{k+1}$ for $p \in P_k$ and sum over $k$.
  have h_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (BS.P k).card * Real.log (2 ^ (k + 1)) := by
    have h_log_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, ∑ p ∈ BS.P k, Real.log p := by
      have h_log : Real.log (Fintype.card (GlobalAssignment BS)) = ∑ p ∈ blockSupport BS, Real.log p := by
        have h_card : (Fintype.card (GlobalAssignment BS)) = ∏ p ∈ blockSupport BS, p := by
          unfold GlobalAssignment; simp +decide [ Fintype.card_pi ] ;
          conv_rhs => rw [ ← Finset.prod_attach ] ;
        rw [ h_card, Nat.cast_prod, Real.log_prod ] ; norm_num;
        exact fun h => by obtain ⟨ k, hk, hk' ⟩ := Finset.mem_biUnion.mp h; have := BS.hwindow k 0 hk'; norm_num at this;
      rw [ h_log, blockSupport, Finset.sum_biUnion ];
      exact fun k hk l hl hkl => blocks_disjoint BS hkl;
    refine le_trans h_log_bound <| Finset.sum_le_sum fun k hk => ?_;
    exact le_trans ( Finset.sum_le_sum fun x hx => Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| BS.hprime k x hx ) <| show ( x : ℝ ) ≤ 2 ^ ( k + 1 ) by exact_mod_cast Nat.le_of_lt <| BS.hwindow k x hx |>.2 ) <| by norm_num;
  -- We can bound each term $\log(2^{k+1}) = (k+1)\log(2)$ and use the fact that $(BS.P k).card \leq 2^k$.
  have h_bound' : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (2 ^ k : ℝ) * (k + 1) * Real.log 2 := by
    refine le_trans h_bound <| Finset.sum_le_sum fun k hk => ?_;
    norm_num [ mul_assoc ];
    gcongr;
    exact_mod_cast le_trans ( Finset.card_le_card ( show BS.P k ⊆ Finset.Ico ( 2 ^ k ) ( 2 ^ ( k + 1 ) ) from fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx ) ) ( by norm_num [ pow_succ' ] ; linarith );
  -- We can bound the sum $\sum_{k=k0}^{K} 2^k (k+1)$ by $2^{K+1} (K+1)$.
  have h_sum_bound : ∑ k ∈ Finset.Icc BS.k0 BS.K, (2 ^ k : ℝ) * (k + 1) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) := by
    have h_sum_bound : ∑ k ∈ Finset.range (BS.K + 1), (2 ^ k : ℝ) * (k + 1) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) := by
      exact Nat.recOn BS.K ( by norm_num ) fun n ihn => by norm_num [ Finset.sum_range_succ, pow_succ' ] at * ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) n ] ;
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) fun _ _ _ => by positivity ) h_sum_bound;
  -- We can bound the sum $\sum_{k=k0}^{K} 2^k (k+1)$ by $2^{K+1} (K+1)$ and use the fact that $\log(2) < 1$.
  have h_final_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) * Real.log 2 := by
    exact h_bound'.trans ( by rw [ ← Finset.sum_mul _ _ _ ] ; exact mul_le_mul_of_nonneg_right h_sum_bound <| Real.log_nonneg <| by norm_num );
  rw [ ← Real.log_le_iff_le_exp ( Nat.cast_pos.mpr <| Fintype.card_pos_iff.mpr ⟨ fun _ => 0 ⟩ ) ];
  refine le_trans h_final_bound ?_;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left hR heps.le ) ; ring_nf ; norm_num [ heps.ne' ];
  nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, show ( 0 : ℝ ) ≤ 2 ^ BS.K by positivity, show ( 0 : ℝ ) ≤ BS.K * 2 ^ BS.K by positivity ]

/-
**Hole 9 (`cold_factor`).**  Per-cold-block fixed-label count: for a label
    of size `|m| ≤ N·X/16` the number of block assignments of energy `≤ n+1`
    whose `m`-class covers a `(1-ρ)` fraction is `≤ exp(ε(n+1))`.  Direct wrapper
    of `LocalEnergy.fixed_label_level_set_bound` at `ρ = 1/4`.
-/
lemma cold_factor (eps : ℝ) (heps : 0 < eps) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ), |(m : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16 →
        ∀ (n : ℕ),
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤ Real.exp (eps * ((n : ℝ) + 1)) := by
  obtain ⟨ X0, hX0, hF ⟩ := LocalEnergy.fixed_label_level_set_bound eps ( 1 / 4 ) heps ( by norm_num ) ( by norm_num );
  refine' ⟨ ⌈X0⌉₊ + 1, by positivity, fun BS k hk1 hk2 hk3 m hm n ↦ _ ⟩;
  convert hF ( 2 ^ k ) _ ( BS.P k ) _ _ m _ ( n + 1 ) _ using 1 <;> norm_num;
  · linarith [ Nat.le_ceil X0 ];
  · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
  · convert BS.hdensity k hk1 hk2 |> le_trans _ using 1 ; ring_nf;
    norm_num [ Real.log_pow ] ; ring_nf ; norm_num;
  · convert hm using 1

/-
Block-`σ` lower control: `1/sigmaP (BS.P k) ≤ 16·2^k·log(2^k)`, from the
    block-density `card ≥ 2^k/(2 log 2^k)` and `sigmaP_lower`.
-/
lemma inv_sigmaP_bound (BS : BlockSystem) (k : ℕ) (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K) :
    1 / sigmaP (BS.P k) ≤ 16 * (2:ℝ) ^ k * Real.log (2 ^ k) := by
  by_cases hN : 2 ≤ (BS.P k).card;
  · have h_sigmaP_lower : (BS.P k).card / (8 * (2 ^ k : ℝ) ^ 2) ≤ sigmaP (BS.P k) := by
      convert LocalEnergy.block_deviation_lower_bound ( 2 ^ k ) ( one_le_pow₀ ( by norm_num ) ) ( BS.P k ) _ _ using 1 <;> norm_num;
      · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
      · linarith;
    have h_density : (BS.P k).card ≥ (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) := by
      convert BS.hdensity k hk1 hk2 using 1;
    rw [ div_le_iff₀ ] at * <;> norm_num at *;
    · rw [ div_le_iff₀ ] at h_density <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ k by positivity, show ( 0 : ℝ ) < k * Real.log 2 by exact mul_pos ( Nat.cast_pos.mpr <| by linarith [ BS.hk0 ] ) <| Real.log_pos <| by norm_num ];
    · exact lt_of_lt_of_le ( by positivity ) h_sigmaP_lower;
  · interval_cases _ : Finset.card ( BS.P k ) <;> simp_all +decide;
    · have := BS.hdensity k hk1 hk2; norm_num [ ‹BS.P k = ∅› ] at this;
      exact absurd this ( not_le_of_gt ( div_pos ( by positivity ) ( mul_pos zero_lt_two ( mul_pos ( Nat.cast_pos.mpr ( by linarith [ BS.hk0 ] ) ) ( Real.log_pos one_lt_two ) ) ) ) );
    · have := BS.hdensity k hk1 hk2;
      rw [ div_le_iff₀ ] at this <;> norm_num [ Real.log_pow ] at *;
      · rcases k with ( _ | _ | k ) <;> norm_num at *;
        · norm_num [ ‹#(BS.P 1) = 1› ] at this ; linarith [ Real.log_lt_sub_one_of_pos zero_lt_two ( by norm_num ) ];
        · norm_num [ ‹#(BS.P (k + 1 + 1)) = 1› ] at this;
          exact absurd this ( by { exact not_le_of_gt ( by { exact Nat.recOn k ( by norm_num; have := Real.log_two_lt_d9; norm_num1 at *; linarith ) fun n ihn => by norm_num [ pow_succ' ] at * ; nlinarith [ Real.log_nonneg one_le_two ] } ) } );
      · exact mul_pos ( Nat.cast_pos.mpr ( by linarith [ BS.hk0 ] ) ) ( Real.log_pos ( by norm_num ) )

/-
Analytic threshold for the hot-block absorption (helper for `hot_factor`).
    For `X` large the energy floor `c2·X/log³X` dominates the logarithmic
    polynomial factor coming from `unified_levelset`.
-/
lemma hot_threshold (eps c2 C0 : ℝ) (heps : 0 < eps) (hc2 : 0 < c2) :
    ∃ X0 : ℕ, 2 ≤ X0 ∧ ∀ X : ℕ, X0 ≤ X →
      eps * c2 * X / (Real.log X) ^ 3 ≥
        2 * (Real.log C0 + Real.log 34 + Real.log X + Real.log (Real.log X) + 1) ∧
      eps * (c2 * X / (Real.log X) ^ 3) ≥ Real.log (c2 * X / (Real.log X) ^ 3) := by
  obtain ⟨X0₁, hX0₁⟩ : ∃ X0₁ : ℕ, 2 ≤ X0₁ ∧ ∀ X : ℕ, X0₁ ≤ X → eps * c2 * (X : ℝ) / (Real.log X) ^ 3 ≥ 2 * (Real.log C0 + Real.log 34 + Real.log X + Real.log (Real.log X) + 1) := by
    have h_lim : Filter.Tendsto (fun X : ℝ => (Real.log C0 + Real.log 34 + Real.log X + Real.log (Real.log X) + 1) * (Real.log X) ^ 3 / X) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $\frac{\log^k X}{X}$ tends to $0$ as $X$ tends to infinity for any $k$.
      have h_log_pow : ∀ k : ℕ, Filter.Tendsto (fun X : ℝ => (Real.log X) ^ k / X) Filter.atTop (nhds 0) := by
        intro k
        have h_log_pow_div_X_zero : Filter.Tendsto (fun X : ℝ => (Real.log X)^k / X) Filter.atTop (nhds 0) := by
          have h_log_pow_div_X_zero : Filter.Tendsto (fun X : ℝ => X^k / Real.exp X) Filter.atTop (nhds 0) := by
            simpa only [div_eq_mul_inv, Real.exp_neg] using
              Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
          have := h_log_pow_div_X_zero.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] )
        exact h_log_pow_div_X_zero;
      -- We'll use the fact that $\frac{\log(\log X)}{X}$ tends to $0$ as $X$ tends to infinity.
      have h_log_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) * (Real.log X) ^ 3 / X) Filter.atTop (nhds 0) := by
        -- We can use the fact that $\frac{\log(\log X)}{\log X}$ tends to $0$ as $X$ tends to infinity.
        have h_log_log_div_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X) Filter.atTop (nhds 0) := by
          have := h_log_pow 1;
          exact this.comp ( Real.tendsto_log_atTop ) |> fun h => h.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by simp +decide [div_eq_mul_inv] );
        convert h_log_log_div_log.mul ( h_log_pow 4 ) using 2 <;> ring_nf;
        grind;
      convert Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( h_log_pow 3 |> Filter.Tendsto.const_mul ( Real.log C0 ) ) ( h_log_pow 3 |> Filter.Tendsto.const_mul ( Real.log 34 ) ) ) ( h_log_pow 4 ) ) h_log_log ) ( h_log_pow 3 ) using 2 <;> ring;
    obtain ⟨ X0₁, hX0₁ ⟩ := Metric.tendsto_atTop.mp h_lim ( eps * c2 / 2 ) ( by positivity );
    refine' ⟨ ⌈X0₁⌉₊ + 2, _, _ ⟩ <;> norm_num;
    intro X hX; specialize hX0₁ X ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ dist_eq_norm ] at hX0₁ ; rw [ Real.norm_eq_abs ] at hX0₁ ; rw [ abs_lt ] at hX0₁ ; rw [ le_div_iff₀ ( pow_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) _ ) ] ; nlinarith [ show ( X : ℝ ) ≥ ⌈X0₁⌉₊ + 2 by exact_mod_cast hX, Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith, pow_pos ( Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith ) 3, mul_div_cancel₀ ( ( Real.log C0 + Real.log 34 + Real.log X + Real.log ( Real.log X ) + 1 ) * Real.log X ^ 3 ) ( show ( X : ℝ ) ≠ 0 by norm_cast; linarith ) ] ;
  -- Show that `eps * (c2 * X / (Real.log X) ^ 3) ≥ Real.log (c2 * X / (Real.log X) ^ 3)` for large X.
  have h_log : Filter.Tendsto (fun X : ℝ => Real.log (c2 * X / (Real.log X) ^ 3) / (c2 * X / (Real.log X) ^ 3)) Filter.atTop (nhds 0) := by
    have h_log : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{t}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
      suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun t => 1 / t) Filter.atTop) (nhds 0) by
        exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    refine h_log.comp ?_;
    -- We can use the change of variables $u = \log X$ to transform the limit expression.
    suffices h_log : Filter.Tendsto (fun u : ℝ => c2 * Real.exp u / u ^ 3) Filter.atTop Filter.atTop by
      have := h_log.comp Real.tendsto_log_atTop;
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
    simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hc2 ( Real.tendsto_exp_div_pow_atTop 3 );
  -- By the definition of limit, there exists an $X0₂$ such that for all $X \geq X0₂$, $\frac{\log(c2 * X / (\log X)^3)}{c2 * X / (\log X)^3} < \epsilon$.
  obtain ⟨X0₂, hX0₂⟩ : ∃ X0₂ : ℕ, ∀ X : ℕ, X0₂ ≤ X → Real.log (c2 * X / (Real.log X) ^ 3) / (c2 * X / (Real.log X) ^ 3) < eps := by
    exact Filter.eventually_atTop.mp ( h_log.eventually ( gt_mem_nhds heps ) ) |> fun ⟨ X0₂, hX0₂ ⟩ => ⟨ ⌈X0₂⌉₊, fun X hX => hX0₂ X <| Nat.le_of_ceil_le hX ⟩;
  refine' ⟨ X0₁ + X0₂ + 2, _, _ ⟩ <;> norm_num at *;
  intro X hX; specialize hX0₂ X ( by linarith ) ; rw [ div_lt_iff₀ ( div_pos ( mul_pos hc2 ( Nat.cast_pos.mpr ( by linarith ) ) ) ( pow_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) 3 ) ) ] at hX0₂; exact ⟨ hX0₁.2 X ( by linarith ), by linarith ⟩ ;

/-- Helper: monotone log bound.  If `1/eps ≤ t0`, `log t0 ≤ eps·t0`, and
    `t0 ≤ t`, then `log t ≤ eps·t`.  (The map `u ↦ eps·u − log u` is
    nondecreasing on `[1/eps,∞)`.) -/
lemma log_le_eps_mul (eps t0 t : ℝ) (heps : 0 < eps) (ht0pos : 0 < t0)
    (ht0 : 1 / eps ≤ t0) (hlog : Real.log t0 ≤ eps * t0) (ht : t0 ≤ t) :
    Real.log t ≤ eps * t := by
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  have hdiv : Real.log (t / t0) ≤ t / t0 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log t = Real.log t0 + Real.log (t / t0) := by
    rw [Real.log_div (ne_of_gt htpos) (ne_of_gt ht0pos)]; ring
  have hepst0 : 1 ≤ eps * t0 := by
    rw [div_le_iff₀ heps] at ht0; linarith
  -- (t - t0)·(eps - 1/t0) ≥ 0
  have hkey : (t - t0) * (eps - 1 / t0) ≥ 0 := by
    apply mul_nonneg (by linarith)
    have : 1 / t0 ≤ eps := by
      rw [div_le_iff₀ ht0pos]; nlinarith
    linarith
  have hexpand : (t - t0) * (eps - 1 / t0) = eps * t - eps * t0 - (t / t0 - 1) := by
    field_simp
  rw [hsplit]
  nlinarith [hdiv, hlog, hkey, hexpand]

/-
Helper: `Rw c2 k → ∞`, so for `X = 2^k` large, `1/eps ≤ Rw c2 k`.
-/
lemma Rw_large (eps c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ (k : ℕ), 1 ≤ k → X0 ≤ (2:ℝ) ^ k → 1 / eps ≤ Rw c2 k := by
  -- Apply the fact that $Rw c2 k$ tends to infinity as $k$ increases.
  have h_Rw_inf : Filter.Tendsto (fun k : ℕ => Rw c2 k) Filter.atTop Filter.atTop := by
    have h_lim : Filter.Tendsto (fun X : ℝ => c2 * X / (Real.log X) ^ 3) Filter.atTop Filter.atTop := by
      have h_lim : Filter.Tendsto (fun u : ℝ => c2 * Real.exp u / u ^ 3) Filter.atTop Filter.atTop := by
        simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hc2 ( Real.tendsto_exp_div_pow_atTop 3 );
      have := h_lim.comp Real.tendsto_log_atTop;
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
    exact h_lim.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) |> Filter.Tendsto.comp <| Filter.tendsto_id;
  obtain ⟨ k, hk ⟩ := Filter.eventually_atTop.mp ( h_Rw_inf.eventually_ge_atTop ( 1 / eps ) );
  exact ⟨ 2 ^ k, by positivity, fun n hn hn' => hk n <| Nat.le_of_not_lt fun h => by linarith [ pow_lt_pow_right₀ ( by norm_num : ( 1 : ℝ ) < 2 ) h ] ⟩

/-
**Hole 8 (`hot_factor`).**  Per-hot-block count: once the block energy floor
    `Rw c2 k ≤ n+1` holds (hot block), the unconstrained level-set count is
    `≤ exp(2ε(n+1))` — the entropy `unified_levelset` bound `C₀ e^{ε(n+1)}(1+√/σ)`
    has its polynomial factor absorbed by the (large) energy floor.  Valid for
    `k0 ≥` a threshold encoded as `X0 ≤ 2^k`.
-/
lemma hot_factor (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (n : ℕ), Rw c2 k ≤ (n : ℝ) + 1 →
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1)).card : ℝ)
            ≤ Real.exp (2 * eps * ((n : ℝ) + 1)) := by
  obtain ⟨ C0, X1, hC0, hX1, h ⟩ := LocalEnergy.block_level_set_bound eps heps heps1
  obtain ⟨ X0₈, hX0₈ ⟩ := hot_threshold eps c2 C0 heps hc2
  obtain ⟨ X0r, hX0r, hX0r' ⟩ := Rw_large eps c2 hc2
  set X0 := Nat.ceil X1 + X0₈ + X0r + 16 with hX0_def
  use X0
  simp [hX0_def] at *;
  refine' ⟨ by positivity, fun BS k hk1 hk2 hk3 n hn => _ ⟩;
  refine' le_trans _ ( Real.exp_le_exp.mpr <| show 2 * eps * ( n + 1 ) ≥ eps * ( n + 1 ) + Real.log ( C0 * 17 * 2 ^ k * Real.log ( 2 ^ k ) * Real.sqrt ( n + 1 ) ) from _ );
  · -- Apply the `unified_levelset` bound to the block `BS.P k`, the radius `R = n + 1`, and the window and density conditions from `BS`.
    have h_unified : (Finset.filter (fun b : BlockAssignment (BS.P k) => QP (BS.P k) b ≤ (n : ℝ) + 1) (Finset.univ : Finset (BlockAssignment (BS.P k)))).card ≤ C0 * Real.exp (eps * (n + 1)) * (1 + Real.sqrt (n + 1) / sigmaP (BS.P k)) := by
      convert h ( 2 ^ k ) _ ( BS.P k ) _ _ ( n + 1 ) _ using 1 <;> norm_num at *;
      · linarith [ Nat.le_ceil X1, show ( X0₈ : ℝ ) ≥ 2 by norm_cast; linarith, show ( 2 : ℝ ) ^ k ≥ 0 by positivity ];
      · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime k p hp ) ⟩;
      · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
      · convert BS.hdensity k hk1 hk2 using 1;
        norm_num [ Real.log_pow ];
    -- Apply the `inv_sigmaP_bound` to the block `BS.P k`.
    have h_inv_sigmaP : 1 + Real.sqrt (n + 1) / sigmaP (BS.P k) ≤ 17 * 2 ^ k * Real.log (2 ^ k) * Real.sqrt (n + 1) := by
      have h_simplified : 1 / sigmaP (BS.P k) ≤ 16 * (2 : ℝ) ^ k * Real.log (2 ^ k) := by
        exact inv_sigmaP_bound BS k hk1 hk2;
      ring_nf at *;
      nlinarith [ show 1 ≤ Real.sqrt ( 1 + n : ℝ ) by exact Real.le_sqrt_of_sq_le ( by linarith ), show 1 ≤ Real.log ( 2 ^ k ) * 2 ^ k by exact one_le_mul_of_one_le_of_one_le ( Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( 2 : ℝ ) ^ k ≥ 2 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) <| show k ≥ 1 by linarith [ BS.hk0 ] ) ] ) ( one_le_pow₀ <| by norm_num ) ];
    refine' le_trans h_unified ( le_trans ( mul_le_mul_of_nonneg_left h_inv_sigmaP <| by positivity ) _ );
    rw [ Real.exp_add, Real.exp_log ( by exact mul_pos ( mul_pos ( mul_pos ( mul_pos hC0 ( by norm_num ) ) ( by positivity ) ) ( Real.log_pos ( one_lt_pow₀ ( by norm_num ) ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X1 ] ) ] ) ) ) ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) ] ; ring_nf ; norm_num [ Real.exp_pos, hC0, heps ] ;
  · -- Apply the logarithmic bound from `log_le_eps_mul`.
    have h_log_bound : Real.log (C0 * 17 * 2 ^ k * Real.log (2 ^ k)) ≤ (eps / 2) * (n + 1) := by
      have h_log_bound : Real.log C0 + Real.log 17 + Real.log (2 ^ k) + Real.log (Real.log (2 ^ k)) ≤ (eps / 2) * (n + 1) := by
        have := hX0₈.2 ( 2 ^ k ) ( by linarith [ Nat.le_ceil X1, show ( 2 : ℕ ) ^ k ≥ X0₈ by exact_mod_cast ( by linarith [ Nat.le_ceil X1 ] : ( X0₈ : ℝ ) ≤ 2 ^ k ) ] ) ; norm_num at *;
        rw [ show ( 34 : ℝ ) = 2 * 17 by norm_num, Real.log_mul ( by positivity ) ( by positivity ) ] at this;
        unfold Rw at hn; norm_num at hn; ring_nf at *; nlinarith [ Real.log_pos one_lt_two ] ;
      convert h_log_bound using 1 ; rw [ Real.log_mul, Real.log_mul, Real.log_mul ] <;> norm_num <;> try positivity;
      linarith [ BS.hk0 ];
    rw [ Real.log_mul ( by exact ne_of_gt <| mul_pos ( mul_pos ( mul_pos hC0 <| by norm_num ) <| by positivity ) <| Real.log_pos <| one_lt_pow₀ one_lt_two <| by linarith [ show k > 0 from Nat.pos_of_ne_zero <| by rintro rfl; linarith [ Nat.le_ceil X1 ] ] ) <| by positivity, Real.log_sqrt <| by positivity ];
    have h_log_bound : Real.log (n + 1) ≤ eps * (n + 1) := by
      apply log_le_eps_mul eps (Rw c2 k) (n + 1) heps (by
      exact div_pos ( mul_pos hc2 ( pow_pos ( by norm_num ) _ ) ) ( pow_pos ( Real.log_pos ( one_lt_pow₀ ( by norm_num ) ( by linarith [ show k > 0 from Nat.pos_of_ne_zero <| by rintro rfl; linarith [ Nat.le_ceil X1 ] ] ) ) ) _ )) (by
      exact hX0r' k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero <| by rintro rfl; linarith [ Nat.le_ceil X1 ] ] ) ( by linarith [ Nat.le_ceil X1 ] ) |> le_trans ( by norm_num )) (by
      convert hX0₈.2 ( 2 ^ k ) ( by linarith [ Nat.le_ceil X1, show ( 2 : ℕ ) ^ k ≥ X0₈ by exact_mod_cast ( by linarith : ( X0₈ : ℝ ) ≤ 2 ^ k ) ] ) |>.2 using 1; all_goals norm_num [ Rw ]) (by
      exact hn);
    linarith

end GlobalControl

end
