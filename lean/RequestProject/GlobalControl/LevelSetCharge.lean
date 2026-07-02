import RequestProject.GlobalControl.BoundaryPenalty
import RequestProject.GlobalControl.LevelSetFiberBound
import RequestProject.GlobalControl.LevelSetLabelCharge
import RequestProject.GlobalControl.ScaleComparison

/-!
# Level-set charge aggregation

Positivity and partition-function estimates aggregating hot, boundary, shell,
and label charges.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-
**Control deviation positivity.**  When `BS.k0 ≥ 2` the block `P_{k0}` has
    at least two primes (block density), so the internal control pairs of the
    `k0` block are nonempty and `sigmaCtrl BS > 0`.
-/
lemma sigmaCtrl_pos_of_k0 (BS : BlockSystem) (hk0 : 2 ≤ BS.k0) : 0 < sigmaCtrl BS := by
  refine' Real.sqrt_pos.mpr _;
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℕ, p ∈ BS.P BS.k0 ∧ q ∈ BS.P BS.k0 ∧ p < q := by
    have h_card : 2 ≤ (BS.P BS.k0).card := by
      have := BS.hdensity BS.k0 ( by norm_num ) ( by linarith [ BS.hk ] );
      rw [ div_le_iff₀ ] at this <;> norm_num at *;
      · contrapose! this;
        interval_cases _ : Finset.card ( BS.P BS.k0 ) <;> norm_num at *;
        rcases n : BS.k0 with ( _ | _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
        · exact Real.log_two_lt_d9.trans_le ( by norm_num );
        · exact Nat.recOn k ( by norm_num; have := Real.log_two_lt_d9; norm_num1 at *; linarith ) fun n ihn => by norm_num [ pow_succ' ] at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two ] ;
      · positivity;
    obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.mp h_card; cases lt_trichotomy p q <;> aesop;
  refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => by positivity ) ( show ( p, q ) ∈ ctrlPairs BS from _ ) ) <;> norm_num [ hpq ];
  · exact sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by have := BS.hprime BS.k0; aesop ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by have := BS.hprime BS.k0; aesop ) ) ) );
  · exact Finset.mem_union_left _ ( Finset.mem_biUnion.mpr ⟨ BS.k0, Finset.mem_Icc.mpr ⟨ le_rfl, by linarith [ BS.hk ] ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ hpq.1, hpq.2.1 ⟩, hpq.2.2 ⟩ ⟩ )

/-
**Boundary floor lower bound.**  Past a uniform threshold, the boundary
    Peierls floor `Pifloor BS e0 (s-1)` dominates `2^{s-1}/log(2^{s-1})^3`
    (the `Rw`-shaped quantity).  Uses the block density `N_k ≥ 2^k/(2 log 2^k)`:
    `Pifloor ≈ N_s·N_{s-1}^3/(2^13·2^{2(s-1)}) ≈ 2^{2s}/poly`, with the extra
    `~2^s/log` factor overtaking any fixed multiple of `2^{s-1}/log^3`.
-/
lemma Pifloor_charge_lower (e0 : ℝ) (he0 : 0 < e0) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem) (s : ℕ), k0min ≤ s →
      BS.k0 + 1 ≤ s → s ≤ BS.K →
      (2:ℝ) ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3 ≤ Pifloor BS e0 (s - 1) := by
  have h_tendsto : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (n - 1) / (Real.log (2 ^ (n - 1))) ^ 3) Filter.atTop Filter.atTop := by
    -- We can use the fact that $2^{n-1} / (\log(2^{n-1}))^3$ grows exponentially faster than any polynomial function.
    have h_exp_growth : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n / (n * Real.log 2) ^ 3) Filter.atTop Filter.atTop := by
      -- We can factor out $2^n$ and use the fact that $\frac{1}{n^3}$ tends to $0$ as $n$ tends to infinity.
      suffices h_factor : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n / n ^ 3) Filter.atTop Filter.atTop by
        convert h_factor.const_mul_atTop ( show 0 < ( Real.log 2 ) ⁻¹ ^ 3 by positivity ) using 2 ; ring;
      -- We can convert this limit into a form that is easier to handle by substituting $m = n \log 2$.
      suffices h_log : Filter.Tendsto (fun m : ℝ => Real.exp m / (m / Real.log 2) ^ 3) Filter.atTop Filter.atTop by
        convert h_log.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos one_lt_two ) ) using 2 ; norm_num [ Real.exp_nat_mul, Real.exp_log ];
      ring_nf;
      exact Filter.Tendsto.atTop_mul_const ( by positivity )
        (by simpa only [div_eq_mul_inv, inv_pow] using Real.tendsto_exp_div_pow_atTop 3);
    convert h_exp_growth.comp ( Filter.tendsto_sub_atTop_nat 1 ) using 2 ; norm_num [ Real.log_pow ];
  obtain ⟨k0min, hk0min⟩ : ∃ k0min : ℕ, ∀ s ≥ k0min, (2 : ℝ) ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3 ≤ (2 ^ s / (4 * Real.log (2 ^ s))) * (2 ^ (s - 1) / (4 * Real.log (2 ^ (s - 1)))) ^ 3 / (2 ^ 13 * (2 ^ (s - 1)) ^ 2) := by
    have h_tendsto : Filter.Tendsto (fun n : ℕ => (2 ^ n / (4 * Real.log (2 ^ n))) * (2 ^ (n - 1) / (4 * Real.log (2 ^ (n - 1)))) ^ 3 / (2 ^ 13 * (2 ^ (n - 1)) ^ 2) / (2 ^ (n - 1) / (Real.log (2 ^ (n - 1))) ^ 3)) Filter.atTop Filter.atTop := by
      -- Simplify the expression inside the limit.
      suffices h_simplify : Filter.Tendsto (fun n : ℕ => (2 ^ n / (4 * n * Real.log 2)) * (2 ^ (3 * (n - 1)) / (64 * (n - 1) ^ 3 * (Real.log 2) ^ 3)) / (2 ^ 13 * 2 ^ (2 * (n - 1))) / (2 ^ (n - 1) / ((n - 1) ^ 3 * (Real.log 2) ^ 3))) Filter.atTop Filter.atTop by
        convert h_simplify using 2 ; norm_num [ Real.log_pow ] ; ring_nf;
        cases ‹ℕ› <;> norm_num ; ring;
      -- Simplify the expression inside the limit further.
      suffices h_simplify' : Filter.Tendsto (fun n : ℕ => (2 ^ n * 2 ^ (3 * (n - 1))) / (4 * n * 64 * 2 ^ 13 * 2 ^ (2 * (n - 1)) * 2 ^ (n - 1)) * (1 / (Real.log 2))) Filter.atTop Filter.atTop by
        refine h_simplify'.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
        field_simp;
        rw [ div_self ( sub_ne_zero_of_ne ( by norm_cast; linarith ) ) ];
      -- Simplify the expression inside the limit further by cancelling out common terms.
      suffices h_simplify'' : Filter.Tendsto (fun n : ℕ => (2 ^ (n + 3 * (n - 1) - 2 * (n - 1) - (n - 1))) / (4 * n * 64 * 2 ^ 13) * (1 / Real.log 2)) Filter.atTop Filter.atTop by
        refine h_simplify''.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
        rw [ show n + 3 * ( n - 1 ) - 2 * ( n - 1 ) - ( n - 1 ) = n by omega ] ; ring_nf;
        norm_num [ mul_assoc, mul_comm, mul_left_comm, ← mul_pow ];
        norm_num [ ← mul_assoc, ← mul_pow ];
      -- Simplify the exponent in the numerator.
      suffices h_exp : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℝ) / (4 * n * 64 * 2 ^ 13) * (1 / Real.log 2)) Filter.atTop Filter.atTop by
        refine h_exp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ show n + 3 * ( n - 1 ) - 2 * ( n - 1 ) - ( n - 1 ) = n by omega ] );
      -- We can factor out the constant $1 / (4 * 64 * 2 ^ 13 * \log 2)$ from the limit.
      suffices h_factor : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℝ) / n) Filter.atTop Filter.atTop by
        convert h_factor.const_mul_atTop ( show 0 < ( 1 / ( 4 * 64 * 2 ^ 13 * Real.log 2 ) ) by positivity ) using 2 ; ring;
      have h_exp_growth : Filter.Tendsto (fun n : ℕ => (Real.exp (n * Real.log 2)) / (n : ℝ)) Filter.atTop Filter.atTop := by
        have := Real.tendsto_exp_div_pow_atTop 1;
        have := this.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos one_lt_two ) );
        convert this.const_mul_atTop ( show 0 < Real.log 2 by positivity ) using 2 ; norm_num ; ring_nf;
        norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      simpa [ Real.exp_nat_mul, Real.exp_log ] using h_exp_growth;
    have := h_tendsto.eventually_gt_atTop 1;
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ k0min, hk0min ⟩ ; exact ⟨ k0min + 2, fun s hs => by have := hk0min s ( by linarith ) ; rw [ lt_div_iff₀ ( by exact div_pos ( pow_pos ( by positivity ) _ ) ( pow_pos ( Real.log_pos ( one_lt_pow₀ ( by norm_num ) ( by omega ) ) ) _ ) ) ] at this; linarith ⟩ ;
  obtain ⟨k0min', hk0min'⟩ : ∃ k0min' : ℕ, ∀ s ≥ k0min', ∀ BS : BlockSystem, s ∈ Finset.Icc BS.k0 BS.K → (2 : ℝ) ^ s / (2 * Real.log (2 ^ s)) ≥ 2 * e0 + 2 ∧ (2 : ℝ) ^ (s - 1) / (2 * Real.log (2 ^ (s - 1))) ≥ 2 * e0 + 2 := by
    have h_tendsto : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n / (2 * Real.log (2 ^ n))) Filter.atTop Filter.atTop := by
      norm_num [ Real.log_pow ];
      -- We can factor out the constant $1/(2 \log 2)$ and use the fact that $2^n / n$ tends to infinity.
      have h_factor : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n / n) Filter.atTop Filter.atTop := by
        have h_exp_growth : Filter.Tendsto (fun n : ℕ => (Real.exp (n * Real.log 2)) / n) Filter.atTop Filter.atTop := by
          have := Real.tendsto_exp_div_pow_atTop 1;
          have := this.comp ( tendsto_natCast_atTop_atTop.atTop_mul_const ( Real.log_pos one_lt_two ) );
          convert this.const_mul_atTop ( show 0 < Real.log 2 by positivity ) using 2 ; norm_num ; ring_nf;
          norm_num [ mul_assoc, mul_comm, mul_left_comm ];
        simpa [ Real.exp_nat_mul, Real.exp_log ] using h_exp_growth;
      convert h_factor.const_mul_atTop ( show 0 < ( 1 / ( 2 * Real.log 2 ) ) by positivity ) using 2 ; ring;
    exact Filter.eventually_atTop.mp ( h_tendsto.eventually_ge_atTop ( 2 * e0 + 2 ) ) |> fun ⟨ k0min', hk0min' ⟩ ↦ ⟨ k0min' + 1, fun s hs BS hBS ↦ ⟨ hk0min' s ( by linarith ), hk0min' ( s - 1 ) ( Nat.le_sub_one_of_lt ( by linarith ) ) ⟩ ⟩;
  use k0min' + k0min + 1;
  intros BS s hs hs' hs''; specialize hk0min s ( by linarith ) ; specialize hk0min' s ( by linarith ) BS ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ; simp_all +decide [ Pifloor ] ;
  refine le_trans hk0min ?_;
  gcongr;
  · have := BS.hdensity ( s - 1 + 1 ) ( by omega ) ( by omega ) ; simp_all +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ s ) ] ;
    grind;
  · rw [ Nat.sub_add_cancel ( by linarith ) ];
    have := BS.hdensity s ( by linarith ) ( by linarith );
    norm_num [ Real.log_pow ] at * ; ring_nf at * ; linarith;
  · have := BS.hdensity ( s - 1 ) ( by omega ) ( by omega ) ; simp_all +decide;
    ring_nf at *; linarith;

/-
For a segment start `s` past a uniform threshold,
    the label-window size `2·labelBound c2 s + 1` is dominated by the boundary
    Peierls floor `Pifloor BS e0 (s-1)` of the predecessor boundary block `s-1`.
    Companion to `labelBound_charge_hot`, combining `Pifloor_charge_lower` with
    `pow_beats_poly_log` exactly as in `labelBound_charge_hot`.
-/
lemma labelBound_charge_boundary (c2 e0 eps : ℝ)
    (heps : 0 < eps) (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem) (s : ℕ), k0min ≤ s →
      BS.k0 + 1 ≤ s → s ≤ BS.K →
      (2 * (labelBound c2 s : ℝ) + 1) ≤ Real.exp (eps * Pifloor BS e0 (s - 1)) := by
  -- Establish the elementary-growth and exponential-growth thresholds.
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ s : ℕ, N1 ≤ s →
    (640 / 3) * Real.sqrt (c2 * (2:ℝ) ^ s) * ((2:ℝ) ^ s * Real.log (2 ^ s)) + 3 ≤
      Real.exp (Real.log ((640 / 3) * Real.sqrt (c2 * (2:ℝ) ^ s) * ((2:ℝ) ^ s * Real.log (2 ^ s))) + 1) := by
        have hN1 : ∃ N1 : ℕ, ∀ s : ℕ, N1 ≤ s →
          (640 / 3) * Real.sqrt (c2 * (2:ℝ) ^ s) * ((2:ℝ) ^ s * Real.log (2 ^ s)) ≥ 3 := by
            have hN1 : Filter.Tendsto (fun s : ℕ => (640 / 3) * Real.sqrt (c2 * (2:ℝ) ^ s) * ((2:ℝ) ^ s * Real.log (2 ^ s))) Filter.atTop Filter.atTop := by
              norm_num [ Real.log_rpow ];
              refine' Filter.Tendsto.atTop_mul_atTop₀ _ _;
              · exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( Filter.Tendsto.const_mul_atTop ( by positivity ) ( by
                  have ht := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / 2)).comp
                    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
                  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using ht ) );
              · exact Filter.Tendsto.atTop_mul_atTop₀ ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ( Filter.Tendsto.atTop_mul_const ( by positivity ) tendsto_natCast_atTop_atTop );
            exact Filter.eventually_atTop.mp ( hN1.eventually_ge_atTop 3 );
        obtain ⟨ N1, hN1 ⟩ := hN1; use N1; intro s hs; rw [ Real.exp_add, Real.exp_log ( by linarith [ hN1 s hs ] ) ] ; nlinarith [ hN1 s hs, Real.add_one_le_exp 1 ] ;
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ s : ℕ, N2 ≤ s →
    Real.log ((640 / 3) * Real.sqrt (c2 * (2:ℝ) ^ s) * ((2:ℝ) ^ s * Real.log (2 ^ s))) + 1 ≤
      eps * (2:ℝ) ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3 := by
        obtain ⟨ N2, hN2 ⟩ := pow_beats_poly_log ( Real.log ( 640 / 3 * Real.sqrt c2 ) + 2 ) ( eps ) ( by positivity );
        use N2 + 4; intros s hs; specialize hN2 s ( by linarith ) ; simp_all +decide [ Real.log_mul, ne_of_gt ] ;
        rw [ Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_sqrt, Real.log_sqrt ] <;> try positivity;
        · rw [ Real.log_sqrt ( by positivity ) ] at hN2 ; norm_num [ Real.log_pow ] at * ; linarith;
        · exact ne_of_gt ( mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos ( by norm_num ) ) );
        · exact ne_of_gt ( mul_pos ( pow_pos ( by norm_num ) _ ) ( mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.log_pos ( by norm_num ) ) ) );
  obtain ⟨kP, hkP⟩ := Pifloor_charge_lower e0 he0;
  refine' ⟨ Max.max N1 ( Max.max N2 ( Max.max kP 4 ) ), fun BS s hs hs' hs'' => _ ⟩ ; simp_all +decide [ labelBound ];
  refine' le_trans _ ( Real.exp_le_exp.mpr ( le_trans _ ( mul_le_mul_of_nonneg_left ( hkP BS s hs.2.2.1 hs' hs'' ) heps.le ) ) );
  convert hN1 s hs.1 |> le_trans _ using 1;
  · linarith [ Int.ceil_lt_add_one ( 20 / 3 * ( Real.sqrt c2 * Real.sqrt ( 2 ^ s ) ) * ( 16 * 2 ^ s * ( s * Real.log 2 ) ) ) ];
  · simpa only [mul_div_assoc] using hN2 s hs.2.1

/-
Boundary penalty floor is nonnegative for interior blocks past a threshold
    (block densities exceed `e0`).
-/
lemma Pifloor_nonneg (e0 : ℝ) (_he0 : 0 < e0) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem) (j : ℕ), k0min ≤ j → BS.k0 ≤ j → j < BS.K →
      0 ≤ Pifloor BS e0 j := by
  -- Choose `k0min` so that for `j ≥ k0min`, the densities force both parts to be nonnegative.
  have h_tendsto : Filter.Tendsto (fun k : ℕ => (2 ^ k : ℝ) / (2 * Real.log (2 ^ k))) Filter.atTop Filter.atTop := by
    norm_num [ Real.log_rpow ];
    -- We can use the fact that $2^k / k$ grows exponentially faster than $k$.
    have h_exp_growth : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / k) Filter.atTop Filter.atTop := by
      refine' Filter.tendsto_atTop_mono' _ _ tendsto_natCast_atTop_atTop;
      filter_upwards [ Filter.eventually_gt_atTop 4 ] with k hk using by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; induction hk <;> norm_num [ Nat.pow_succ ] at * ; nlinarith;
    convert h_exp_growth.const_mul_atTop ( show 0 < ( 1 / ( 2 * Real.log 2 ) ) by positivity ) using 2 ; ring;
  obtain ⟨ k0min, hk0min ⟩ := Filter.eventually_atTop.mp ( h_tendsto.eventually ( Filter.eventually_ge_atTop ( e0 + 2 ) ) );
  refine' ⟨ k0min, fun BS j hj hj' hj'' => _ ⟩;
  refine' div_nonneg _ _ <;> norm_num;
  refine' mul_nonneg _ ( pow_nonneg _ _ );
  · have := hk0min ( j + 1 ) ( by linarith );
    have := BS.hdensity ( j + 1 ) ( by linarith ) ( by linarith ) ; norm_num at * ; linarith;
  · have := BS.hdensity j hj' ( by linarith );
    linarith [ hk0min j hj ]

/-
Charge sum over admissible hot sets: `∑_H ∏_{j∈H} exp(ε·Rw j) ≤ exp(2εR)·exp(nB)`.
    `admH` is exactly the `Icc`-powerset filtered by `∑ Rw ≤ R`, so this is a
    direct instance of `sum_subset_charge_le` (with `Rw ≥ 0`).
-/
lemma chargeH_le (eps c2 R : ℝ) (heps : 0 < eps) (hc2 : 0 < c2) (BS : BlockSystem) :
    (∑ H ∈ admH BS c2 R, ∏ j ∈ H, Real.exp (eps * Rw c2 j))
      ≤ Real.exp (2 * eps * R) * Real.exp (numBlocks BS) := by
  simpa only [admH] using
    sum_subset_charge_le BS (fun j => Rw c2 j) R eps heps
      (fun j _ => div_nonneg (mul_nonneg hc2.le (pow_nonneg zero_le_two _))
        (pow_nonneg (Real.log_nonneg (one_le_pow₀ one_le_two)) _))

/-
Charge sum over admissible boundary sets: `∑_B ∏_{j∈B} exp(ε·Pifloor j) ≤
    exp(2εR)·exp(nB)`.  `admB` ranges over `Ico`-powersets, so we apply
    `sum_subset_charge_le` to the truncated weight `(if j < K then Pifloor j else 0)`
    (nonnegative on `Icc` by `Pifloor_nonneg`), using `admB ⊆` the `Icc` filter.
-/
lemma chargeB_le (eps e0 : ℝ) (heps : 0 < eps) (he0 : 0 < e0) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem), k0min ≤ BS.k0 → ∀ R : ℝ,
      (∑ B ∈ admB BS e0 R, ∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j))
        ≤ Real.exp (2 * eps * R) * Real.exp (numBlocks BS) := by
  -- Apply `Pifloor_nonneg` to find `kP` such that for all `j ≥ kP`, `Pifloor BS e0 j ≥ 0`.
  obtain ⟨kP, hkP⟩ : ∃ kP : ℕ, ∀ (BS : BlockSystem) (j : ℕ), kP ≤ j → BS.k0 ≤ j → j < BS.K → 0 ≤ Pifloor BS e0 j :=
    Pifloor_nonneg e0 he0
  use kP; intros BS hBS R; simp_all +decide [ admB ] ;
  refine' le_trans _ ( GlobalControl.sum_subset_charge_le BS ( fun j => if j < BS.K then Pifloor BS e0 j else 0 ) R eps heps _ );
  · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
    rotate_left;
    exact Finset.image ( fun B => B ) ( Finset.filter ( fun B => ∑ j ∈ B, Pifloor BS e0 j ≤ R ) ( Finset.powerset ( Finset.Ico BS.k0 BS.K ) ) );
    · simp +contextual [ Finset.subset_iff ];
      exact fun x hx₁ hx₂ y hy => le_of_lt ( hx₁ hy |>.2 );
    · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => Real.exp_nonneg _;
    · simp +zetaDelta at *;
      exact Finset.sum_le_sum fun x hx => Finset.prod_le_prod ( fun _ _ => Real.exp_nonneg _ ) fun y hy => by rw [ if_pos ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hx |>.1 ) hy ) ] ) ] ;
  · grind

/-
The initial label window cardinality is bounded by `3 + 14·√R/σ_{k0}`.
    `labelFin` at `k0` is `Icc (-(L0)) (L0)` with `L0 = ⌈7√R/σ_{k0}⌉ ≥ 0`, so its
    card is `2·L0 + 1 ≤ 2(7√R/σ_{k0} + 1) + 1`.
-/
lemma labelFin_k0_card_le (BS : BlockSystem) (c2 R : ℝ) (_hR0 : 0 ≤ R) :
    ((labelFin BS c2 R BS.k0).card : ℝ) ≤ 3 + 14 * Real.sqrt R / sigmaP (BS.P BS.k0) := by
  -- Let `σ := sigmaP (BS.P BS.k0) ≥ 0` and `x := 7 * Real.sqrt R / σ ≥ 0`.
  set σ := sigmaP (BS.P BS.k0)
  have hσ0 : 0 ≤ σ := sigmaP_nonneg _
  set x := 7 * Real.sqrt R / σ
  have hx0 : 0 ≤ x := by
    positivity;
  --Card of an integer `Finset.Icc a b` is `(b - a + 1).toNat`; here `Finset.Icc (-(L0)) (L0)` has card `(L0 - (-(L0)) + 1).toNat = (2*L0 + 1).toNat`.
  have hlabels_card : ((labelFin BS c2 R BS.k0).card : ℝ) = 2 * Int.ceil x + 1 := by
    unfold labelFin; norm_num;
    rw [ show L0 BS R = ⌈x⌉ from rfl ] ; ring_nf;
    norm_cast;
    rw [ Int.toNat_of_nonneg ( by positivity ) ];
  convert hlabels_card.le.trans _ using 1 ; ring_nf;
  convert add_le_add_left ( mul_le_mul_of_nonneg_right ( Int.ceil_lt_add_one x |> le_of_lt ) zero_le_two ) 1 using 1 ; ring;
  ring!

/-
The per-segment-start label charge (`hcharge` for `label_product_le`):
    every non-initial window `|labelFin s|` is bounded by the predecessor's
    Peierls charge, via `labelBound_charge_hot` / `labelBound_charge_boundary`.
-/
lemma hcharge_le (eps c2 e0 : ℝ) (heps : 0 < eps) (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem), k0min ≤ BS.k0 → ∀ (R : ℝ) (H B : Finset ℕ),
      ∀ s ∈ RequestProject.segmentStarts BS.k0 BS.K H B, s ≠ BS.k0 →
        ((labelFin BS c2 R s).card : ℝ) ≤
          (if s - 1 ∈ H then Real.exp (eps * Rw c2 (s - 1))
           else Real.exp (eps * Pifloor BS e0 (s - 1))) := by
  obtain ⟨k1, hk1⟩ := GlobalControl.labelBound_charge_hot c2 eps heps hc2
  obtain ⟨k2, hk2⟩ := GlobalControl.labelBound_charge_boundary c2 e0 eps heps hc2 he0
  use max k1 k2;
  intros BS hBS R H B s hs hs_ne_K0
  have hs_bounds : BS.k0 ≤ s ∧ s ≤ BS.K := segStarts_le BS H B hs
  have hs_gt_k0 : BS.k0 + 1 ≤ s := by
    exact Nat.succ_le_of_lt ( lt_of_le_of_ne hs_bounds.1 hs_ne_K0.symm )
  have hs_card : ((labelFin BS c2 R s).card : ℝ) = 2 * (labelBound c2 s : ℝ) + 1 := by
    unfold labelFin; simp +decide [ hs_ne_K0 ] ;
    rw_mod_cast [ Int.toNat_of_nonneg ] ; ring;
    unfold labelBound; norm_num; positivity;
  grind

end GlobalControl

end
