import Mathlib.Analysis.Complex.ExponentialBounds
import RequestProject.Core.Asymptotics
import RequestProject.GlobalControl.LevelSetParameters
import RequestProject.GlobalPeierlsBookkeeping

/-!
# Level-set label charges

Analytic and finite-combinatorial principles charging segment-start label
windows to hot-block and boundary energies.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### Label charging -/

/-- The number of admissible label assignments factors as the product of the
    per-segment-start window sizes. -/
lemma admLabels_card (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) :
    (admLabels BS c2 R H B).card
      = ∏ s ∈ RequestProject.segmentStarts BS.k0 BS.K H B, (labelFin BS c2 R s).card := by
  rw [admLabels, Finset.card_image_of_injOn, Finset.card_pi]
  -- the zero-extension map is injective on the pi
  intro ℓ hℓ ℓ' hℓ' heq
  rw [Finset.mem_coe, Finset.mem_pi] at hℓ hℓ'
  funext s hs
  have := congrFun heq s
  simpa [dif_pos hs] using this

/-- Generic charge-sum bound: summing the per-element charge `exp(ε·w j)` over
    all weight-`≤R` subsets is `≤ exp(2εR)·exp(numBlocks)`, via
    `weighted_subset_entropy` (with `ε' = 4ε`).  Instantiated for the hot
    (`w = Rw`) and boundary (`w = Pifloor`) charges. -/
lemma sum_subset_charge_le (BS : BlockSystem) (w : ℕ → ℝ) (R eps : ℝ)
    (heps : 0 < eps) (hw : ∀ j ∈ Finset.Icc BS.k0 BS.K, 0 ≤ w j) :
    (∑ S ∈ (Finset.Icc BS.k0 BS.K).powerset.filter (fun S => ∑ j ∈ S, w j ≤ R),
        ∏ j ∈ S, Real.exp (eps * w j))
      ≤ Real.exp (2 * eps * R) * Real.exp (numBlocks BS) := by
  have hcb : ∀ j ∈ Finset.Icc BS.k0 BS.K,
      Real.exp (eps * w j) ≤ Real.exp (4 * eps * w j / 4) :=
    fun j _ => le_of_eq (by congr 1; ring)
  have hwse := GlobalPeierls.weighted_subset_entropy (Finset.Icc BS.k0 BS.K) w
    (fun j => Real.exp (eps * w j)) (4 * eps) R (by linarith)
    (fun _ _ => Real.exp_nonneg _) hcb
  refine le_trans hwse ?_
  refine mul_le_mul (Real.exp_le_exp.mpr (le_of_eq (by ring)))
    (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (Real.exp_nonneg _)
  calc (∑ j ∈ Finset.Icc BS.k0 BS.K, Real.exp (-(4 * eps) * w j / 4))
      ≤ ∑ _j ∈ Finset.Icc BS.k0 BS.K, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj =>
          Real.exp_le_one_iff.mpr (by nlinarith [hw j hj, heps]))
    _ = (numBlocks BS : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
        norm_cast

/-! ### Analytic growth and per-label charge -/

/-
An exponential `2^{s-1}` term over a cube of logs
    eventually dominates any affine-plus-`log log` expression.  This is the only
    genuine analysis in the label-charging argument; everything else is algebra.
-/
lemma pow_beats_poly_log (C D : ℝ) (hD : 0 < D) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      C + (3 * s / 2) * Real.log 2 + Real.log (Real.log (2 ^ s))
        ≤ D * 2 ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3 := by
  -- We can divide both sides of the equation by $2^{s-1}$, which is positive.
  suffices h_div' : Filter.Tendsto (fun s : ℕ => (C + 3 * s / 2 * Real.log 2 + Real.log (Real.log (2 ^ s))) / (2 ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3)) Filter.atTop (nhds 0) by
    obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp h_div' D hD;
    refine' ⟨ N + 2, fun s hs => _ ⟩ ; specialize hN s ( by linarith ) ; simp_all +decide [ mul_div_assoc ];
    rw [ abs_of_nonneg ( Real.log_nonneg <| by nlinarith [ show ( s : ℝ ) ≥ 2 by norm_cast; linarith, Real.log_two_gt_d9, mul_div_cancel₀ ( 3 : ℝ ) two_ne_zero ] ) ] at hN ; rw [ div_lt_iff₀ <| by exact div_pos ( pow_pos zero_lt_two _ ) <| pow_pos ( mul_pos ( Nat.cast_pos.mpr <| Nat.sub_pos_of_lt <| by linarith ) <| Real.log_pos one_lt_two ) _ ] at hN ; linarith [ abs_le.mp ( show |C + 3 * ( s / 2 : ℝ ) * Real.log 2 + Real.log ( s * Real.log 2 )| ≤ _ from le_of_eq rfl ) ] ;
  -- We'll use the fact that $2^{s-1}$ grows much faster than $(\log (2^{s-1}))^3$.
  have h_exp_growth : Filter.Tendsto (fun s : ℕ => (s : ℝ) / (2 ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3)) Filter.atTop (nhds 0) := by
    -- We can simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun s : ℕ => (s : ℝ) * (Real.log 2 * (s - 1)) ^ 3 / (2 ^ (s - 1))) Filter.atTop (nhds 0) by
      convert h_simp using 2 ; norm_num [ Real.log_pow ] ; ring_nf;
      cases ‹_› <;> norm_num ; ring;
    -- We can factor out $s^4$ from the numerator and denominator.
    suffices h_factor : Filter.Tendsto (fun s : ℕ => (s ^ 4 : ℝ) / (2 ^ (s - 1))) Filter.atTop (nhds 0) by
      refine' squeeze_zero_norm' _ h_factor ; norm_num;
      refine' ⟨ 2, fun n hn => _ ⟩ ; gcongr;
      rw [ abs_of_nonneg ( Real.log_nonneg one_le_two ), abs_of_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ];
      exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( mul_nonneg ( Real.log_nonneg one_le_two ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( mul_le_of_le_one_left ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ( Real.log_two_lt_d9.le.trans ( by norm_num ) ) ) _ ) ( Nat.cast_nonneg _ ) ) ( by nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, pow_two ( n - 1 : ℝ ) ] );
    rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; norm_num;
    refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat ; norm_num;
    refine' ⟨ 200, fun n hn => _ ⟩ ; rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at *;
    nlinarith [ Nat.zero_le ( 2 ^ ‹_› ), pow_nonneg ( Nat.zero_le ‹_› ) 2, pow_nonneg ( Nat.zero_le ‹_› ) 3, pow_nonneg ( Nat.zero_le ‹_› ) 4 ];
  -- We'll use the fact that $Real.log (Real.log (2 ^ s))$ grows much slower than $s$.
  have h_log_log_growth : Filter.Tendsto (fun s : ℕ => Real.log (Real.log (2 ^ s)) / (2 ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3)) Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ h_exp_growth;
    norm_num [ Real.log_pow ];
    refine' ⟨ 2, fun n hn => _ ⟩ ; rw [ abs_of_nonneg ( Real.log_nonneg <| by nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, Real.log_two_gt_d9, Real.log_le_sub_one_of_pos zero_lt_two ] ) ] ; rw [ abs_of_nonneg ( Real.log_nonneg one_le_two ) ] ; gcongr;
    exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, show ( n : ℝ ) ≥ 2 by norm_cast ] );
  convert Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( show Filter.Tendsto ( fun s : ℕ => ( 1 : ℝ ) / ( 2 ^ ( s - 1 ) / Real.log ( 2 ^ ( s - 1 ) ) ^ 3 ) ) Filter.atTop ( nhds 0 ) from ?_ ) ) ( h_exp_growth.const_mul ( 3 * Real.log 2 / 2 ) ) ) h_log_log_growth using 2 <;> ring_nf;
  -- We'll use the fact that $(s-1)^3 * (1/2)^{s-1}$ tends to $0$ as $s$ tends to infinity.
  have h_lim : Filter.Tendsto (fun s : ℕ => (s : ℝ) ^ 3 * (1 / 2) ^ s) Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
    norm_num;
    refine' ⟨ 20, fun n hn => _ ⟩ ; rw [ inv_eq_one_div, div_pow, mul_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at *;
    nlinarith [ Nat.pow_le_pow_left ‹20 ≤ _› 3 ];
  convert h_lim.comp ( Filter.tendsto_sub_atTop_nat 1 ) |> Filter.Tendsto.mul_const ( Real.log 2 ^ 3 ) using 2 <;> norm_num ; ring

/-
For a segment start `s` past a uniform threshold, the
    label-window size `2·labelBound c2 s + 1` is dominated by the Peierls energy
    of the predecessor hot block `s-1`.
-/
lemma labelBound_charge_hot (c2 eps : ℝ) (heps : 0 < eps) (hc2 : 0 < c2) :
    ∃ k0min : ℕ, ∀ s : ℕ, k0min ≤ s →
      (2 * (labelBound c2 s : ℝ) + 1) ≤ Real.exp (eps * Rw c2 (s - 1)) := by
  -- By `Int.ceil_le`/`Int.le_ceil`, `(labelBound c2 s : ℝ) ≤ (20/3)*√(c2*2^s)*(16*2^s*log(2^s)) + 1`.
  -- Hence `2*(labelBound c2 s)+1 ≤ (640/3)*√(c2*2^s)*(2^s*log(2^s)) + 3`.
  have h_labelBound_le : ∀ s : ℕ, s ≥ 4 → 2 * (labelBound c2 s : ℝ) + 1 ≤ (640 / 3) * Real.sqrt (c2 * (2 : ℝ) ^ s) * (2 ^ s * Real.log (2 ^ s)) + 3 := by
    intro s hs; rw [ labelBound ] ; norm_num ; ring_nf ;
    linarith [ Int.ceil_lt_add_one ( Real.sqrt c2 * Real.sqrt ( 2 ^ s ) * s * Real.log 2 * 2 ^ s * ( 320 / 3 ) ) ];
  -- Choose `k0min` large enough so that for all `s ≥ k0min`, `P + 3 ≤ Real.exp (Real.log P + 1)`.
  obtain ⟨k0min, hk0min⟩ : ∃ k0min : ℕ, ∀ s : ℕ, k0min ≤ s → (640 / 3) * Real.sqrt (c2 * (2 : ℝ) ^ s) * (2 ^ s * Real.log (2 ^ s)) + 3 ≤ Real.exp (Real.log ((640 / 3) * Real.sqrt (c2 * (2 : ℝ) ^ s) * (2 ^ s * Real.log (2 ^ s))) + 1) := by
    have h_exp_log : ∃ k0min : ℕ, ∀ s : ℕ, k0min ≤ s → (640 / 3) * Real.sqrt (c2 * (2 : ℝ) ^ s) * (2 ^ s * Real.log (2 ^ s)) ≥ 3 := by
      have h_exp_log : Filter.Tendsto (fun s : ℕ => (640 / 3) * Real.sqrt (c2 * (2 : ℝ) ^ s) * (2 ^ s * Real.log (2 ^ s))) Filter.atTop Filter.atTop := by
        refine' Filter.tendsto_atTop_mono _ _;
        use fun n => 640 / 3 * Real.sqrt c2 * 2 ^ n * Real.log 2 * n;
        · norm_num [ Real.sqrt_mul, hc2.le ] ; ring_nf ; norm_num;
          exact fun n => le_mul_of_one_le_right ( by positivity ) ( Real.le_sqrt_of_sq_le ( mod_cast Nat.one_le_pow _ _ ( by decide ) ) );
        · exact Filter.Tendsto.atTop_mul_atTop₀ ( Filter.Tendsto.atTop_mul_const ( by positivity ) ( Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) ) tendsto_natCast_atTop_atTop;
      exact Filter.eventually_atTop.mp ( h_exp_log.eventually_ge_atTop 3 );
    obtain ⟨ k0min, hk0min ⟩ := h_exp_log; use k0min; intros s hs; rw [ Real.exp_add, Real.exp_log ( by linarith [ hk0min s hs ] ) ] ; nlinarith [ hk0min s hs, Real.add_one_le_exp 1 ] ;
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : ℕ, N ≤ s → Real.log ((640 / 3) * Real.sqrt (c2 * (2 : ℝ) ^ s) * (2 ^ s * Real.log (2 ^ s))) + 1 ≤ eps * c2 * 2 ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3 := by
    have := GlobalControl.pow_beats_poly_log ( Real.log ( 640 / 3 * Real.sqrt c2 ) + 2 ) ( eps * c2 ) ( by positivity );
    obtain ⟨ N, hN ⟩ := this; use N + 4; intros s hs; specialize hN s ( by linarith ) ; simp_all +decide [ Real.log_mul, Real.log_sqrt, hc2.le, ne_of_gt hc2 ] ;
    rw [ Real.log_mul, Real.log_mul, Real.log_mul, Real.log_mul, Real.log_sqrt, Real.log_sqrt ] <;> first | positivity | norm_num ; ring_nf at * ; norm_num at *;
    · grind +splitImp;
    · linarith;
    · linarith;
  use Max.max k0min ( Max.max N 4 ) ; intros s hs ; specialize h_labelBound_le s ( by linarith [ le_max_left k0min ( Max.max N 4 ), le_max_right k0min ( Max.max N 4 ), le_max_left N 4, le_max_right N 4 ] ) ; specialize hk0min s ( by linarith [ le_max_left k0min ( Max.max N 4 ), le_max_right k0min ( Max.max N 4 ), le_max_left N 4, le_max_right N 4 ] ) ; specialize hN s ( by linarith [ le_max_left k0min ( Max.max N 4 ), le_max_right k0min ( Max.max N 4 ), le_max_left N 4, le_max_right N 4 ] ) ; simp_all +decide [ Rw ] ;
  exact h_labelBound_le.trans ( hk0min.trans ( Real.exp_le_exp.mpr ( by simpa only [ mul_assoc, mul_div_assoc ] using hN ) ) )

/-! ### RequestProject.segmentStarts / labelFin structural helpers -/

/-
Every segment start lies in the block range `[k0, K]`.
-/
lemma segStarts_le (BS : BlockSystem) (H B : Finset ℕ) {s : ℕ}
    (hs : s ∈ RequestProject.segmentStarts BS.k0 BS.K H B) : BS.k0 ≤ s ∧ s ≤ BS.K := by
  exact Finset.mem_Icc.mp ( Finset.mem_sdiff.mp ( Finset.mem_filter.mp hs |>.1 ) |>.1 )

/-
A non-initial segment start has its predecessor in `H ∪ B`.
-/
lemma segStarts_pred_mem (BS : BlockSystem) (H B : Finset ℕ) {s : ℕ}
    (hs : s ∈ RequestProject.segmentStarts BS.k0 BS.K H B) (hne : s ≠ BS.k0) : (s - 1) ∈ H ∨ (s - 1) ∈ B := by
  unfold RequestProject.segmentStarts at hs; aesop;
lemma label_product_le (BS : BlockSystem) (c2 e0 eps R : ℝ) (H B : Finset ℕ)
    (heps : 0 ≤ eps)
    (hRwnn : ∀ j ∈ H, 0 ≤ Rw c2 j)
    (hPinn : ∀ j ∈ B, 0 ≤ Pifloor BS e0 j)
    (hcharge : ∀ s ∈ RequestProject.segmentStarts BS.k0 BS.K H B, s ≠ BS.k0 →
        ((labelFin BS c2 R s).card : ℝ) ≤
          (if s - 1 ∈ H then Real.exp (eps * Rw c2 (s - 1))
           else Real.exp (eps * Pifloor BS e0 (s - 1)))) :
    (∏ s ∈ RequestProject.segmentStarts BS.k0 BS.K H B, ((labelFin BS c2 R s).card : ℝ))
      ≤ ((labelFin BS c2 R BS.k0).card : ℝ)
          * (∏ j ∈ H, Real.exp (eps * Rw c2 j))
          * (∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j)) := by
  have h_erase : (∏ s ∈ (RequestProject.segmentStarts BS.k0 BS.K H B).erase BS.k0, (labelFin BS c2 R s).card : ℝ) ≤ (∏ j ∈ H, Real.exp (eps * Rw c2 j)) * (∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j)) := by
    refine' le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun s hs => hcharge s _ _ ) _;
    · exact Finset.mem_of_mem_erase hs;
    · exact Finset.ne_of_mem_erase hs;
    · have h_split : (∏ s ∈ (RequestProject.segmentStarts BS.k0 BS.K H B).erase BS.k0, (if s - 1 ∈ H then Real.exp (eps * Rw c2 (s - 1)) else Real.exp (eps * Pifloor BS e0 (s - 1)))) = (∏ j ∈ (H ∪ B) ∩ Finset.image (fun s => s - 1) ((RequestProject.segmentStarts BS.k0 BS.K H B).erase BS.k0), if j ∈ H then Real.exp (eps * Rw c2 j) else Real.exp (eps * Pifloor BS e0 j)) := by
        refine' Finset.prod_bij ( fun s hs => s - 1 ) _ _ _ _ <;> simp_all +decide;
        · exact fun a ha₁ ha₂ => ⟨ segStarts_pred_mem BS H B ha₂ ha₁, a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
        · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; rw [ tsub_left_inj ] at h <;> linarith [ segStarts_le BS H B ha₂, segStarts_le BS H B ha₄, BS.hk0 ] ;
      rw [ h_split, ← Finset.prod_inter_mul_prod_sdiff ];
      refine' mul_le_mul _ _ _ _;
      any_goals exact H;
      · rw [ ← Finset.prod_inter_mul_prod_sdiff H ( ( H ∪ B ) ∩ image ( fun s => s - 1 ) ( ( RequestProject.segmentStarts BS.k0 BS.K H B ).erase BS.k0 ) ∩ H ) ];
        simp +decide [ Finset.inter_comm ];
        exact le_trans ( by rw [ Finset.prod_congr rfl fun x hx => if_pos <| Finset.mem_of_mem_inter_left hx ] ) ( le_mul_of_one_le_right ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) <| le_trans ( by norm_num ) <| Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => Real.one_le_exp <| mul_nonneg heps <| hRwnn _ <| Finset.mem_sdiff.mp ‹_› |>.1 );
      · rw [ ← Finset.prod_sdiff <| show ( ( H ∪ B ) ∩ image ( fun s => s - 1 ) ( ( RequestProject.segmentStarts BS.k0 BS.K H B ).erase BS.k0 ) ) \ H ⊆ B from ?_ ];
        · rw [ Finset.prod_congr rfl fun x hx => if_neg <| by aesop ];
          exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ( by exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => Real.one_le_exp ( mul_nonneg heps ( hPinn _ ( by aesop ) ) ) ) );
        · grind;
      · exact Finset.prod_nonneg fun x hx => by split_ifs <;> positivity;
      · exact Finset.prod_nonneg fun _ _ => Real.exp_nonneg _;
  by_cases h : BS.k0 ∈ RequestProject.segmentStarts BS.k0 BS.K H B <;> simp_all +decide [ mul_assoc ];
  · rw [ ← Finset.mul_prod_erase _ _ h ] ; exact mul_le_mul_of_nonneg_left h_erase <| Nat.cast_nonneg _;
  · exact le_trans h_erase ( le_mul_of_one_le_left ( mul_nonneg ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ) ( mod_cast Finset.card_pos.mpr ⟨ 0, by
      unfold labelFin; simp +decide [ L0 ] ;
      exact Int.ceil_nonneg ( div_nonneg ( mul_nonneg ( by norm_num ) ( Real.sqrt_nonneg _ ) ) ( sigmaP_nonneg _ ) ) ⟩ ) )

end GlobalControl

end
