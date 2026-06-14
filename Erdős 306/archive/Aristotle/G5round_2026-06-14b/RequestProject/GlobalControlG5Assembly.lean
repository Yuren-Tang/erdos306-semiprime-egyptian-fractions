/-
G5 assembly leaf for `GlobalControl`.

This file imports the (stable, cached) cover layer `GlobalControlG5Data` and
develops the remaining `hrhs` ε-budget assembly (note 40 §5): the label-charging
(`weighted_subset_entropy` coupling), the per-fiber count discharge, and the
final `global_levelset` assembly.  Keeping it separate from the large
`GlobalControlG5Data.lean` lets each edit re-elaborate only this leaf.

## Status of the note-42 `hrhs` sub-lemmas

Proved and axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`):
  * `admLabels_card`, `sum_subset_charge_le` (pre-existing);
  * `pow_beats_poly_log` (N1 analytic core: `2^{s-1}/log^3` beats any
    affine-plus-`log log` term);
  * `labelBound_charge_hot` (N1 hot charge: `2·labelBound c2 s + 1 ≤
    exp(eps·Rw c2 (s-1))`);
  * `segStarts_le`, `segStarts_pred_mem`, `labelFin_card_pos` (structural
    helpers for the segment-start set and label windows);
  * `label_product_le` (N4: the segment-start label product factors as the
    initial window times the hot/boundary products, via the `s ↦ s-1` reindex);
  * `fiber_card_exp_bound` (N3: per-fiber count discharge combining
    `hot_factor` and `cold_factor`, taking the per-block label-size bound as a
    hypothesis `hlabsize`);
  * `cold_master` (N5: a single `(c2,e0,X0)` giving both block dominance
    `IsDominant` and the boundary penalty floor, from `boundary_penalty_per_k`);
  * `hadmL_final` (N5: the label-range admissibility `hadmL`, routing
    `coldLabel_mem_labelFin` through every segment start);
  * `global_levelset_final` (N5: the exact statement of
    `GlobalControl.global_levelset`, fully assembled from `cold_master`,
    `hadmL_final`, `hrhs_final`, and `global_levelset_route`).

Still open — ONE precisely-named residual `sorry`:
  * `hrhs_final` (the four-fold fiber sum bound).  This is the genuine
    mathematical obstruction, not a translation gap.  The note-42 N5 route
    factors `∑ℓ fiber.card ≤ |admLabels|·(per-fiber bound)` via `hrhs_inner`, but
    BOTH the per-fiber bound and `fiber_card_exp_bound`'s `hlabsize` hypothesis
    are FALSE for the *initial* segment (`segStart = k0`) when `R` is large:
    there the label window `L0 = ⌈ 7√R/σ_{k0} ⌉` exceeds the `cold_factor`
    threshold `N_k·2^k/16` (this already fails for `R ≳ 2^{2k0}/poly(k0)`), and
    a single large first-segment label can have a count comparable to a small
    one — so the `√R/σctrl` factor in the target CANNOT be obtained as a count
    of label choices but must be charged *collectively* against the first
    segment's energy (a segment-level counting lemma, the `σctrl`/S3 machinery).
    That collective lemma is absent from the frozen core, so `hrhs_final` is
    left as the single honest, TRUE residual `sorry`.  Everything else in the
    G5 chain (cover, admissibility, route closure, N1–N4, `cold_master`,
    `hadmL_final`, and the `global_levelset_final` assembly) is proved.
-/
import RequestProject.GlobalControlG5Data

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### Label-charging (note 40 §5 step (d)) -/

/-- The number of admissible label assignments factors as the product of the
    per-segment-start window sizes. -/
lemma admLabels_card (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) :
    (admLabels BS c2 R H B).card
      = ∏ s ∈ segStarts BS H B, (labelFin BS c2 R s).card := by
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

/-! ### N1 — analytic core and per-label charge -/

/-
**N1 analytic core.**  An exponential `2^{s-1}` term over a cube of logs
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
      convert h_simp using 2 ; norm_num [ Real.log_pow ] ; ring;
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
  convert Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_const_nhds.mul ( show Filter.Tendsto ( fun s : ℕ => ( 1 : ℝ ) / ( 2 ^ ( s - 1 ) / Real.log ( 2 ^ ( s - 1 ) ) ^ 3 ) ) Filter.atTop ( nhds 0 ) from ?_ ) ) ( h_exp_growth.const_mul ( 3 * Real.log 2 / 2 ) ) ) h_log_log_growth using 2 <;> ring;
  -- We'll use the fact that $(s-1)^3 * (1/2)^{s-1}$ tends to $0$ as $s$ tends to infinity.
  have h_lim : Filter.Tendsto (fun s : ℕ => (s : ℝ) ^ 3 * (1 / 2) ^ s) Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
    norm_num;
    refine' ⟨ 20, fun n hn => _ ⟩ ; rw [ inv_eq_one_div, div_pow, mul_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at *;
    nlinarith [ Nat.pow_le_pow_left ‹20 ≤ _› 3 ];
  convert h_lim.comp ( Filter.tendsto_sub_atTop_nat 1 ) |> Filter.Tendsto.mul_const ( Real.log 2 ^ 3 ) using 2 <;> norm_num ; ring

/-
**N1 hot charge.**  For a segment start `s` past a uniform threshold, the
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

/-! ### segStarts / labelFin structural helpers -/

/-
Every segment start lies in the block range `[k0, K]`.
-/
lemma segStarts_le (BS : BlockSystem) (H B : Finset ℕ) {s : ℕ}
    (hs : s ∈ segStarts BS H B) : BS.k0 ≤ s ∧ s ≤ BS.K := by
  exact Finset.mem_Icc.mp ( Finset.mem_sdiff.mp ( Finset.mem_filter.mp hs |>.1 ) |>.1 )

/-
A non-initial segment start has its predecessor in `H ∪ B`.
-/
lemma segStarts_pred_mem (BS : BlockSystem) (H B : Finset ℕ) {s : ℕ}
    (hs : s ∈ segStarts BS H B) (hne : s ≠ BS.k0) : (s - 1) ∈ H ∨ (s - 1) ∈ B := by
  unfold segStarts at hs; aesop;

/-
The label window is always nonempty (`labelBound`/`L0` are nonnegative).
-/
lemma labelFin_card_pos (BS : BlockSystem) (c2 R : ℝ)
    (s : ℕ) : 1 ≤ (labelFin BS c2 R s).card := by
  unfold labelFin;
  unfold L0 labelBound;
  split_ifs <;> norm_num;
  · exact Nat.one_le_iff_ne_zero.mpr ( by norm_num; linarith [ Int.ceil_nonneg ( show 0 ≤ 7 * Real.sqrt R / sigmaP ( BS.P BS.k0 ) by exact div_nonneg ( mul_nonneg ( by norm_num ) ( Real.sqrt_nonneg _ ) ) ( show 0 ≤ sigmaP ( BS.P BS.k0 ) by exact Real.sqrt_nonneg _ ) ) ] );
  · exact Nat.succ_le_of_lt ( by norm_num; linarith [ Int.ceil_nonneg ( show 0 ≤ 20 / 3 * ( Real.sqrt c2 * Real.sqrt ( 2 ^ s ) ) * ( 16 * 2 ^ s * ( s * Real.log 2 ) ) by positivity ) ] )

/-! ### N4 — label-product bound (structural) -/

/-
**N4 label product.**  Given a per-segment-start charge bounding each
    non-initial window by `exp` of the predecessor block's Peierls energy, the
    product over all segment starts factors as the initial window times the hot
    and boundary products.  Pure finite combinatorics (reindexing `s ↦ s-1`).
-/
lemma label_product_le (BS : BlockSystem) (c2 e0 eps R : ℝ) (H B : Finset ℕ)
    (heps : 0 ≤ eps)
    (hRwnn : ∀ j ∈ H, 0 ≤ Rw c2 j)
    (hPinn : ∀ j ∈ B, 0 ≤ Pifloor BS e0 j)
    (hcharge : ∀ s ∈ segStarts BS H B, s ≠ BS.k0 →
        ((labelFin BS c2 R s).card : ℝ) ≤
          (if s - 1 ∈ H then Real.exp (eps * Rw c2 (s - 1))
           else Real.exp (eps * Pifloor BS e0 (s - 1)))) :
    (∏ s ∈ segStarts BS H B, ((labelFin BS c2 R s).card : ℝ))
      ≤ ((labelFin BS c2 R BS.k0).card : ℝ)
          * (∏ j ∈ H, Real.exp (eps * Rw c2 j))
          * (∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j)) := by
  have h_erase : (∏ s ∈ (segStarts BS H B).erase BS.k0, (labelFin BS c2 R s).card : ℝ) ≤ (∏ j ∈ H, Real.exp (eps * Rw c2 j)) * (∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j)) := by
    refine' le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun s hs => hcharge s _ _ ) _;
    · exact Finset.mem_of_mem_erase hs;
    · exact Finset.ne_of_mem_erase hs;
    · have h_split : (∏ s ∈ (segStarts BS H B).erase BS.k0, (if s - 1 ∈ H then Real.exp (eps * Rw c2 (s - 1)) else Real.exp (eps * Pifloor BS e0 (s - 1)))) = (∏ j ∈ (H ∪ B) ∩ Finset.image (fun s => s - 1) ((segStarts BS H B).erase BS.k0), if j ∈ H then Real.exp (eps * Rw c2 j) else Real.exp (eps * Pifloor BS e0 j)) := by
        refine' Finset.prod_bij ( fun s hs => s - 1 ) _ _ _ _ <;> simp_all +decide;
        · exact fun a ha₁ ha₂ => ⟨ segStarts_pred_mem BS H B ha₂ ha₁, a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
        · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; rw [ tsub_left_inj ] at h <;> linarith [ segStarts_le BS H B ha₂, segStarts_le BS H B ha₄, BS.hk0 ] ;
      rw [ h_split, ← Finset.prod_inter_mul_prod_diff ];
      refine' mul_le_mul _ _ _ _;
      any_goals exact H;
      · rw [ ← Finset.prod_inter_mul_prod_diff H ( ( H ∪ B ) ∩ image ( fun s => s - 1 ) ( ( segStarts BS H B ).erase BS.k0 ) ∩ H ) ];
        simp +decide [ Finset.inter_comm ];
        exact le_trans ( by rw [ Finset.prod_congr rfl fun x hx => if_pos <| Finset.mem_of_mem_inter_left hx ] ) ( le_mul_of_one_le_right ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) <| le_trans ( by norm_num ) <| Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => Real.one_le_exp <| mul_nonneg heps <| hRwnn _ <| Finset.mem_sdiff.mp ‹_› |>.1 );
      · rw [ ← Finset.prod_sdiff <| show ( ( H ∪ B ) ∩ image ( fun s => s - 1 ) ( ( segStarts BS H B ).erase BS.k0 ) ) \ H ⊆ B from ?_ ];
        · rw [ Finset.prod_congr rfl fun x hx => if_neg <| by aesop ];
          exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ( by exact le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => Real.one_le_exp ( mul_nonneg heps ( hPinn _ ( by aesop ) ) ) ) );
        · grind;
      · exact Finset.prod_nonneg fun x hx => by split_ifs <;> positivity;
      · exact Finset.prod_nonneg fun _ _ => Real.exp_nonneg _;
  by_cases h : BS.k0 ∈ segStarts BS H B <;> simp_all +decide [ mul_assoc ];
  · rw [ ← Finset.mul_prod_erase _ _ h ] ; exact mul_le_mul_of_nonneg_left h_erase <| Nat.cast_nonneg _;
  · exact le_trans h_erase ( le_mul_of_one_le_left ( mul_nonneg ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ) ( mod_cast Finset.card_pos.mpr ⟨ 0, by
      unfold labelFin; simp +decide [ L0 ] ;
      exact Int.ceil_nonneg ( div_nonneg ( mul_nonneg ( by norm_num ) ( Real.sqrt_nonneg _ ) ) ( sigmaP_nonneg _ ) ) ⟩ ) )

/-! ### N3 — per-fiber count discharge -/

/-
**N3 fiber discharge.**  Combining `hot_factor` (for hot blocks) and
    `cold_factor` (for cold blocks, with the segment-start label of size
    `≤ N·2^k/16`), every fiber's cardinality is at most the per-block product of
    `exp(2ε(v k + 1))`.  The label-size discharge is supplied as `hlabsize`.
-/
lemma fiber_card_exp_bound (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ),
        X0 ≤ (2:ℝ) ^ BS.k0 →
        (∀ k ∈ Finset.Icc BS.k0 BS.K, k ∈ H → Rw c2 k ≤ (v k : ℝ) + 1) →
        (∀ k ∈ Finset.Icc BS.k0 BS.K, k ∉ H →
          |((ℓ (segStart BS H B k) : ℤ) : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16) →
        ((fiber BS H B v ℓ).card : ℝ) ≤
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
  obtain ⟨Xh, hXh0, hHot⟩ := hot_factor eps heps heps1 c2 hc2
  obtain ⟨Xc, hXc0, hCold⟩ := cold_factor eps heps
  use max Xh Xc
  simp [hXh0, hXc0];
  intros BS H B v ℓ hXh hXc hhot hlabsize
  apply fiber_prod_bound BS H B v ℓ eps;
  intro k hk; by_cases hkH : k ∈ H <;> simp +decide [ hkH ] ;
  · exact hHot BS k ( Finset.mem_Icc.mp hk |>.1 ) ( Finset.mem_Icc.mp hk |>.2 ) ( le_trans hXh ( pow_le_pow_right₀ ( by norm_num ) ( Finset.mem_Icc.mp hk |>.1 ) ) ) _ ( hhot k ( Finset.mem_Icc.mp hk |>.1 ) ( Finset.mem_Icc.mp hk |>.2 ) hkH );
  · norm_num +zetaDelta at *;
    exact le_trans ( hCold BS k hk.1 hk.2 ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hk.1 ] ) _ ( hlabsize k hk.1 hk.2 hkH ) _ ) ( Real.exp_le_exp.mpr ( by nlinarith ) )

/-! ### N5 — master constants, label admissibility, and final assembly -/

/-
**Master cold constants.**  A single triple `(c2,e0,X0)` providing both the
    block-dominance (`IsDominant`) used to read off cold labels and the boundary
    penalty floor.  Both are obtained from `boundary_penalty_per_k` (whose cold
    facts already expose, for the same `c2`, the residue agreement that yields
    dominance for `X0` large).
-/
lemma cold_master :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) := by
  obtain ⟨ c2, e0, X0, hc2, he0, hX0, h ⟩ := boundary_penalty_per_k;
  obtain ⟨X0thr, hX0thr⟩ : ∃ X0thr : ℕ, ∀ X : ℕ, X0thr ≤ X → 16 * e0 * Real.log X ≤ X := by
    have := SBEEForcing.exists_X0_const_logbnd ( 16 * e0 );
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
    · convert h_class_count.le using 1 ; norm_num [ classCount ]);
  · exact fun BS a k hk₁ hk₂ hk₃ hk₄ hk₅ hk₆ => h.2 BS a k hk₁ hk₂ hk₃ hk₆

/-
**Label admissibility (`hadmL`).**  For `k0` past a uniform threshold, the
    zero-extended cold labels of any sub-`R` assignment lie in `admLabels`.
    This routes `coldLabel_mem_labelFin` (needing `IsDominant` from `cold_master`)
    through every segment start.
-/
lemma hadmL_final (c2 X0 : ℝ) (hc2 : 0 < c2)
    (hdom : ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) :
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
  have hdomk : SBEEForcing.IsDominant (2 ^ s) (BS.P s) (restrict BS a s) (1 / 4) := by
    exact hdom BS a s hs1 hs2 ( by exact le_trans hX0 ( pow_le_pow_right₀ ( by norm_num ) hs1 ) ) hcold;
  apply coldLabel_mem_labelFin BS c2 R a s hs1 hs2 hR0 hc2.le (hk0min s (by linarith)).left hN8 hslog hdomk hcold hbR hσpos

/-- **N5 `hrhs` assembly (the single residual `sorry`).**  The four-fold fiber
    sum is bounded by `exp(A·numBlocks)·exp(8εR)·(1+√R/σctrl)`.

    This statement is TRUE (it is the level-set count of G5), but its proof is
    the genuine remaining obstruction.  The hot/boundary blocks and all
    non-initial cold segments assemble cleanly from `hrhs_inner`,
    `admLabels_card`, `label_product_le`, `sum_subset_charge_le`,
    `fiber_card_exp_bound`, and `sigmaCtrl_le_sigmaP_k0`; but the INITIAL
    segment defeats the per-fiber route: for large `R` the initial label window
    `L0 = ⌈7√R/σ_{k0}⌉` exceeds the `cold_factor` size threshold `N_k·2^k/16`,
    so neither `fiber_card_exp_bound`'s `hlabsize` nor the per-fiber bound it
    yields hold for first-segment cold blocks.  The `√R/σctrl` target factor
    must instead be charged collectively against the first segment's energy via
    a segment-level counting lemma that is not part of the frozen core.  Left as
    a precisely-named `sorry`. -/
lemma hrhs_final (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 e0 X0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) (hX0 : 0 < X0)
    (hdom : ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      X0 ≤ (2:ℝ) ^ BS.k0 → ∀ R : ℝ, 1 ≤ R →
        (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  sorry

/-- **G5 — global level-set theorem (final assembly).**  Identical statement to
    `GlobalControl.global_levelset`; kept in this leaf to avoid the cyclic
    import.  Assembles `cold_master`, `hadmL_final`, and `hrhs_final` through
    `global_levelset_route`. -/
theorem global_levelset_final (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  obtain ⟨c2, e0, X0, hc2, he0, hX0, hdom, hpen⟩ := cold_master
  obtain ⟨k0L, hadmL⟩ := hadmL_final c2 X0 hc2 hdom
  obtain ⟨k0R, A, hA, hrhs⟩ := hrhs_final eps heps heps1 c2 e0 X0 hc2 he0 hX0 hdom
  obtain ⟨k0X, hX0pow⟩ : ∃ n : ℕ, X0 ≤ (2:ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X0 (by norm_num : (1:ℝ) < 2)
    exact ⟨n, le_of_lt hn⟩
  refine ⟨max k0L (max k0R k0X), A, hA, ?_⟩
  intro BS hk0 hadm R hR
  have hk0L : k0L ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  have hk0R : k0R ≤ BS.k0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk0
  have hk0X : k0X ≤ BS.k0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk0
  have hX0k0 : X0 ≤ (2:ℝ) ^ BS.k0 :=
    le_trans hX0pow (pow_le_pow_right₀ (by norm_num) hk0X)
  refine global_levelset_route BS eps c2 e0 X0 R A (by linarith) hX0k0 ?_ ?_ ?_ ?_
  · -- hpen
    intro a _ha k hk1 hk2 hkX hkb
    exact hpen BS a k hk1 hk2 hkX hkb
  · -- hdom
    intro a _ha k hk1 hk2 hkc
    have hXk : X0 ≤ (2:ℝ) ^ k := le_trans hX0k0 (pow_le_pow_right₀ (by norm_num) hk1)
    have hnh : ¬ isHot BS c2 a k := fun h =>
      hkc (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hk2⟩, h⟩)
    exact hdom BS a k hk1 hk2 hXk hnh
  · -- hadmL
    intro a ha
    exact hadmL BS hk0L hX0k0 a R (by linarith) ha
  · -- hrhs
    exact hrhs BS hk0R hadm hX0k0 R hR

end GlobalControl