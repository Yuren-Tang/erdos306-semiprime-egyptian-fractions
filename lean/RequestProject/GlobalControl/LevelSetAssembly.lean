/-
G5 assembly leaf for `GlobalControl`.

This file imports the stable level-set data layer `GlobalControl.LevelSetData` and
develops the remaining `hrhs` ε-budget assembly (note 40 §5): the label-charging
(`weighted_subset_entropy` coupling), the per-fiber count discharge, and the
final `global_levelset` assembly.  Keeping it separate from the large
`LevelSetData.lean` lets each edit re-elaborate only this leaf.

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
  * `global_levelset` (N5: the exact statement of
    `GlobalControl.global_levelset`, fully assembled from `cold_master`,
    `hadmL_final`, `hrhs_final`, and `global_levelset_route`).

Now PROVED and axiom-clean (this round), completing the note-45 route:
  * `labelBound_charge_boundary` (+ `Pifloor_charge_lower`): the boundary
    analogue of `labelBound_charge_hot`;
  * `sigmaCtrl_pos`, `Pifloor_nonneg`, `block_card_lower` (structural positivity
    / density helpers);
  * `chargeH_le`, `chargeB_le` (the two Peierls charge sums via
    `sum_subset_charge_le`), `labelFin_k0_card_le` (initial window card),
    `hcharge_le` (the `label_product_le` per-start charge);
  * `fiber_card_exp_bound'` (per-fiber discharge WITHOUT `hlabsize`, via
    `hot_factor` + the label-uniform `cold_count_large`);
  * `cold_count_large` (label-uniform per-cold-block count) and
    `cold_count_nonwrap` (the non-wrapped huge-label case is an EMPTY fiber, via
    `theoremA_label_range`/`cold_label_size64`);
  * `hrhs_charge_bound` and `hrhs_final` (the full four-fold fiber sum bound),
    hence `global_levelset` — all reduced to the single kernel below.

Now CLOSED (this round), completing the G5 chain:
  * `wrapped_count_le_small_fixed_label` (the wrapped huge-label reduction) is
    fully proved.  `cold_count_wrap` applies this reduction to get a small fixed
    label `M`, then `cold_factor` with `2ε`.  The kernel extracts a dominant
    representative `M` and injects the wrapped `m`-fiber into the fixed-label
    `M`-fiber.  The extraction needs Theorem-B dominance for arbitrary block
    assignments in the cold range; since this only holds below Theorem-B's
    intrinsic constant, it is threaded as the hypothesis `ColdDominance c2`
    (discharged in `cold_master` via `theorem_B_nondominant_forcing`, taking the
    minimum of the boundary constant and Theorem-B's constant).  Supporting
    lemmas added: `two_prime_label_eq` (two-prime CRT label rigidity),
    `cold_small_label_agree` (per-assignment small-label extraction with residue
    agreement), and `Rw_mono_c2` / `not_isHot_mono_cold` / `boundarySet_mono`.
    The entire G5 chain (cover, admissibility, route closure, N1–N5,
    `cold_master`, `hadmL_final`, the per-fiber discharge, the charge assembly,
    and `global_levelset`) is now proved and axiom-clean
    (`propext`, `Classical.choice`, `Quot.sound`).
-/
import RequestProject.GlobalControl.LevelSetData
import RequestProject.GlobalPeierlsBookkeeping

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
      rw [ h_split, ← Finset.prod_inter_mul_prod_sdiff ];
      refine' mul_le_mul _ _ _ _;
      any_goals exact H;
      · rw [ ← Finset.prod_inter_mul_prod_sdiff H ( ( H ∪ B ) ∩ image ( fun s => s - 1 ) ( ( segStarts BS H B ).erase BS.k0 ) ∩ H ) ];
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

/-- **Cold-regime dominance for arbitrary block assignments.**
    At parameter `c2`, eventually every block-assignment of cold energy
    (`< Rw c2 k`) admits a dominant `(1/4)`-label.  This is
    `theorem_B_nondominant_forcing` re-routed to `BlockSystem` blocks; it holds
    only for `c2` at most Theorem-B's intrinsic constant, so it is carried as a
    hypothesis through the cold-count chain. -/
def ColdDominance (c2 : ℝ) : Prop :=
  ∃ X1 : ℝ, 0 < X1 ∧ ∀ (BS : BlockSystem) (k : ℕ),
    BS.k0 ≤ k → k ≤ BS.K → X1 ≤ (2:ℝ) ^ k →
    ∀ (b : BlockAssignment (BS.P k)) (Rb : ℝ),
      QP (BS.P k) b ≤ Rb → Rb < Rw c2 k →
      SBEEForcing.IsDominant ((2:ℕ) ^ k) (BS.P k) b (1/4)

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
    block-dominance (`IsDominant`) used to read off cold labels and the boundary
    penalty floor.  Both are obtained from `boundary_penalty_per_k` (whose cold
    facts already expose, for the same `c2`, the residue agreement that yields
    dominance for `X0` large).
-/
lemma cold_master_struct :
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
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) ∧
      ColdDominance c2 := by
  obtain ⟨c2P, e0, X0P, hc2P, he0, hX0P, hdomR, hpen⟩ := GlobalControl.cold_master_struct
  obtain ⟨c2B, X0B, hc2B, hX0B, HB⟩ := SBEEForcing.theorem_B_nondominant_forcing (1/4) (by norm_num) (by norm_num);
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
**N1 boundary charge.**  For a segment start `s` past a uniform threshold,
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
  -- Apply `pow_beats_poly_log` to obtain `N1` and `N2`.
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
    above `cold_factor`'s window (`N·2^k/16 < |m|`) but below the CRT wrap
    threshold (`|m| ≤ (2^k)²/2`), in the low-energy regime (`n+1 < Rw c2 k`) the
    fiber is EMPTY: by `theoremA_label_range` any `(3/4)`-conforming `b` of energy
    `≤ n+1` would force `|m| ≤ (20/3)√(n+1)/σ_k`, and combined with `sigmaP_lower`
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
              obtain ⟨ X0, hX0_pos, hX0 ⟩ := GlobalControl.cold_label_size64 c2 hc2;
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
**Per-assignment small-label extraction with residue agreement (note 45).**
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
  obtain ⟨X0s, hX0s0, Hsize⟩ := SBEEForcing.cold_label_size (1/4) (by norm_num) (by norm_num) c2 hc2
  obtain ⟨e0, X0e, he0pos, hX0e0, Hexc⟩ := SBEEForcing.cold_exception_bound (1/4) (by norm_num) (by norm_num) c2 hc2;
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

/-- **Wrapped-label reduction kernel (note 45).**
    In the low-energy wrapped regime, the assignments conforming to a large
    wrapped label `m` inject into the fixed-label fiber for one small label `M`.
    This is the Theorem-A-internal dominant-representative extraction and
    transport step; with it, `cold_count_wrap` is just `cold_factor`.  The cold
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
  obtain ⟨X0c, hX0c0, hlog⟩ := SBEEForcing.exists_X0_const_logbnd (8 * e0 + 8)
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

/-- **Wrapped huge-label cold count (note 45 wrapper).**
    For a label beyond the CRT wrap threshold (`(2^k)²/2 < |m|`), the per-block
    conforming count is still `≤ exp(2ε(n+1))`.  The actual wrapped-label work is
    isolated in `wrapped_count_le_small_fixed_label`; this lemma only applies
    `cold_factor` to the resulting small fixed label. -/
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
  obtain ⟨Xc, hXc0, hCold⟩ := cold_factor (2 * eps) (by positivity)
  refine ⟨max Xr Xc, by positivity, ?_⟩
  intro BS k hk1 hk2 hk3 m n hn hwrap
  obtain ⟨M, hMsmall, hleM⟩ :=
    hReduce BS k hk1 hk2 (le_trans (le_max_left _ _) hk3) m n hn hwrap
  exact le_trans hleM
    (by
      convert hCold BS k hk1 hk2 (le_trans (le_max_right _ _) hk3) M hMsmall n using 1)

/-- **The residual kernel (note 45): huge-label cold count in the low-energy
    regime.**  For a cold block (`n+1 < Rw c2 k`) and a label `m` LARGER than
    `cold_factor`'s window (`|m| > N·2^k/16`), the count of `(3/4)`-conforming
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
      `≤ exp(2ε(n+1))` via `hot_factor`;
    * else, if `|m| ≤ N·2^k/16`, the conforming count is `≤ exp(ε(n+1))` via
      `cold_factor`;
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
  obtain ⟨Xh, hXh0, hHot⟩ := hot_factor eps heps heps1 c2 hc2
  obtain ⟨Xc, hXc0, hCold⟩ := cold_factor eps heps
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
**Per-fiber count discharge, label-uniform version (note 45).**  Same as
    `fiber_card_exp_bound` but WITHOUT the per-block label-size hypothesis
    `hlabsize`: the per-fiber count `∏_k exp(2ε(v_k+1))` holds for ANY label
    assignment `ℓ`.  Hot blocks use `hot_factor`; cold blocks use the
    label-uniform `cold_count_large`.
-/
lemma fiber_card_exp_bound' (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 : ℝ) (hc2 : 0 < c2) (hdomB : ColdDominance c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ),
        X0 ≤ (2:ℝ) ^ BS.k0 →
        (∀ k ∈ Finset.Icc BS.k0 BS.K, k ∈ H → Rw c2 k ≤ (v k : ℝ) + 1) →
        ((fiber BS H B v ℓ).card : ℝ) ≤
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
  obtain ⟨Xh, hXh0, hHot⟩ := GlobalControl.hot_factor eps heps heps1 c2 hc2
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
      ∀ s ∈ segStarts BS H B, s ≠ BS.k0 →
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

/-
**N5 charge assembly (pre-collapse).**  The four-fold fiber sum is bounded
    by the initial label window times the shell bound times the two Peierls
    charge sums, all kept in unsimplified `exp` form for the final algebra.
    Combines `hrhs_inner`, `fiber_card_exp_bound'`, `admLabels_card`,
    `label_product_le` (with `hcharge_le`), and `chargeH_le`/`chargeB_le`.
-/
lemma hrhs_charge_bound (eps c2 e0 : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (hc2 : 0 < c2) (he0 : 0 < e0) (hdomB : ColdDominance c2) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem), k0min ≤ BS.k0 → ∀ R : ℝ, 0 ≤ R →
      (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
        ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
        ((labelFin BS c2 R BS.k0).card : ℝ)
          * (Real.exp ((2 * eps + eps) * R) *
              Real.exp ((numBlocks BS : ℝ) *
                (2 * eps + Real.log (1 / (1 - Real.exp (-eps))))))
          * (Real.exp (2 * eps * R) * Real.exp (numBlocks BS))
          * (Real.exp (2 * eps * R) * Real.exp (numBlocks BS)) := by
  obtain ⟨Xf, hXf0, hfib⟩ := fiber_card_exp_bound' eps heps heps1 c2 hc2 hdomB;
  obtain ⟨kf, hkf⟩ : ∃ kf : ℕ, Xf ≤ 2 ^ kf := by
    exact pow_unbounded_of_one_lt Xf one_lt_two |> fun ⟨ kf, hkf ⟩ => ⟨ kf, le_of_lt hkf ⟩
  obtain ⟨kh, hchg⟩ := hcharge_le eps c2 e0 heps hc2 he0
  obtain ⟨kb, hchB⟩ := chargeB_le eps e0 heps he0
  obtain ⟨kPnn, hPnn⟩ := Pifloor_nonneg e0 he0
  use max kf (max kh (max kb kPnn));
  intro BS hBS R hR0
  set C := (labelFin BS c2 R BS.k0).card
  set SB := Real.exp ((2 * eps + eps) * R) * Real.exp ((numBlocks BS : ℝ) * (2 * eps + Real.log (1 / (1 - Real.exp (-eps)))) );
  refine' le_trans ( Finset.sum_le_sum fun H hH => Finset.sum_le_sum fun B hB => _ ) _;
  use fun H B => C * SB * (∏ j ∈ H, Real.exp (eps * Rw c2 j)) * (∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j));
  · refine' le_trans ( hrhs_inner BS c2 R eps H B heps hR0 _ ) _;
    · intro v hv ℓ hℓ;
      apply hfib;
      · exact le_trans hkf ( pow_le_pow_right₀ ( by norm_num ) ( le_trans ( le_max_left _ _ ) hBS ) );
      · exact fun k hk hkH => Finset.mem_filter.mp hv |>.2.2 k hk hkH;
    · rw [ admLabels_card ];
      convert mul_le_mul_of_nonneg_right ( label_product_le BS c2 e0 eps R H B heps.le _ _ _ ) ( show 0 ≤ SB by positivity ) using 1;
      · norm_cast;
      · ring!;
      · exact fun _ _ => div_nonneg ( mul_nonneg hc2.le ( pow_nonneg zero_le_two _ ) ) ( pow_nonneg ( Real.log_nonneg ( one_le_pow₀ ( by norm_num ) ) ) _ );
      · simp +zetaDelta at *;
        exact fun j hj => hPnn BS j ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) hj ) ] ) ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) hj ) ] ) ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) hj ) ] );
      · exact hchg BS ( by linarith [ Nat.le_max_left kf ( Max.max kh ( Max.max kb kPnn ) ), Nat.le_max_right kf ( Max.max kh ( Max.max kb kPnn ) ), Nat.le_max_left kh ( Max.max kb kPnn ), Nat.le_max_right kh ( Max.max kb kPnn ), Nat.le_max_left kb kPnn, Nat.le_max_right kb kPnn ] ) R H B;
  · simp +decide only [mul_assoc, mul_comm, mul_left_comm];
    simp +decide only [← mul_assoc, ← sum_mul];
    simp +decide only [← mul_sum];
    refine' le_trans ( mul_le_mul_of_nonneg_left ( chargeH_le eps c2 R heps hc2 BS ) ( by positivity ) ) _;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hchB BS ( by linarith [ Nat.le_max_right kf ( Max.max kh ( Max.max kb kPnn ) ), Nat.le_max_left kh ( Max.max kb kPnn ), Nat.le_max_right kh ( Max.max kb kPnn ), Nat.le_max_left kb kPnn, Nat.le_max_right kb kPnn ] ) R ) ( by positivity ) ) ( by positivity ) ) _ ; ring_nf ; norm_num

/-
**N5 `hrhs` assembly.**  The four-fold fiber
    sum is bounded by `exp(A·numBlocks)·exp(8εR)·(1+√R/σctrl)`.
    (Now fully proved; the cold dominance is supplied via `hdomB`.)

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
    a segment-level counting lemma that is not part of the frozen core.

    This is now routed through the label-uniform `fiber_card_exp_bound'`
    (note 45): `hrhs_inner` applies for every `ℓ`, and the `√R/σctrl` factor is
    the first-segment window `L0` via `admLabels_card`/`sigmaCtrl_le_sigmaP_k0`.
-/
lemma hrhs_final (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 e0 X0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) (_hX0 : 0 < X0)
    (_hdom : ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4))
    (hdomB : ColdDominance c2) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      X0 ≤ (2:ℝ) ^ BS.k0 → ∀ R : ℝ, 1 ≤ R →
        (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  obtain ⟨kc, hc⟩ := hrhs_charge_bound eps c2 e0 heps heps1 hc2 he0 hdomB
  obtain ⟨csig, hcsig0, hsig⟩ := sigmaCtrl_le_sigmaP_k0
  set A0 := 2 * eps + Real.log (1 / (1 - Real.exp (-eps))) + 2
  set A := A0 + |Real.log (3 + 14 * csig)| + 2
  set k0min := max kc 2
  use k0min, A;
  refine' ⟨ _, _ ⟩;
  · exact add_pos_of_pos_of_nonneg ( add_pos_of_pos_of_nonneg ( add_pos_of_pos_of_nonneg ( by positivity ) ( Real.log_nonneg ( by rw [ le_div_iff₀ ] <;> nlinarith [ Real.exp_pos ( -eps ), Real.exp_lt_one_iff.mpr ( show -eps < 0 by linarith ) ] ) ) ) zero_le_two ) ( abs_nonneg _ ) |> add_pos_of_pos_of_nonneg <| by positivity;
  · intro BS hBS hk0 hX0 R hR
    have h_sigmaCtrl_pos : 0 < sigmaCtrl BS := by
      exact sigmaCtrl_pos_of_k0 BS ( le_trans ( le_max_right _ _ ) hBS )
    have h_sigmaP_pos : 0 < sigmaP (BS.P BS.k0) := by
      contrapose! h_sigmaCtrl_pos;
      exact le_trans ( hsig BS ( le_trans ( le_max_right _ _ ) hBS ) ) ( mul_nonpos_of_nonneg_of_nonpos ( by positivity ) h_sigmaCtrl_pos )
    have h_nb : (BS.k0 : ℝ) ≤ numBlocks BS := by
      exact_mod_cast Nat.le_sub_of_add_le ( by linarith [ hk0.1, hk0.2 ] )
    have h_nb_ge_1 : 1 ≤ numBlocks BS := by
      exact Nat.one_le_iff_ne_zero.mpr ( by rw [ numBlocks ] ; exact Nat.sub_ne_zero_of_lt ( by linarith [ hk0.1 ] ) );
    refine' le_trans ( hc BS ( le_trans ( le_max_left _ _ ) hBS ) R ( by positivity ) ) _;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( labelFin_k0_card_le BS c2 R ( by positivity ) ) _ ) _ ) _ ) _;
    · positivity;
    · positivity;
    · positivity;
    · -- Apply the bounds on the exponential terms and the logarithmic terms.
      have h_exp_bound : (3 + 14 * Real.sqrt R / sigmaP (BS.P BS.k0)) ≤ (3 + 14 * csig * BS.k0) * (1 + Real.sqrt R / sigmaCtrl BS) := by
        have h_exp_bound : 14 * Real.sqrt R / sigmaP (BS.P BS.k0) ≤ 14 * csig * BS.k0 * Real.sqrt R / sigmaCtrl BS := by
          field_simp;
          grind +locals;
        ring_nf at *;
        nlinarith [ show 0 ≤ Real.sqrt R * ( sigmaCtrl BS ) ⁻¹ by positivity, show 0 ≤ csig * BS.k0 by positivity ];
      have h_exp_bound : (3 + 14 * csig * BS.k0) ≤ Real.exp (|Real.log (3 + 14 * csig)|) * Real.exp (numBlocks BS) := by
        have h_exp_bound : 3 + 14 * csig * BS.k0 ≤ (3 + 14 * csig) * BS.k0 := by
          nlinarith [ show ( BS.k0 : ℝ ) ≥ 2 by norm_cast; exact le_trans ( le_max_right _ _ ) hBS ];
        refine le_trans h_exp_bound ?_;
        gcongr;
        · rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith ) ), Real.exp_log ( by linarith ) ];
        · exact le_trans h_nb ( by linarith [ Real.add_one_le_exp ( numBlocks BS : ℝ ) ] );
      refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ‹_› _ ) _ ) _ ) _;
      · positivity;
      · positivity;
      · positivity;
      · refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right h_exp_bound _ ) _ ) _ ) _ ) _;
        · positivity;
        · positivity;
        · positivity;
        · positivity;
        · norm_num [ ← Real.exp_add ] ; ring_nf;
          norm_num [ A, A0 ] ; ring_nf;
          norm_num [ mul_assoc, ← Real.exp_add, ← Real.exp_nat_mul ] ; ring_nf;
          refine' add_le_add _ _;
          · rw [ mul_assoc, mul_assoc, mul_assoc, mul_comm ];
            rw [ mul_assoc, mul_assoc, ← Real.exp_add ] ; ring_nf;
            exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ show ( numBlocks BS : ℝ ) ≥ 1 by norm_cast, abs_nonneg ( Real.log ( 3 + csig * 14 ) ) ] ) <| by positivity;
          · exact Real.exp_le_exp.mpr ( by nlinarith [ show ( numBlocks BS : ℝ ) ≥ 1 by norm_cast, show ( |Real.log ( 3 + csig * 14 )| : ℝ ) ≥ 0 by positivity, show ( eps : ℝ ) ≥ 0 by positivity, show ( R : ℝ ) ≥ 1 by norm_cast ] )

/-- **G5 — global level-set theorem (final assembly).**  Identical statement to
    `GlobalControl.global_levelset`; kept in this leaf to avoid the cyclic
    import.  Assembles `cold_master`, `hadmL_final`, and `hrhs_final` through
    `global_levelset_route`. -/
theorem global_levelset (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  obtain ⟨c2, e0, X0, hc2, he0, hX0, hdom, hpen, hdomB⟩ := cold_master
  obtain ⟨k0L, hadmL⟩ := hadmL_final c2 X0 hc2 hdom
  obtain ⟨k0R, A, hA, hrhs⟩ := hrhs_final eps heps heps1 c2 e0 X0 hc2 he0 hX0 hdom hdomB
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

/-- Compatibility alias for the historical assembly name. -/
alias global_levelset_final := global_levelset

end GlobalControl
