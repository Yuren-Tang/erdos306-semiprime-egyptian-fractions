/-
# SBEE Assembly: the faithful target `SBEEPartitionBound` and `single_block_counting`

This file formalizes **P3**: the faithful single-block counting target of
`28 Faithful SBEE Statement …md` and its assembly from Theorems A + B + C
(`30 §2`).

## Status overview

* `IrvingGood` — the faithful pruning/regime hypothesis (no free labeling).
* `SBEEPartitionBound` — the faithful target predicate (uniform `C`, pruning
  hypothesis, no labeling), exactly as designed in note 28 §3.
* `single_block_counting` — `SBEEPartitionBound c`.  **Fully proved (no `sorry`).**
  Assembled from the unified level-set bound `unified_levelset` (combining
  Theorem A+B below the window via `SBEEForcing.corollary_SBEE_below_window` and
  Theorem C above the window via `SBEEFingerprint.fingerprint_count`, glued by the
  asymptotic mesh `mesh_lemma : R_C ≤ R_w`) and the Laplace/dyadic-series step
  `partfun_series_bound`, with `sigmaP_upper` absorbing the additive constant.
-/
import RequestProject.SBEEForcing

open Finset

namespace SBEEAssembly

open scoped Classical

/-- **Irving-good / pruning hypothesis** (faithful, no free labeling).

    The block `P` is a set of primes lying in a dyadic window `[X, 2X]` of
    near-maximal density `|P| ≥ X/(2 log X)`.  This is the regime hypothesis that
    the unconditional proof of `29`/`30` actually uses (it replaces note 28 §4's
    original abstract reciprocal-dispersion form: `29`/`30` show this geometric
    condition *implies* the required dispersion via the deterministic Lemma D, so
    no Kloosterman/Irving input is needed).  It is genuinely restrictive — sparse
    or non-dyadic blocks fail it — so the target below is **not** vacuous. -/
def IrvingGood (P : Finset ℕ) : Prop :=
  ∃ X : ℕ, 0 < X ∧ (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) ∧
    (X:ℝ) / (2 * Real.log X) ≤ P.card

/-- **Faithful SBEE partition-function target** (note 28 §3).

    A *single* block-independent constant `C` such that for every Irving-good
    prime block `P` with at least two primes, the Gaussian partition function
    saves: `∑_a exp(-c·Q_P(a)) ≤ C / σ_P`.

    `C` is quantified *outside* `∀ P` (fixing the vacuity failure 2 of note 28),
    `IrvingGood P` is a genuine hypothesis (fixing the too-strong failure 3), and
    there is **no** free labeling in the statement (the dominant/non-dominant
    split is internal proof structure). -/
def SBEEPartitionBound (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p),
      IrvingGood P → 2 ≤ P.card →
        blockPartFun P hP c ≤ C / sigmaP P

/-
**Single-block counting = SBEE** (`30 §2`, assembled).

    The faithful target `SBEEPartitionBound c` holds.

    Proof (`30 §2`): trichotomy on `R` against the window floor `R_w ≍ X/log³X`
    (Theorem B) and the fingerprint threshold `R_C ≍ X^{2/3}log^{4/3}X`
    (Theorem C), with the mesh `R_C ≪ R_w` (asymptotic in `X`):
    * `R < R_w`: every level-set assignment is dominant
      (`SBEEForcing.theorem_B_nondominant_forcing`); apply Theorem A
      (`SBEEForcing.theorem_A_dominant_count`).
    * `R_w ≤ R ≤ R_triv`: `SBEEFingerprint.fingerprint_count` (Theorem C, proved).
    * `R > R_triv`: trivial.
    Integrating the resulting level-set bound against `c·e^{-cR}` (Laplace) yields
    the partition-function bound `∑_a e^{-cQ_P(a)} ≤ C/σ_P`.

    **Status**: fully proved (no `sorry`).  All of `fingerprint_count`,
    `theorem_A_dominant_count`, `theorem_B_nondominant_forcing`, the mesh
    `R_C ≤ R_w` and the Laplace/series transform are now machine-verified.

**Growth threshold with a log power.**  `X/(log X)^n → ∞`, so for any `K`
    there is `X0` with `K ≤ X/(log X)^n` for `X ≥ X0`.
-/
lemma logthreshold_pow (n : ℕ) (K : ℝ) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℕ, X0 ≤ X → K ≤ (X:ℝ)/(Real.log X)^n := by
  -- By the properties of logarithms and powers, we know that $\frac{X}{(\log X)^n} \to \infty$ as $X \to \infty$.
  have h_log_pow_inf : Filter.Tendsto (fun X : ℕ => (X : ℝ) / (Real.log X) ^ n) Filter.atTop Filter.atTop := by
    -- Let $y = \log x$, therefore the expression becomes $\frac{e^y}{y^n}$.
    suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ n) Filter.atTop Filter.atTop by
      have h_subst : Filter.Tendsto (fun X : ℕ => Real.exp (Real.log X) / (Real.log X) ^ n) Filter.atTop Filter.atTop := by
        exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
      exact h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with X hX using by rw [ Real.exp_log ( Nat.cast_pos.mpr hX ) ] );
    exact Real.tendsto_exp_div_pow_atTop n;
  rcases Filter.eventually_atTop.mp ( h_log_pow_inf.eventually_ge_atTop K ) with ⟨ X0, hX0 ⟩ ; exact ⟨ X0 + 1, by positivity, fun X hX => hX0 _ <| Nat.le_of_succ_le <| mod_cast hX ⟩

/-
**σ_P upper bound.**  For a dyadic prime block, `σ_P ≤ N/X²`.
-/
lemma sigmaP_upper (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) :
    sigmaP P ≤ (P.card:ℝ)/(X:ℝ)^2 := by
  refine Real.sqrt_le_iff.mpr ?_;
  refine' ⟨ by positivity, le_trans ( Finset.sum_le_sum fun pq hpq => one_div_le_one_div_of_le ?_ <| pow_le_pow_left₀ ( by positivity ) ( mul_le_mul ( Nat.cast_le.mpr <| hP _ pq.1.2 |>.2.1 ) ( Nat.cast_le.mpr <| hP _ pq.2.2 |>.2.1 ) ( by positivity ) <| by positivity ) 2 ) _ ⟩ <;> norm_num;
  · positivity;
  · field_simp;
    exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num [ sq, Finset.card_product ] )

/-
**Mesh `R_C ≤ R_w` (asymptotic).**  For `X` large the fingerprint threshold
    `Cε·X^{2/3}(log X)^{4/3}` is below the window floor `cp·X/(log X)³`.
-/
lemma mesh_lemma (cp Ceps : ℝ) (hcp : 0 < cp) (_hCeps : 0 < Ceps) :
    ∃ X1 : ℝ, 0 < X1 ∧ ∀ X : ℕ, X1 ≤ X →
      Ceps*(X:ℝ)^((2:ℝ)/3)*(Real.log X)^((4:ℝ)/3) ≤ cp*(X:ℝ)/(Real.log X)^3 := by
  obtain ⟨X1, hX1⟩ : ∃ X1 : ℝ, 0 < X1 ∧ ∀ X : ℕ, X1 ≤ X → Ceps^3 * (X : ℝ)^2 * (Real.log X)^4 ≤ cp^3 * (X : ℝ)^3 / (Real.log X)^9 := by
    obtain ⟨ X1, hX1 ⟩ := logthreshold_pow 13 ( Ceps^3 / cp^3 );
    refine' ⟨ Max.max X1 3, _, _ ⟩ <;> norm_num;
    intro X hX₁ hX₂; have := hX1.2 X hX₁; rw [ div_le_div_iff₀ ] at this;
    · rw [ le_div_iff₀ ( pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _ ) ] ; nlinarith [ show ( X : ℝ ) ^ 3 > 0 by positivity ] ;
    · positivity;
    · exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  refine' ⟨ Max.max X1 3, by positivity, fun X hX => _ ⟩ ; specialize hX1 ; replace hX1 := hX1.2 X ( le_trans ( le_max_left _ _ ) hX ) ; norm_num at *;
  contrapose! hX1;
  convert pow_lt_pow_left₀ hX1 ( div_nonneg ( mul_nonneg hcp.le ( Nat.cast_nonneg _ ) ) ( pow_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) _ ) ) three_ne_zero using 1 <;> ring_nf;
  norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), ← Real.rpow_mul ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ]

/-
**Unified level-set bound.**  Combining Theorem A+B (below the window, via
    `corollary_SBEE_below_window`) and Theorem C (`fingerprint_count`, above the
    window) through the mesh, every level set is bounded by
    `C₀·e^{εR}·(1 + √R/σ_P)` for all `R ≥ 1`.
-/
set_option maxHeartbeats 1000000 in
lemma unified_levelset (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ (C0 X1 : ℝ), 0 < C0 ∧ 0 < X1 ∧
      ∀ (X : ℕ), X1 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ C0 * Real.exp (eps*R) * (1 + Real.sqrt R / sigmaP P) := by
  -- Apply the provided solution to obtain the constants `C0` and `X1`.
  obtain ⟨cp, X0c, hcp, hX0c, Hcor⟩ := SBEEForcing.corollary_SBEE_below_window eps hε0 (1/4) (by norm_num) (by norm_num)
  obtain ⟨Ceps, X0f, hCeps, hX0f, Hfp⟩ := SBEEFingerprint.fingerprint_count eps hε0 hε1
  obtain ⟨Xm, hXm0, hmesh⟩ := mesh_lemma cp Ceps hcp hCeps
  obtain ⟨X16, hX160, hX16⟩ := logthreshold_pow 3 (16/cp)
  obtain ⟨Xc2, hXc20, hXc2⟩ := logthreshold_pow 1 4;
  refine' ⟨ 20, Max.max ( Max.max X0c X0f ) ( Max.max Xm ( Max.max X16 ( Max.max Xc2 3 ) ) ), _, _, _ ⟩ <;> norm_num;
  intro X hX0c hX0f hXm hX16 hXc2 hX3 P inst hP hN R hR1
  by_cases hRle : R ≤ cp * X / (Real.log X)^3;
  · convert le_trans ( Hcor X hX0c P hP hN R hR1 hRle ) _ using 1;
    ring_nf;
    linarith [ Real.exp_pos ( eps * R ) ];
  · have hRC : Ceps * X ^ ((2 : ℝ) / 3) * (Real.log X) ^ ((4 : ℝ) / 3) ≤ R := by
      exact le_trans ( hmesh X hXm ) ( le_of_not_ge hRle );
    have hNsqrt : (P.card : ℝ) ≤ Real.sqrt R / sigmaP P := by
      have hNsqrt : (P.card : ℝ) ≤ Real.sqrt R / sigmaP P := by
        have hσub : sigmaP P ≤ (P.card : ℝ) / (X : ℝ)^2 := by
          convert sigmaP_upper X ( by linarith ) P hP using 1
        have hN2X : (P.card : ℝ) ≤ 2 * X := by
          exact_mod_cast SBEEFingerprint.block_card_le_two_mul X P hP
        have hR16 : (16 : ℝ) ≤ R := by
          rename_i hX16' hXc2';
          have := hX16' X hX16; rw [ div_le_iff₀ ( by positivity ) ] at this; ring_nf at *; nlinarith;
        have hNsqrt : (P.card : ℝ) * sigmaP P ≤ Real.sqrt R := by
          refine le_trans ( mul_le_mul_of_nonneg_left hσub <| Nat.cast_nonneg _ ) ?_;
          rw [ mul_div, div_le_iff₀ ] <;> try positivity;
          exact le_trans ( mul_le_mul hN2X hN2X ( by positivity ) ( by positivity ) ) ( by nlinarith [ Real.sqrt_nonneg R, Real.sq_sqrt ( show 0 ≤ R by positivity ), show ( X : ℝ ) ^ 2 ≥ 0 by positivity ] );
        rwa [ le_div_iff₀ ( show 0 < sigmaP P from _ ) ];
        apply sigmaP_pos_of_two;
        · exact fun p hp => hP p hp |>.1;
        · contrapose! hN;
          interval_cases _ : #P <;> norm_num at *;
          · exact div_pos ( by positivity ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) );
          · rw [ lt_div_iff₀ ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ];
            have := Real.log_lt_sub_one_of_pos ( by positivity : 0 < ( X : ℝ ) / 2 );
            rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this;
            linarith [ this ( by linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] ), Real.log_le_sub_one_of_pos zero_lt_two ];
      exact hNsqrt;
    have hNsqrt : (P.card : ℝ) * Real.exp (eps * R) ≤ 20 * Real.exp (eps * R) * (1 + Real.sqrt R / sigmaP P) := by
      nlinarith [ Real.exp_pos ( eps * R ), show 0 ≤ Real.sqrt R / sigmaP P by exact div_nonneg ( Real.sqrt_nonneg _ ) ( show 0 ≤ sigmaP P by exact Real.sqrt_nonneg _ ) ];
    refine le_trans ?_ hNsqrt;
    convert Hfp X hX0f P hP _ R hRC using 1;
    exact Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ) hN )

/-
**Partition function from a level-set bound (Laplace / dyadic series).**
    A finite Gaussian sum `∑ exp(-c·qᵢ)` is controlled by a level-set bound
    `#{qᵢ ≤ R} ≤ C₀·e^{εR}·(1 + √R/σ)` (for `R ≥ 1`, `ε < c`) via a geometric
    majorant.
-/
set_option maxHeartbeats 1000000 in
lemma partfun_series_bound {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (c eps C0 sig : ℝ) (hc : 0 < c) (_hε0 : 0 ≤ eps) (hεc : eps < c)
    (hC0 : 0 ≤ C0) (hsig : 0 < sig)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
        ((Finset.univ.filter (fun i => q i ≤ R)).card : ℝ)
          ≤ C0 * Real.exp (eps*R) * (1 + Real.sqrt R / sig)) :
    ∑ i, Real.exp (-c * q i)
      ≤ C0 * Real.exp eps / (1 - Real.exp (-(c-eps)))^2 * (1 + 1/sig) := by
  -- Let $r := \exp(-(c-\epsilon))$; since $c-\epsilon > 0$, $0 < r < 1$.
  set r := Real.exp (-(c - eps)) with hr
  have hr_pos : 0 < r := by
    positivity
  have hr_lt_1 : r < 1 := by
    exact Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr ( sub_pos.mpr hεc ) );
  -- For each $i$, $\exp(-c q_i) \leq \exp(-c \lfloor q_i \rfloor)$ since $q_i \geq \lfloor q_i \rfloor \geq 0$ and $c > 0$.
  have h_floor_dom : ∑ i, Real.exp (-c * q i) ≤ ∑ m ∈ Finset.image (fun i => Nat.floor (q i)) Finset.univ, Real.exp (-c * m) * (Finset.card (Finset.filter (fun i => Nat.floor (q i) = m) Finset.univ)) := by
    have h_floor_dom : ∀ i, Real.exp (-c * q i) ≤ Real.exp (-c * (Nat.floor (q i) : ℝ)) := by
      exact fun i => Real.exp_le_exp.mpr ( mul_le_mul_of_nonpos_left ( Nat.floor_le ( hq i ) ) ( neg_nonpos.mpr hc.le ) );
    refine' le_trans ( Finset.sum_le_sum fun i _ => h_floor_dom i ) _;
    rw [ Finset.sum_image' ] ; simp +decide [ mul_comm ];
    intro i; rw [ Finset.sum_congr rfl fun j hj => by rw [ Finset.mem_filter.mp hj |>.2 ] ] ; simp +decide [ mul_comm ] ;
  -- For each $m$, the cardinality of the fiber $\{i : \lfloor q_i \rfloor = m\}$ is at most $C_0 \exp(\epsilon(m+1))(1 + (m+1)/\sigma)$.
  have h_fiber_bound : ∀ m : ℕ, (Finset.card (Finset.filter (fun i => Nat.floor (q i) = m) Finset.univ)) ≤ C0 * Real.exp (eps * (m + 1)) * (1 + (m + 1) / sig) := by
    intro m
    have h_fiber_bound_step : (Finset.card (Finset.filter (fun i => q i ≤ m + 1) Finset.univ)) ≤ C0 * Real.exp (eps * (m + 1)) * (1 + (m + 1) / sig) := by
      refine' le_trans ( hlevel ( m + 1 ) ( by linarith ) ) _;
      gcongr;
      exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩;
    refine' le_trans _ h_fiber_bound_step;
    gcongr;
    exact fun h => by linarith [ Nat.lt_floor_add_one ( q ‹_› ), show ( ⌊q ‹_›⌋₊ : ℝ ) = m by exact_mod_cast h ] ;
  -- So $\sum_{i} \exp(-c q_i) \leq \sum_{m} \exp(-c m) C_0 \exp(\epsilon(m+1))(1 + (m+1)/\sigma) = C_0 \exp(\epsilon) \sum_{m} r^m (1 + (m+1)/\sigma)$.
  have h_sum_bound : ∑ i, Real.exp (-c * q i) ≤ C0 * Real.exp eps * ∑' m : ℕ, r^m * (1 + (m + 1) / sig) := by
    have h_sum_bound : ∑ i, Real.exp (-c * q i) ≤ C0 * Real.exp eps * ∑ m ∈ Finset.image (fun i => Nat.floor (q i)) Finset.univ, r^m * (1 + (m + 1) / sig) := by
      refine le_trans h_floor_dom ?_;
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_le_sum fun m hm => _ ; specialize h_fiber_bound m ; simp_all +decide [Real.exp_neg, mul_assoc, mul_comm, mul_left_comm] ;
      convert mul_le_mul_of_nonneg_left h_fiber_bound ( inv_nonneg.2 ( Real.exp_nonneg ( c * m ) ) ) using 1 ; ring_nf;
      norm_num [ ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add ] ; ring_nf;
      simpa only [ mul_assoc, ← Real.exp_add ] using by ring_nf;
    refine' le_trans h_sum_bound ( mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum _ _ _ ) ( by positivity ) );
    · exact fun _ _ => by positivity;
    · have h_summable : Summable (fun m : ℕ => r^m * (m + 1)) := by
        refine' summable_of_ratio_norm_eventually_le _ _;
        exact ( 1 + r ) / 2;
        · grind;
        · norm_num [ pow_succ', mul_assoc, abs_of_pos hr_pos ];
          exact ⟨ ⌈ ( 1 + r ) / ( 1 - r ) ⌉₊ + 1, fun n hn => by rw [ abs_of_nonneg ( by positivity ), abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.le_ceil ( ( 1 + r ) / ( 1 - r ) ), show ( n : ℝ ) ≥ ⌈ ( 1 + r ) / ( 1 - r ) ⌉₊ + 1 by exact_mod_cast hn, pow_nonneg hr_pos.le n, mul_le_mul_of_nonneg_right ( show ( r : ℝ ) ≤ 1 by linarith ) ( pow_nonneg hr_pos.le n ), mul_div_cancel₀ ( 1 + r ) ( by linarith : ( 1 - r ) ≠ 0 ) ] ⟩;
      convert h_summable.mul_right ( 1 / sig ) |> Summable.add <| summable_geometric_of_lt_one hr_pos.le hr_lt_1 using 2
      all_goals first | rfl | ring_nf
  -- Evaluate the geometric series $\sum_{m=0}^{\infty} r^m (1 + (m+1)/\sigma)$.
  have h_geo_series : ∑' m : ℕ, r^m * (1 + (m + 1) / sig) = (1 / (1 - r)) + (1 / sig) * (1 / (1 - r)^2) := by
    have h_geo_series : ∑' m : ℕ, r^m * (m + 1) = 1 / (1 - r)^2 := by
      have h_geo_series : HasSum (fun m : ℕ => r^m * (m + 1)) (1 / (1 - r)^2) := by
        have h_geo_series : HasSum (fun m : ℕ => (m : ℝ) * r^m) (r / (1 - r)^2) := by
          have := tsum_coe_mul_geometric_of_norm_lt_one ( show ‖r‖ < 1 from by simpa [ abs_of_pos hr_pos ] using hr_lt_1 );
          exact this ▸ Summable.hasSum ( by exact ( by contrapose! this; erw [ tsum_eq_zero_of_not_summable this ] ; exact ne_of_lt ( div_pos hr_pos ( sq_pos_of_pos ( sub_pos.mpr hr_lt_1 ) ) ) ) );
        convert HasSum.add ( hasSum_geometric_of_lt_one hr_pos.le hr_lt_1 ) h_geo_series using 1 <;> ring_nf;
        grind;
      exact h_geo_series.tsum_eq;
    convert congr_arg₂ ( · + · ) ( tsum_geometric_of_lt_one hr_pos.le hr_lt_1 ) ( congr_arg ( fun x : ℝ => x / sig ) h_geo_series ) using 1 <;> ring_nf;
    rw [ ← tsum_mul_left ] ; rw [ ← Summable.tsum_add ] ; congr ; ext m ; ring;
    · refine' Summable.mul_left _ _;
      refine' Summable.add ( summable_geometric_of_lt_one hr_pos.le hr_lt_1 ) _;
      contrapose! h_geo_series;
      rw [ tsum_eq_zero_of_not_summable ] <;> norm_num;
      · nlinarith;
      · exact fun h => h_geo_series <| Summable.of_nonneg_of_le ( fun m => by positivity ) ( fun m => by exact mul_le_mul_of_nonneg_left ( by linarith ) ( by positivity ) ) h;
    · exact summable_geometric_of_lt_one hr_pos.le hr_lt_1;
  refine le_trans h_sum_bound ?_;
  rw [ h_geo_series ] ; ring_nf;
  rw [ add_comm ] ; gcongr; all_goals nlinarith only [ hr_pos, hr_lt_1 ]

/-
**Single-block counting = SBEE** (`30 §2`, assembled).
-/
theorem single_block_counting (c : ℝ) (hc : 0 < c) :
    SBEEPartitionBound c := by
  -- Set eps := min (c/2) (1/2). Then 0<eps, eps<c (eps≤c/2<c), eps<1 (eps≤1/2<1), and c-eps>0.
  set eps := min (c / 2) (1 / 2)
  have hε0 : 0 < eps := by
    positivity
  have hεc : eps < c := by
    exact lt_of_le_of_lt ( min_le_left _ _ ) ( half_lt_self hc )
  have hε1 : eps < 1 := by
    exact lt_of_le_of_lt ( min_le_right _ _ ) ( by norm_num );
  obtain ⟨ C0, X1, hC0, hX1, Huni ⟩ := SBEEAssembly.unified_levelset eps hε0 hε1;
  -- Set K := C0 * Real.exp eps / (1 - Real.exp (-(c-eps)))^2.
  set K := C0 * Real.exp eps / (1 - Real.exp (-(c-eps)))^2 with hK_def;
  -- Set M := ⌈X1⌉₊.
  set M := Nat.ceil X1 with hM_def;
  refine' ⟨ Max.max ( 3 * K ) ( ( 2 * ( M : ℝ ) ) ^ ( 2 * M ) * 2 + 1 ), _, _ ⟩ <;> norm_num;
  · exact Or.inr ( by positivity );
  · intro P hP hIrv hcard2
    obtain ⟨X, hX0, hPrange, hNbound⟩ := hIrv
    haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
    have hX1nat : 1 ≤ X := hX0
    have hσpos : 0 < sigmaP P := sigmaP_pos_of_two P hP hcard2
    have hσub : sigmaP P ≤ (P.card:ℝ)/(X:ℝ)^2 := sigmaP_upper X hX1nat P hPrange
    have hN2X : (P.card:ℝ) ≤ 2*X := by exact_mod_cast SBEEFingerprint.block_card_le_two_mul X P hPrange
    have hXr1 : (1:ℝ) ≤ X := by exact_mod_cast hX1nat
    have hσ2 : sigmaP P ≤ 2 := le_trans hσub (by rw [div_le_iff₀ (by positivity)]; nlinarith [hN2X, hXr1]);
    by_cases hXbig : X1 ≤ (X:ℝ);
    · have hlevel : ∀ R:ℝ, 1≤R → ((Finset.univ.filter (fun a:BlockAssignment P => QP P a ≤ R)).card:ℝ) ≤ C0*Real.exp (eps*R)*(1+Real.sqrt R/sigmaP P) := fun R hR => Huni X hXbig P hPrange hNbound R hR;
      have hser := partfun_series_bound (fun a:BlockAssignment P => QP P a) (fun a => QP_nonneg P a) c eps C0 (sigmaP P) hc (by positivity) (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hC0.le hσpos hlevel;
      have hKge : blockPartFun P hP c ≤ K * (1 + 1 / sigmaP P) := by
        unfold blockPartFun
        rw [hK_def]
        convert hser using 1
      rw [ le_div_iff₀ hσpos ];
      refine le_trans ?_ ( le_max_left _ _ );
      nlinarith [ mul_div_cancel₀ 1 hσpos.ne', show 0 ≤ K by exact div_nonneg ( mul_nonneg hC0.le ( Real.exp_nonneg _ ) ) ( sq_nonneg _ ) ];
    · have hbpf_le : blockPartFun P hP c ≤ (2*(X:ℝ))^P.card := by
        refine' le_trans ( Finset.sum_le_sum fun a _ => Real.exp_le_one_iff.mpr _ ) _ <;> norm_num;
        · exact mul_nonneg hc.le ( QP_nonneg P a );
        · exact le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun _ _ => show ( _ : ℝ ) ≤ 2 * X from mod_cast hPrange _ ( Subtype.mem _ ) |>.2.2 ) ( by norm_num );
      have hXM : X ≤ M := by
        exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil X1 ] );
      have hb : blockPartFun P hP c ≤ (2*(M:ℝ))^(2*M) := by
        refine le_trans hbpf_le ?_;
        exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr hXM ) zero_le_two ) _ ) ( pow_le_pow_right₀ ( by linarith [ show ( M : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.ceil_pos.mpr hX1 ) ] ) ( by linarith [ show ( P.card : ℕ ) ≤ 2 * X by exact_mod_cast hN2X ] ) );
      rw [ le_div_iff₀ hσpos ];
      exact le_trans ( mul_le_mul_of_nonneg_left hσ2 <| by exact Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) <| by nlinarith [ le_max_right ( 3 * K ) ( ( 2 * M : ℝ ) ^ ( 2 * M ) * 2 + 1 ) ] ;

end SBEEAssembly
