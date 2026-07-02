import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Converting finite sublevel-set growth into a Laplace-sum bound. -/

open Finset

namespace RequestProject

/-
**Partition function from a level-set bound (Laplace / dyadic series).**
    A finite Gaussian sum `∑ exp(-c·qᵢ)` is controlled by a level-set bound
    `#{qᵢ ≤ R} ≤ C₀·e^{εR}·(1 + √R/σ)` (for `R ≥ 1`, `ε < c`) via a geometric
    majorant.
-/
set_option maxHeartbeats 1000000 in
lemma partition_function_bound_of_level_sets {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
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


end RequestProject
