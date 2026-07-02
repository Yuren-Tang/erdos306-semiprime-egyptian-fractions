import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Elementary asymptotic thresholds used throughout the proof. -/

namespace RequestProject

open Filter Topology

/-- Every constant multiple of `log X` is eventually bounded by `X`, for
natural-number scales `X`. -/
theorem eventually_const_mul_log_le_nat (K : ℝ) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℕ, X0 ≤ X → K * Real.log X ≤ X := by
  have h_tendsto_zero :
      Filter.Tendsto (fun X : ℝ => Real.log X / X) Filter.atTop (nhds 0) := by
    suffices h_log_recip :
        Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y))
          (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
      exact h_log_recip.congr (by simp +contextual [div_eq_inv_mul])
    norm_num
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa using Real.continuous_mul_log.neg.tendsto 0)
  obtain ⟨X0, hX0⟩ := Metric.tendsto_atTop.mp h_tendsto_zero
    (1 / (|K| + 1)) (by positivity)
  refine ⟨⌊X0⌋₊ + 1, ?_, ?_⟩ <;> norm_num at *
  · grind +splitImp
  · intro X hX
    specialize hX0 X (le_trans (Nat.lt_floor_add_one X0).le (by exact_mod_cast hX))
    rw [div_lt_iff₀] at hX0 <;> norm_cast at *
    · cases abs_cases K <;> cases abs_cases (Real.log X) <;>
        nlinarith [inv_mul_cancel₀ (by linarith : |K| + 1 ≠ 0),
          Real.log_nonneg (show (X : ℝ) ≥ 1 by norm_cast; linarith)]
    · linarith

/-- Every constant is eventually bounded by `X / (log X) ^ n`, for
natural-number scales `X`. -/
theorem eventually_le_natCast_div_log_pow (n : ℕ) (K : ℝ) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℕ, X0 ≤ X →
      K ≤ (X : ℝ) / (Real.log X) ^ n := by
  have h_log_pow_inf :
      Filter.Tendsto (fun X : ℕ => (X : ℝ) / (Real.log X) ^ n)
        Filter.atTop Filter.atTop := by
    suffices h_log :
        Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ n)
          Filter.atTop Filter.atTop by
      have h_subst :
          Filter.Tendsto
            (fun X : ℕ => Real.exp (Real.log X) / (Real.log X) ^ n)
            Filter.atTop Filter.atTop :=
        h_log.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact h_subst.congr' (by
        filter_upwards [Filter.eventually_gt_atTop 0] with X hX
        rw [Real.exp_log (Nat.cast_pos.mpr hX)])
    exact Real.tendsto_exp_div_pow_atTop n
  rcases Filter.eventually_atTop.mp (h_log_pow_inf.eventually_ge_atTop K) with
    ⟨X0, hX0⟩
  exact ⟨X0 + 1, by positivity,
    fun X hX => hX0 _ (Nat.le_of_succ_le (by exact_mod_cast hX))⟩

/-- A linear bound for `log` propagates from a base point `t0` throughout
`[t0, ∞)` once `t0 ≥ 1 / eps`. -/
theorem log_le_linear_of_base (eps t0 t : ℝ) (heps : 0 < eps)
    (ht0pos : 0 < t0) (ht0 : 1 / eps ≤ t0)
    (hlog : Real.log t0 ≤ eps * t0) (ht : t0 ≤ t) :
    Real.log t ≤ eps * t := by
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  have hdiv : Real.log (t / t0) ≤ t / t0 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log t = Real.log t0 + Real.log (t / t0) := by
    rw [Real.log_div (ne_of_gt htpos) (ne_of_gt ht0pos)]
    ring
  have hkey : (t - t0) * (eps - 1 / t0) ≥ 0 := by
    apply mul_nonneg (by linarith)
    have : 1 / t0 ≤ eps := by
      rw [div_le_iff₀ ht0pos]
      rw [div_le_iff₀ heps] at ht0
      nlinarith
    linarith
  have hexpand :
      (t - t0) * (eps - 1 / t0) = eps * t - eps * t0 - (t / t0 - 1) := by
    field_simp
  rw [hsplit]
  nlinarith [hdiv, hlog, hkey, hexpand]


lemma geom_div_pow_tendsto (r : ℝ) (hr : 1 < r) (m : ℕ) :
    Filter.Tendsto (fun n : ℕ => r ^ n / (n : ℝ) ^ m) Filter.atTop Filter.atTop := by
  have hlr : 0 < Real.log r := Real.log_pos hr
  have h1 : Filter.Tendsto (fun x : ℝ => Real.exp x / x ^ m) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_div_pow_atTop m
  have h2 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log r) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hlr tendsto_natCast_atTop_atTop
  have h3 := h1.comp h2
  have hcongr :
      (fun n : ℕ => r ^ n / (n : ℝ) ^ m) =
        fun n : ℕ =>
          (Real.log r) ^ m *
            (Real.exp ((n : ℝ) * Real.log r) / (((n : ℝ) * Real.log r) ^ m)) := by
    funext n
    rw [Real.exp_nat_mul, Real.exp_log (by linarith), mul_pow]
    by_cases hn : (n : ℝ) = 0
    · have hn0 : n = 0 := Nat.cast_eq_zero.mp hn
      subst n
      by_cases hm : m = 0
      · subst m
        simp
      · simp [zero_pow hm]
    · field_simp [hn, ne_of_gt hlr]
  rw [hcongr]
  exact h3.const_mul_atTop (by positivity)

lemma beats_affine_of_tendsto (f : ℕ → ℝ)
    (hf : Filter.Tendsto (fun n : ℕ => f n / ((n : ℝ) + 1)) Filter.atTop Filter.atTop)
    (M : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → M * ((k : ℝ) + 1) ≤ f k := by
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hf.eventually_ge_atTop M)
  refine ⟨K, ?_⟩
  intro k hk
  have hMk : M ≤ f k / ((k : ℝ) + 1) := hK k hk
  have hpos : 0 < (k : ℝ) + 1 := by positivity
  calc
    M * ((k : ℝ) + 1) ≤ (f k / ((k : ℝ) + 1)) * ((k : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right hMk hpos.le
    _ = f k := by field_simp [ne_of_gt hpos]

lemma affine_div_le_linear_multiple
    (β A V : ℝ) (hβ : 0 < β) (hA : 0 < A) :
    ∃ M : ℝ, ∀ k : ℕ,
      (A * (2 * (k : ℝ) + 1) + V) / β ≤ M * ((k : ℝ) + 1) := by
  refine ⟨(2 * A + |A + V|) / β, ?_⟩
  intro k
  have hk : 0 ≤ (k : ℝ) := by positivity
  have hAV : A + V ≤ |A + V| := le_abs_self _
  have hAbs : 0 ≤ |A + V| := abs_nonneg _
  have hAbsMul : 0 ≤ |A + V| * (k : ℝ) := mul_nonneg hAbs hk
  have hnum :
      A * (2 * (k : ℝ) + 1) + V ≤
        (2 * A + |A + V|) * ((k : ℝ) + 1) := by
    nlinarith [hAV, hA.le, hk, hAbsMul]
  calc
    (A * (2 * (k : ℝ) + 1) + V) / β
        ≤ ((2 * A + |A + V|) * ((k : ℝ) + 1)) / β :=
          div_le_div_of_nonneg_right hnum hβ.le
    _ = ((2 * A + |A + V|) / β) * ((k : ℝ) + 1) := by
      field_simp [ne_of_gt hβ]

lemma exp1_model_div_succ_pow_tendsto
    (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun k : ℕ => c * ((2 : ℝ) ^ k) / (((k : ℝ) + 1) ^ 4))
      Filter.atTop Filter.atTop := by
  have hbase :
      Filter.Tendsto
        (fun k : ℕ => (2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 4))
        Filter.atTop Filter.atTop := by
    exact (geom_div_pow_tendsto 2 one_lt_two 4).comp
      (tendsto_add_atTop_nat 1)
  have hscaled := hbase.const_mul_atTop (by positivity : 0 < c / 2)
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with k hk
  have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hkpos]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The model term divided by `(k+1)` still tends to infinity. -/
lemma exp2_model_div_linear_tendsto
    (c0 : ℝ) (hc0 : 0 < c0) :
    Filter.Tendsto
      (fun k : ℕ =>
        (c0 * ((2 : ℝ) ^ (2 * k)) / (((k : ℝ) + 1) ^ 4)) /
          ((k : ℝ) + 1))
      Filter.atTop Filter.atTop := by
  have hbase :
      Filter.Tendsto
        (fun k : ℕ => (4 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ 5))
        Filter.atTop Filter.atTop := by
    exact (geom_div_pow_tendsto 4 (by norm_num) 5).comp
      (tendsto_add_atTop_nat 1)
  have hscaled := hbase.const_mul_atTop (by positivity : 0 < c0 / 4)
  refine hscaled.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with k hk
  have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
  have hpow : ((2 : ℝ) ^ (2 * k)) = (4 : ℝ) ^ k := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
  rw [hpow]
  field_simp [hkpos]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf

end RequestProject
