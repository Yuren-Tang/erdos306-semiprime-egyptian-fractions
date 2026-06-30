import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Elementary asymptotic thresholds used throughout the proof. -/

namespace RequestProject

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

end RequestProject
