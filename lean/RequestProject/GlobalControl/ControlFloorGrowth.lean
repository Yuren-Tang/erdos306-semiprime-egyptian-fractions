import RequestProject.GlobalControl.BoundaryFloorGrowth

/-!
# Control-floor growth

The forcing floor and boundary floor each dominate affine scale costs; their
minimum therefore absorbs every fixed entropy cost.
-/

open Finset BigOperators Classical
open Filter Topology

noncomputable section

namespace GlobalControl

/-- `Rw c2 k / (k+1) → ∞`, via comparison with `2^k/(k+1)^4`. -/
private lemma Rw_div_linear_tendsto
    (c2 : ℝ) (hc2 : 0 < c2) :
    Filter.Tendsto (fun k : ℕ => Rw c2 k / ((k : ℝ) + 1))
      Filter.atTop Filter.atTop := by
  refine tendsto_atTop_mono' Filter.atTop ?_
    (RequestProject.exp1_model_div_succ_pow_tendsto c2 hc2)
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by positivity
  have hk1pos : 0 < (k : ℝ) + 1 := by positivity
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) := hlog2pos.le
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos zero_lt_two]
  have hklog_nonneg : 0 ≤ (k : ℝ) * Real.log (2 : ℝ) :=
    mul_nonneg hkpos.le hlog2nonneg
  have hklog_le : (k : ℝ) * Real.log (2 : ℝ) ≤ (k : ℝ) + 1 := by
    nlinarith
  have hpow_le :
      ((k : ℝ) * Real.log (2 : ℝ)) ^ 3 ≤ ((k : ℝ) + 1) ^ 3 :=
    pow_le_pow_left₀ hklog_nonneg hklog_le 3
  have hden_le :
      ((k : ℝ) * Real.log (2 : ℝ)) ^ 3 * ((k : ℝ) + 1) ≤
        ((k : ℝ) + 1) ^ 4 := by
    calc
      ((k : ℝ) * Real.log (2 : ℝ)) ^ 3 * ((k : ℝ) + 1)
          ≤ ((k : ℝ) + 1) ^ 3 * ((k : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hpow_le hk1pos.le
      _ = ((k : ℝ) + 1) ^ 4 := by ring
  have hden_log_pos :
      0 < ((k : ℝ) * Real.log (2 : ℝ)) ^ 3 * ((k : ℝ) + 1) :=
    mul_pos (pow_pos (mul_pos hkpos hlog2pos) _) hk1pos
  have hden_poly_pos : 0 < ((k : ℝ) + 1) ^ 4 := pow_pos hk1pos _
  have hnum_nonneg : 0 ≤ c2 * (2 : ℝ) ^ k :=
    mul_nonneg hc2.le (pow_nonneg (by norm_num) _)
  unfold Rw
  rw [Real.log_pow]
  calc
    c2 * (2 : ℝ) ^ k / (((k : ℝ) + 1) ^ 4)
        ≤ c2 * (2 : ℝ) ^ k /
            (((k : ℝ) * Real.log (2 : ℝ)) ^ 3 * ((k : ℝ) + 1)) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_log_pos hden_le
    _ = (c2 * (2 : ℝ) ^ k / (((k : ℝ) * Real.log (2 : ℝ)) ^ 3)) /
          ((k : ℝ) + 1) := by
      field_simp [ne_of_gt hden_log_pos, ne_of_gt hk1pos]

/-- `Rw c2 k` eventually beats every affine function of `k`. -/
private lemma Rw_affine_lower
    (c2 : ℝ) (hc2 : 0 < c2) :
    ∀ (β A V : ℝ), 0 < β → 0 < A →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (A * (2 * (k : ℝ) + 1) + V) / β ≤ Rw c2 k := by
  intro β A V hβ hA
  obtain ⟨M, hM⟩ := RequestProject.affine_div_le_linear_multiple β A V hβ hA
  obtain ⟨K, hK⟩ :=
    RequestProject.beats_affine_of_tendsto (fun k : ℕ => Rw c2 k)
      (Rw_div_linear_tendsto c2 hc2) M
  exact ⟨K, fun k hk => le_trans (hM k) (hK k hk)⟩

/-- The global control floor eventually dominates every prescribed affine function of the base scale. -/
private lemma control_floor_affine_lower
    (c2 e0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ (β A V : ℝ), 0 < β → 0 < A →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
        (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤
          globalControlFloor BS c2 e0 := by
  intro β A V hβ hA
  obtain ⟨KRw, hRw⟩ := Rw_affine_lower c2 hc2 β A V hβ hA
  obtain ⟨KPi0, c0, hc0, hPiLower⟩ := boundary_floor_exp_poly_lower e0 he0
  obtain ⟨KPi1, hPi1⟩ := RequestProject.exp2_affine_lower c0 hc0 β A V hβ hA
  refine ⟨max KRw (max KPi0 KPi1), ?_⟩
  intro BS hk hadm
  have hkRw : KRw ≤ BS.k0 := le_trans (le_max_left _ _) hk
  have hkPi0 : KPi0 ≤ BS.k0 := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hk)
  have hkPi1 : KPi1 ≤ BS.k0 := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hk)
  have hRwBS :
      (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤ Rw c2 BS.k0 :=
    hRw BS.k0 hkRw
  have hPiModel :
      (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤
        c0 * ((2 : ℝ) ^ (2 * BS.k0)) / (((BS.k0 : ℝ) + 1) ^ 4) := by
    have := hPi1 BS.k0 hkPi1
    linarith
  have hPiBS :
      (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤ Pifloor BS e0 BS.k0 :=
    le_trans hPiModel (hPiLower BS hkPi0 hadm)
  unfold globalControlFloor
  exact le_min hRwBS hPiBS

/-- The global control floor eventually absorbs the fixed entropy and Laplace prefactors. -/
theorem control_floor_absorbs_entropy
    (c : ℝ) (_hc : 0 < c) (eps A c2 e0 : ℝ)
    (_heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
    (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ η : ℝ, 0 < η →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
        Real.exp
            (A * (numBlocks BS : ℝ) -
              (c - (8 * eps + c) / 2) * globalControlFloor BS c2 e0) *
          (2 *
            (Real.exp (8 * eps) /
              (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2)) ≤ η := by
  intro η hη
  classical
  set β : ℝ := c - (8 * eps + c) / 2 with hβ_def
  set K0 : ℝ := Real.exp (8 * eps) /
    (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2 with hK0_def
  have hβ_pos : 0 < β := by
    rw [hβ_def]
    nlinarith [hepsc]
  have hβ_alt : (8 * eps + c) / 2 - 8 * eps = β := by
    rw [hβ_def]
    ring
  have hden_ne :
      (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ≠ 0 := by
    rw [hβ_alt]
    have hexplt : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hK0_pos : 0 < K0 := by
    rw [hK0_def]
    exact div_pos (Real.exp_pos _) (sq_pos_of_ne_zero hden_ne)
  set V : ℝ := Real.log ((2 * K0) / η) with hV_def
  obtain ⟨k0floor, hfloor⟩ :=
    control_floor_affine_lower c2 e0 hc2 he0 β A V hβ_pos hA
  refine ⟨max 2 k0floor, ?_⟩
  intro BS hk0 hadm
  have hk0floor : k0floor ≤ BS.k0 := le_trans (le_max_right _ _) hk0
  have hfloorBS :
      (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤
        globalControlFloor BS c2 e0 :=
    hfloor BS hk0floor hadm
  have hT_le :
      A * (2 * (BS.k0 : ℝ) + 1) + V ≤
        β * globalControlFloor BS c2 e0 := by
    have := (div_le_iff₀ hβ_pos).mp hfloorBS
    nlinarith
  have hnum_nat : numBlocks BS ≤ 2 * BS.k0 + 1 := by
    unfold numBlocks admissibleGlobalRange at *
    omega
  have hnum :
      (numBlocks BS : ℝ) ≤ 2 * (BS.k0 : ℝ) + 1 := by
    exact_mod_cast hnum_nat
  have hAnum :
      A * (numBlocks BS : ℝ) ≤ A * (2 * (BS.k0 : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hnum hA.le
  have harg :
      A * (numBlocks BS : ℝ) -
          β * globalControlFloor BS c2 e0 ≤ -V := by
    linarith
  have hexp_le :
      Real.exp
          (A * (numBlocks BS : ℝ) -
            β * globalControlFloor BS c2 e0) ≤ Real.exp (-V) :=
    Real.exp_le_exp.mpr harg
  have htwoK0_pos : 0 < 2 * K0 := mul_pos (by norm_num) hK0_pos
  have htwoK0_nonneg : 0 ≤ 2 * K0 := htwoK0_pos.le
  have hratio_pos : 0 < (2 * K0) / η := div_pos htwoK0_pos hη
  calc
    Real.exp
          (A * (numBlocks BS : ℝ) -
            (c - (8 * eps + c) / 2) * globalControlFloor BS c2 e0) *
        (2 *
          (Real.exp (8 * eps) /
            (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2))
        = Real.exp
          (A * (numBlocks BS : ℝ) -
            β * globalControlFloor BS c2 e0) * (2 * K0) := by
            rw [hβ_def, hK0_def]
    _ ≤ Real.exp (-V) * (2 * K0) := by
        exact mul_le_mul_of_nonneg_right hexp_le htwoK0_nonneg
    _ = η := by
        rw [hV_def, Real.exp_neg, Real.exp_log hratio_pos]
        field_simp [hK0_pos.ne', hη.ne']

end GlobalControl

end
