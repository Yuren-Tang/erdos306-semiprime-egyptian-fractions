import RequestProject.GlobalControl.Localization

/-!
# Boundary-floor growth

Prime-density lower bounds force the boundary penalty floor to grow like an
exponential-over-polynomial function of the base scale.
-/

open Finset BigOperators Classical
open Filter Topology

noncomputable section

namespace GlobalControl

private lemma density_card_ge
    (e0 : ℝ) :
    ∃ K1 : ℕ, ∀ (BS : BlockSystem), K1 ≤ BS.k0 → admissibleGlobalRange BS →
      4 * (e0 + 1) ≤ ((BS.P BS.k0).card : ℝ) ∧
      4 * (e0 + 1) ≤ ((BS.P (BS.k0 + 1)).card : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have htend :
      Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / (k : ℝ)) Filter.atTop Filter.atTop :=
    by simpa using RequestProject.geom_div_pow_tendsto 2 one_lt_two 1
  obtain ⟨K, hK⟩ :=
    Filter.eventually_atTop.mp
      (htend.eventually_ge_atTop (8 * (e0 + 1) * Real.log (2 : ℝ)))
  refine ⟨max 1 K, ?_⟩
  intro BS hBS hadm
  have hk0K : K ≤ BS.k0 := le_trans (le_max_right _ _) hBS
  have hk0posNat : 1 ≤ BS.k0 := le_trans (le_max_left _ _) hBS
  have hk0pos : 0 < (BS.k0 : ℝ) := by exact_mod_cast hk0posNat
  have hk0logpos : 0 < 2 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)) := by positivity
  have hpowk :
      8 * (e0 + 1) * Real.log (2 : ℝ) ≤
        (2 : ℝ) ^ BS.k0 / (BS.k0 : ℝ) :=
    hK BS.k0 hk0K
  have htargetk :
      4 * (e0 + 1) ≤
        (2 : ℝ) ^ BS.k0 / (2 * ((BS.k0 : ℝ) * Real.log (2 : ℝ))) := by
    rw [le_div_iff₀ hk0logpos]
    have hmul := mul_le_mul_of_nonneg_right hpowk hk0pos.le
    have hcancel :
        ((2 : ℝ) ^ BS.k0 / (BS.k0 : ℝ)) * (BS.k0 : ℝ) =
          (2 : ℝ) ^ BS.k0 := by
      field_simp [ne_of_gt hk0pos]
    rw [hcancel] at hmul
    nlinarith
  have hdensk := BS.hdensity BS.k0 le_rfl (by linarith [BS.hk])
  have hdensk' :
      (2 : ℝ) ^ BS.k0 / (2 * ((BS.k0 : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P BS.k0).card : ℝ) := by
    convert hdensk using 1
    norm_num [Real.log_pow]
  have hk1K : K ≤ BS.k0 + 1 := le_trans hk0K (Nat.le_succ _)
  have hk1posNat : 1 ≤ BS.k0 + 1 := by omega
  have hk1pos : 0 < ((BS.k0 + 1 : ℕ) : ℝ) := by exact_mod_cast hk1posNat
  have hk1logpos : 0 < 2 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)) := by
    positivity
  have hpowk1 :
      8 * (e0 + 1) * Real.log (2 : ℝ) ≤
        (2 : ℝ) ^ (BS.k0 + 1) / ((BS.k0 + 1 : ℕ) : ℝ) :=
    hK (BS.k0 + 1) hk1K
  have htargetk1 :
      4 * (e0 + 1) ≤
        (2 : ℝ) ^ (BS.k0 + 1) /
          (2 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) := by
    rw [le_div_iff₀ hk1logpos]
    have hmul := mul_le_mul_of_nonneg_right hpowk1 hk1pos.le
    have hcancel :
        ((2 : ℝ) ^ (BS.k0 + 1) / ((BS.k0 + 1 : ℕ) : ℝ)) *
            ((BS.k0 + 1 : ℕ) : ℝ) =
          (2 : ℝ) ^ (BS.k0 + 1) := by
      field_simp [ne_of_gt hk1pos]
    rw [hcancel] at hmul
    nlinarith
  have hk1leK : BS.k0 + 1 ≤ BS.K := by
    have : BS.k0 + 1 ≤ 2 * BS.k0 := by omega
    exact le_trans this hadm.1
  have hdensk1 := BS.hdensity (BS.k0 + 1) (by omega) hk1leK
  have hdensk1' :
      (2 : ℝ) ^ (BS.k0 + 1) /
          (2 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P (BS.k0 + 1)).card : ℝ) := by
    convert hdensk1 using 1
    norm_num [Real.log_pow]
  exact ⟨le_trans htargetk hdensk', le_trans htargetk1 hdensk1'⟩

private lemma sub_half {e0 N : ℝ} (he0 : 0 < e0) (hN : 4 * (e0 + 1) ≤ N) :
    N / 2 ≤ N - e0 ∧ N / 2 ≤ N - e0 - 1 := by
  constructor <;> linarith

private lemma Pifloor_density_raw_lower
    (e0 : ℝ) (he0 : 0 < e0) :
    ∃ K1 : ℕ, ∀ (BS : BlockSystem), K1 ≤ BS.k0 → admissibleGlobalRange BS →
      ((2 : ℝ) ^ (BS.k0 + 1) /
          (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))) *
        (((2 : ℝ) ^ BS.k0 /
          (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)))) ^ 3) /
        (2 ^ 13 * ((2 : ℝ) ^ BS.k0) ^ 2) ≤
          Pifloor BS e0 BS.k0 := by
  obtain ⟨K1, hcard⟩ := density_card_ge e0
  refine ⟨K1, ?_⟩
  intro BS hK hadm
  have hcards := hcard BS hK hadm
  have hk0posNat : 1 ≤ BS.k0 := BS.hk0
  have hk0pos : 0 < (BS.k0 : ℝ) := by exact_mod_cast hk0posNat
  have hk1pos : 0 < ((BS.k0 + 1 : ℕ) : ℝ) := by positivity
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have hden0pos : 0 < 2 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)) := by positivity
  have hden1pos :
      0 < 2 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)) := by positivity
  have hdens0 := BS.hdensity BS.k0 le_rfl (by linarith [BS.hk])
  have hdens0' :
      (2 : ℝ) ^ BS.k0 / (2 * ((BS.k0 : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P BS.k0).card : ℝ) := by
    convert hdens0 using 1
    norm_num [Real.log_pow]
  have hk1leK : BS.k0 + 1 ≤ BS.K := by
    have : BS.k0 + 1 ≤ 2 * BS.k0 := by omega
    exact le_trans this hadm.1
  have hdens1 := BS.hdensity (BS.k0 + 1) (by omega) hk1leK
  have hdens1' :
      (2 : ℝ) ^ (BS.k0 + 1) /
          (2 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P (BS.k0 + 1)).card : ℝ) := by
    convert hdens1 using 1
    norm_num [Real.log_pow]
  have hhalf0 :
      ((BS.P BS.k0).card : ℝ) / 2 ≤ ((BS.P BS.k0).card : ℝ) - e0 :=
    (sub_half he0 hcards.1).1
  have hhalf1 :
      ((BS.P (BS.k0 + 1)).card : ℝ) / 2 ≤
        ((BS.P (BS.k0 + 1)).card : ℝ) - e0 - 1 :=
    (sub_half he0 hcards.2).2
  have hmodel0 :
      (2 : ℝ) ^ BS.k0 / (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P BS.k0).card : ℝ) / 2 := by
    calc
      (2 : ℝ) ^ BS.k0 / (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)))
          = ((2 : ℝ) ^ BS.k0 / (2 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)))) / 2 := by
            ring
      _ ≤ ((BS.P BS.k0).card : ℝ) / 2 := by gcongr
  have hmodel1 :
      (2 : ℝ) ^ (BS.k0 + 1) /
          (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P (BS.k0 + 1)).card : ℝ) / 2 := by
    calc
      (2 : ℝ) ^ (BS.k0 + 1) /
          (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))
          =
        ((2 : ℝ) ^ (BS.k0 + 1) /
          (2 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))) / 2 := by
            ring
      _ ≤ ((BS.P (BS.k0 + 1)).card : ℝ) / 2 := by gcongr
  have hsub0_nonneg : 0 ≤ ((BS.P BS.k0).card : ℝ) - e0 := by
    exact le_trans (by positivity : 0 ≤ ((BS.P BS.k0).card : ℝ) / 2) hhalf0
  have hsub1_nonneg :
      0 ≤ ((BS.P (BS.k0 + 1)).card : ℝ) - e0 - 1 := by
    exact le_trans (by positivity :
      0 ≤ (2 : ℝ) ^ (BS.k0 + 1) /
        (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))) (le_trans hmodel1 hhalf1)
  have hmodel0sub :
      (2 : ℝ) ^ BS.k0 / (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P BS.k0).card : ℝ) - e0 :=
    le_trans hmodel0 hhalf0
  have hmodel1sub :
      (2 : ℝ) ^ (BS.k0 + 1) /
          (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) ≤
        ((BS.P (BS.k0 + 1)).card : ℝ) - e0 - 1 :=
    le_trans hmodel1 hhalf1
  have hprod :
      (2 : ℝ) ^ (BS.k0 + 1) /
          (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ))) *
        ((2 : ℝ) ^ BS.k0 /
          (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)))) ^ 3 ≤
      (((BS.P (BS.k0 + 1)).card : ℝ) - e0 - 1) *
        (((BS.P BS.k0).card : ℝ) - e0) ^ 3 := by
    exact mul_le_mul hmodel1sub
      (pow_le_pow_left₀ (by positivity) hmodel0sub 3)
      (by positivity)
      hsub1_nonneg
  have hden_nonneg : 0 ≤ 2 ^ 13 * ((2 : ℝ) ^ BS.k0) ^ 2 := by positivity
  unfold Pifloor
  exact div_le_div_of_nonneg_right hprod hden_nonneg

/-- Prime density gives an exponential-over-polynomial lower bound for the
boundary penalty floor.

This is the density chain from `BS.hdensity` at `k₀` and `k₀+1`: after discarding
the fixed exception budget, `Pifloor` is still bounded below by an
exponential-over-polynomial term, uniformly over admissible block systems.
-/
lemma boundary_floor_exp_poly_lower
    (e0 : ℝ) (he0 : 0 < e0) :
    ∃ K1 : ℕ, ∃ c0 : ℝ, 0 < c0 ∧
      ∀ (BS : BlockSystem), K1 ≤ BS.k0 → admissibleGlobalRange BS →
        c0 * ((2 : ℝ) ^ (2 * BS.k0)) / (((BS.k0 : ℝ) + 1) ^ 4) ≤
          Pifloor BS e0 BS.k0 := by
  obtain ⟨K1, hraw⟩ := Pifloor_density_raw_lower e0 he0
  refine ⟨K1, 1 / (2 ^ 20 * (Real.log (2 : ℝ)) ^ 4), ?_, ?_⟩
  · positivity
  · intro BS hK hadm
    have hrawBS := hraw BS hK hadm
    have hk0posNat : 1 ≤ BS.k0 := BS.hk0
    have hk0pos : 0 < (BS.k0 : ℝ) := by exact_mod_cast hk0posNat
    have hk1pos : 0 < ((BS.k0 + 1 : ℕ) : ℝ) := by positivity
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
    have hpoly :
        ((BS.k0 : ℝ) + 1) * (BS.k0 : ℝ) ^ 3 ≤ ((BS.k0 : ℝ) + 1) ^ 4 := by
      have hk0le : (BS.k0 : ℝ) ≤ (BS.k0 : ℝ) + 1 := by linarith
      have hpowle : (BS.k0 : ℝ) ^ 3 ≤ ((BS.k0 : ℝ) + 1) ^ 3 :=
        pow_le_pow_left₀ hk0pos.le hk0le 3
      calc
        ((BS.k0 : ℝ) + 1) * (BS.k0 : ℝ) ^ 3
            ≤ ((BS.k0 : ℝ) + 1) * ((BS.k0 : ℝ) + 1) ^ 3 := by
              exact mul_le_mul_of_nonneg_left hpowle (by positivity)
        _ = ((BS.k0 : ℝ) + 1) ^ 4 := by ring
    have hmodel_raw :
        (1 / (2 ^ 20 * (Real.log (2 : ℝ)) ^ 4)) *
            ((2 : ℝ) ^ (2 * BS.k0)) / (((BS.k0 : ℝ) + 1) ^ 4) ≤
          ((2 : ℝ) ^ (BS.k0 + 1) /
              (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))) *
            (((2 : ℝ) ^ BS.k0 /
              (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)))) ^ 3) /
            (2 ^ 13 * ((2 : ℝ) ^ BS.k0) ^ 2) := by
      have hnumpos : 0 < (2 : ℝ) ^ (2 * BS.k0) := by positivity
      have hden_model_pos :
          0 < 2 ^ 20 * (Real.log (2 : ℝ)) ^ 4 * (((BS.k0 : ℝ) + 1) ^ 4) := by
        positivity
      have hden_raw_pos :
          0 <
            2 ^ 20 * (Real.log (2 : ℝ)) ^ 4 *
              (((BS.k0 : ℝ) + 1) * (BS.k0 : ℝ) ^ 3) := by
        positivity
      have hden_le :
          2 ^ 20 * (Real.log (2 : ℝ)) ^ 4 *
              (((BS.k0 : ℝ) + 1) * (BS.k0 : ℝ) ^ 3) ≤
            2 ^ 20 * (Real.log (2 : ℝ)) ^ 4 * (((BS.k0 : ℝ) + 1) ^ 4) := by
        gcongr
      calc
        (1 / (2 ^ 20 * (Real.log (2 : ℝ)) ^ 4)) *
            ((2 : ℝ) ^ (2 * BS.k0)) / (((BS.k0 : ℝ) + 1) ^ 4)
            =
          ((2 : ℝ) ^ (2 * BS.k0)) /
            (2 ^ 20 * (Real.log (2 : ℝ)) ^ 4 * (((BS.k0 : ℝ) + 1) ^ 4)) := by
              field_simp [ne_of_gt hlog2pos, ne_of_gt (by positivity :
                0 < ((BS.k0 : ℝ) + 1) ^ 4)]
        _ ≤
          ((2 : ℝ) ^ (2 * BS.k0)) /
            (2 ^ 20 * (Real.log (2 : ℝ)) ^ 4 *
              (((BS.k0 : ℝ) + 1) * (BS.k0 : ℝ) ^ 3)) := by
              exact div_le_div_of_nonneg_left hnumpos.le hden_raw_pos hden_le
        _ =
          ((2 : ℝ) ^ (BS.k0 + 1) /
              (4 * (((BS.k0 + 1 : ℕ) : ℝ) * Real.log (2 : ℝ)))) *
            (((2 : ℝ) ^ BS.k0 /
              (4 * ((BS.k0 : ℝ) * Real.log (2 : ℝ)))) ^ 3) /
            (2 ^ 13 * ((2 : ℝ) ^ BS.k0) ^ 2) := by
              field_simp [ne_of_gt hk0pos, ne_of_gt hk1pos, ne_of_gt hlog2pos,
                ne_of_gt (by positivity : 0 < (2 : ℝ) ^ BS.k0)]
              rw [show (2 : ℝ) ^ (2 * BS.k0) = ((2 : ℝ) ^ BS.k0) ^ 2 by
                rw [mul_comm 2 BS.k0, pow_mul]]
              rw [pow_succ]
              norm_num [Nat.cast_add, Nat.cast_one]
              ring
    exact le_trans hmodel_raw hrawBS

end GlobalControl

end
