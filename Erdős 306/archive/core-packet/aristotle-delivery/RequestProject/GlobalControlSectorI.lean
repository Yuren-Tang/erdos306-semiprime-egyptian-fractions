import RequestProject.GlobalControl
import RequestProject.GlobalControlG6

open Finset BigOperators Classical
open Filter Topology

noncomputable section

namespace GlobalControl

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

/-- `Rw c2 k / (k+1) → ∞`, via comparison with `2^k/(k+1)^4`. -/
lemma Rw_div_linear_tendsto
    (c2 : ℝ) (hc2 : 0 < c2) :
    Filter.Tendsto (fun k : ℕ => Rw c2 k / ((k : ℝ) + 1))
      Filter.atTop Filter.atTop := by
  refine tendsto_atTop_mono' Filter.atTop ?_
    (exp1_model_div_succ_pow_tendsto c2 hc2)
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

/-!
# G7 Sector I absorption

This file is downstream-only.  It isolates the sector-I Laplace absorption
above the global control floor, with the corrected level-set hypothesis carrying
the fixed `exp(A * numBlocks BS)` factor.
-/


/-- For a `Fintype` index and a decidable predicate, the subtype `tsum` is the
filtered finite sum. -/
lemma sectorI_fintype_subtype_tsum_eq {α : Type*} [Fintype α] (S : α → Prop)
    [DecidablePred S] (f : α → ℝ) :
    ∑' a : {x // S x}, f a.1 = ∑ a ∈ Finset.univ.filter S, f a := by
  classical
  rw [tsum_fintype]
  exact (Finset.sum_subtype (Finset.univ.filter S) (by intro x; simp) f).symm

/-- Convert the `Set.ncard` level-set hypothesis to the finite-filter form used
by `SBEEAssembly.partfun_series_bound`. -/
lemma sectorI_global_levelset_finset_bound
    (Cglob eps : ℝ) (BS : BlockSystem)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∀ R : ℝ, 1 ≤ R →
      ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS) := by
  intro R hR
  classical
  have hcard :
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) =
        ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset_setOf]
  simpa [hcard] using hlevel R hR

/-- Step A: full Laplace bound at exponent `c'`. -/
lemma sectorI_full_laplace_bound
    (c' eps A : ℝ) (hc' : 0 < c') (heps0 : 0 ≤ 8 * eps)
    (hepsc' : 8 * eps < c') (BS : BlockSystem) (hσ : 0 < sigmaCtrl BS)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∑ a : GlobalAssignment BS, Real.exp (-c' * Qctrl BS a) ≤
      Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps) /
        (1 - Real.exp (-(c' - 8 * eps))) ^ 2 *
        (1 + 1 / sigmaCtrl BS) := by
  exact SBEEAssembly.partfun_series_bound
    (fun a : GlobalAssignment BS => Qctrl BS a)
    (fun a => Qctrl_nonneg BS a)
    c' (8 * eps) (Real.exp (A * (numBlocks BS : ℝ))) (sigmaCtrl BS)
    hc' heps0 hepsc' (Real.exp_pos _).le hσ
    (sectorI_global_levelset_finset_bound
      (Real.exp (A * (numBlocks BS : ℝ))) eps BS hlevel)

lemma density_card_ge
    (e0 : ℝ) :
    ∃ K1 : ℕ, ∀ (BS : BlockSystem), K1 ≤ BS.k0 → admissibleGlobalRange BS →
      4 * (e0 + 1) ≤ ((BS.P BS.k0).card : ℝ) ∧
      4 * (e0 + 1) ≤ ((BS.P (BS.k0 + 1)).card : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  have htend :
      Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / (k : ℝ)) Filter.atTop Filter.atTop :=
    by simpa using geom_div_pow_tendsto 2 one_lt_two 1
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

lemma sub_half {e0 N : ℝ} (he0 : 0 < e0) (hN : 4 * (e0 + 1) ≤ N) :
    N / 2 ≤ N - e0 ∧ N / 2 ≤ N - e0 - 1 := by
  constructor <;> linarith

lemma Pifloor_density_raw_lower
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

/-- The remaining prime-density lower bound for `Pifloor`.

This is the density chain from `BS.hdensity` at `k₀` and `k₀+1`: after discarding
the fixed exception budget, `Pifloor` is still bounded below by an
exponential-over-polynomial term, uniformly over admissible block systems.

`sorry` reason: this is exactly the `Pifloor` density chain requested in
`CODEX_TASK_pifloor_density.md`, using `BS.hdensity` at `k₀` and `k₀+1`. -/
lemma Pifloor_exp_poly_lower
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

/-- `Rw c2 k` eventually beats every affine function of `k`. -/
lemma Rw_affine_lower
    (c2 : ℝ) (hc2 : 0 < c2) :
    ∀ (β A V : ℝ), 0 < β → 0 < A →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (A * (2 * (k : ℝ) + 1) + V) / β ≤ Rw c2 k := by
  intro β A V hβ hA
  obtain ⟨M, hM⟩ := affine_div_le_linear_multiple β A V hβ hA
  obtain ⟨K, hK⟩ :=
    beats_affine_of_tendsto (fun k : ℕ => Rw c2 k)
      (Rw_div_linear_tendsto c2 hc2) M
  exact ⟨K, fun k hk => le_trans (hM k) (hK k hk)⟩

/-- The model lower bound `c0 * 2^(2k)/(k+1)^4` eventually beats every affine
function of `k`. -/
lemma exp2_affine_lower
    (c0 : ℝ) (hc0 : 0 < c0) :
    ∀ (β A V : ℝ), 0 < β → 0 < A →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      (A * (2 * (k : ℝ) + 1) + V) / β ≤
        c0 * ((2 : ℝ) ^ (2 * k)) / (((k : ℝ) + 1) ^ 4) := by
  intro β A V hβ hA
  obtain ⟨M, hM⟩ := affine_div_le_linear_multiple β A V hβ hA
  obtain ⟨K, hK⟩ :=
    beats_affine_of_tendsto
      (fun k : ℕ =>
        c0 * ((2 : ℝ) ^ (2 * k)) / (((k : ℝ) + 1) ^ 4))
      (exp2_model_div_linear_tendsto c0 hc0) M
  exact ⟨K, fun k hk => le_trans (hM k) (hK k hk)⟩

/-- The remaining floor-growth input for Sector I.

This is the density-driven lower bound requested in `CODEX_TASK_pifloor.md`,
packaged in the affine form actually consumed by the absorption arithmetic:
eventually the global floor beats any prescribed affine function of `k₀`.

The only unproved density input used below is `Pifloor_exp_poly_lower`. -/
lemma Pifloor_density_lower
    (c2 e0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ (β A V : ℝ), 0 < β → 0 < A →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
        (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤
          globalControlFloor BS c2 e0 := by
  intro β A V hβ hA
  obtain ⟨KRw, hRw⟩ := Rw_affine_lower c2 hc2 β A V hβ hA
  obtain ⟨KPi0, c0, hc0, hPiLower⟩ := Pifloor_exp_poly_lower e0 he0
  obtain ⟨KPi1, hPi1⟩ := exp2_affine_lower c0 hc0 β A V hβ hA
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

/-- The floor-growth input for Sector I.

For `cbar = (8*eps+c)/2` and
`K0 = exp(8eps)/(1-exp(-(cbar-8eps)))^2`, the global control floor eventually
absorbs the fixed block-count factor and the Laplace prefactor. -/
theorem Pifloor_superlinear
    (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
    (heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
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
    Pifloor_density_lower c2 e0 hc2 he0 β A V hβ_pos hA
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

theorem sectorI_floor_growth_absorption
    (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
    (heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
    (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ η : ℝ, 0 < η →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      0 < sigmaCtrl BS →
      (∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
            (1 + Real.sqrt R / sigmaCtrl BS)) →
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1) ≤ η / sigmaCtrl BS := by
  intro η hη
  classical
  set cbar : ℝ := (8 * eps + c) / 2 with hcbar_def
  set K0 : ℝ := Real.exp (8 * eps) /
    (1 - Real.exp (-(cbar - 8 * eps))) ^ 2 with hK0_def
  obtain ⟨k0grow, hgrow⟩ :=
    Pifloor_superlinear c hc eps A c2 e0 heps hepsc hA hc2 he0 η hη
  refine ⟨max 2 k0grow, ?_⟩
  intro BS hk0 hadm hσ hlevel
  have hk0two : 2 ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  have hk0grow : k0grow ≤ BS.k0 := le_trans (le_max_right _ _) hk0
  have hσle : sigmaCtrl BS ≤ 1 := sigmaCtrl_le_one BS hk0two
  have hcbar_pos : 0 < cbar := by
    rw [hcbar_def]
    nlinarith [heps, hc]
  have h8cbar : 8 * eps < cbar := by
    rw [hcbar_def]
    nlinarith [hepsc]
  have hcbarc : cbar < c := by
    rw [hcbar_def]
    nlinarith [hepsc]
  have hdpos : 0 < c - cbar := sub_pos.mpr hcbarc
  have h8eps_nonneg : 0 ≤ 8 * eps := by nlinarith [heps]
  have hlap := sectorI_full_laplace_bound cbar eps A hcbar_pos h8eps_nonneg
    h8cbar BS hσ hlevel
  have hgrowBS :
      Real.exp
            (A * (numBlocks BS : ℝ) -
              (c - (8 * eps + c) / 2) * globalControlFloor BS c2 e0) *
          (2 *
            (Real.exp (8 * eps) /
              (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2)) ≤ η :=
    hgrow BS hk0grow hadm
  have hgrowBS' :
      Real.exp
            (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
          (2 * K0) ≤ η := by
    simpa [hcbar_def, hK0_def] using hgrowBS
  have htail :
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)
        ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
          ∑ a : GlobalAssignment BS, Real.exp (-cbar * Qctrl BS a) := by
    rw [sectorI_fintype_subtype_tsum_eq
      (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a)
      (fun a => Real.exp (-c * Qctrl BS a))]
    calc
      ∑ a ∈ Finset.univ.filter
          (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a),
          Real.exp (-c * Qctrl BS a)
          ≤ ∑ a ∈ Finset.univ.filter
              (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a),
              Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
                Real.exp (-cbar * Qctrl BS a) := by
            refine Finset.sum_le_sum (fun a ha => ?_)
            have hfloor : globalControlFloor BS c2 e0 ≤ Qctrl BS a :=
              (Finset.mem_filter.mp ha).2
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            nlinarith [mul_le_mul_of_nonneg_left hfloor hdpos.le]
        _ = Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              ∑ a ∈ Finset.univ.filter
                (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a),
                Real.exp (-cbar * Qctrl BS a) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              ∑ a : GlobalAssignment BS, Real.exp (-cbar * Qctrl BS a) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun a _ _ => (Real.exp_pos _).le)
  have hsum_bound :
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)
        ≤ Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (1 + 1 / sigmaCtrl BS) := by
    calc
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)
          ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              ∑ a : GlobalAssignment BS, Real.exp (-cbar * Qctrl BS a) := htail
      _ ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
            (Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps) /
              (1 - Real.exp (-(cbar - 8 * eps))) ^ 2 *
              (1 + 1 / sigmaCtrl BS)) := by
          exact mul_le_mul_of_nonneg_left hlap (Real.exp_pos _).le
      _ = (Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              Real.exp (A * (numBlocks BS : ℝ))) *
            K0 * (1 + 1 / sigmaCtrl BS) := by
          rw [hK0_def]
          ring
      _ = Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (1 + 1 / sigmaCtrl BS) := by
          have hexp :
              Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
                  Real.exp (A * (numBlocks BS : ℝ)) =
                Real.exp (A * (numBlocks BS : ℝ) -
                  (c - cbar) * globalControlFloor BS c2 e0) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
  have hσ_factor : 1 + 1 / sigmaCtrl BS ≤ 2 / sigmaCtrl BS := by
    have hle_inv : (1 : ℝ) ≤ 1 / sigmaCtrl BS := by
      rw [le_div_iff₀ hσ]
      simpa using hσle
    calc
      1 + 1 / sigmaCtrl BS ≤ 1 / sigmaCtrl BS + 1 / sigmaCtrl BS :=
        by simpa [add_comm] using add_le_add_left hle_inv (1 / sigmaCtrl BS)
      _ = 2 / sigmaCtrl BS := by ring
  have hK0_nonneg : 0 ≤ K0 := by
    rw [hK0_def]
    exact div_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hcoef_nonneg :
      0 ≤ Real.exp (A * (numBlocks BS : ℝ) -
            (c - cbar) * globalControlFloor BS c2 e0) * K0 :=
    mul_nonneg (Real.exp_pos _).le hK0_nonneg
  calc
    ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
        Real.exp (-c * Qctrl BS a.1)
        ≤ Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (1 + 1 / sigmaCtrl BS) := hsum_bound
    _ ≤ Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (2 / sigmaCtrl BS) := by
        exact mul_le_mul_of_nonneg_left hσ_factor hcoef_nonneg
    _ = (Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            (2 * K0)) / sigmaCtrl BS := by
        ring
    _ ≤ η / sigmaCtrl BS :=
        div_le_div_of_nonneg_right hgrowBS' hσ.le

theorem sectorI_absorption' (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
    (heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
    (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ η : ℝ, 0 < η →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      0 < sigmaCtrl BS →
      (∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
            (1 + Real.sqrt R / sigmaCtrl BS)) →
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1) ≤ η / sigmaCtrl BS := by
  exact sectorI_floor_growth_absorption c hc eps A c2 e0 heps hepsc hA hc2 he0

end GlobalControl

end
