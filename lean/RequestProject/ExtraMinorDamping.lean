import RequestProject.CircleMethodArcs

open Finset BigOperators

noncomputable section

namespace CircleMethod

/-!
# R2-extra-minor: per-gadget sibling damping (note 50 §4, arithmetic core)

The b-fiber siblings of a main-arc frequency share its block residues but differ
modulo a prime `r ∣ b`.  A gadget edge `r·s` (with `s` a block prime, so the
sibling is still diagonal modulo `s`) then has phase distance bounded below:
`‖h/(rs)‖ ≥ 1/(2r)`.  This is the constant-per-gadget damping; using
`G = O(log C)` such gadgets per prime `r` of `b` beats the `(2C/σ)(b-1)` sibling
count (note 50 §4).  This file proves the arithmetic lower bound.
-/

/-- **Per-gadget sibling damping.**  For distinct primes `r`, `s` and a frequency
`h` that is diagonal modulo `s` (`h ≡ m`, `m` small: `2|m| < s`) but *offset*
modulo `r` (`h ≢ m`), the nearest-integer distance satisfies
`‖h/(rs)‖ ≥ 1/(2r)`. -/
lemma gadget_nndist1_lower (r s : ℕ) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hrs : r ≠ s) (h : ℕ) (m : ℤ)
    (hm_s : (h : ZMod s) = (m : ZMod s)) (hm_r : (h : ZMod r) ≠ (m : ZMod r))
    (hm_small : 2 * |m| < (s : ℤ)) :
    1 / (2 * (r : ℝ)) ≤ GlobalControl.nndist1 ((h : ℝ) / ((r : ℝ) * (s : ℝ))) := by
  have hcop : Nat.Coprime r s := (Nat.coprime_primes hr hs).mpr hrs
  rw [nndist1_eq_crtRepr_div r s hr hs hrs h]
  set M : ℤ := crtRepr r s (h : ZMod r) (h : ZMod s) with hM
  -- M ≡ m (mod s), M ≢ m (mod r)
  have hMs : (M : ZMod s) = (m : ZMod s) := by
    rw [hM, crtRepr_congr_right r s _ _ hcop, hm_s]
  have hMr : (M : ZMod r) ≠ (m : ZMod r) := by
    rw [hM, crtRepr_congr_left r s _ _ hcop]; exact hm_r
  -- s ∣ (M - m), and M ≠ m, so |M - m| ≥ s
  have hdvd : (s : ℤ) ∣ (M - m) := by
    have h0 : ((M - m : ℤ) : ZMod s) = 0 := by push_cast; rw [hMs]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hne : M ≠ m := fun hEq => hMr (by rw [hEq])
  have hMm_ne : M - m ≠ 0 := sub_ne_zero.mpr hne
  have habs_ge : (s : ℤ) ≤ |M - m| :=
    Int.le_of_dvd (abs_pos.mpr hMm_ne) ((dvd_abs _ _).mpr hdvd)
  -- triangle: |M - m| ≤ |M| + |m|, hence s ≤ 2|M|
  have htri : |M - m| ≤ |M| + |m| := abs_sub M m
  have hkey : (s : ℤ) ≤ 2 * |M| := by linarith [habs_ge, htri, hm_small]
  -- cast to ℝ and finish
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs.pos
  have hkeyR : (s : ℝ) ≤ 2 * |(M : ℝ)| := by
    have := hkey
    rw [← Int.cast_abs]
    push_cast at this ⊢
    exact_mod_cast this
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) * (s : ℝ))]
  have hsimp : 1 / (2 * (r : ℝ)) * ((r : ℝ) * (s : ℝ)) = (s : ℝ) / 2 := by
    field_simp
  rw [hsimp]
  linarith [hkeyR]

/-- **Single-gadget damping factor.**  Under the sibling hypotheses, the gadget's
Bernoulli character factor has norm `≤ √(1 − (8/9)/r²) < 1` (a constant `< 1`
depending only on `r`).  Using `G` such gadgets per prime `r ∣ b` gives damping
`(√(1−(8/9)/r²))^G → 0` (note 50 §4). -/
lemma gadget_charFun_damp (r s : ℕ) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hrs : r ≠ s) (θ : ℝ) (hθlb : 1/3 ≤ θ) (hθub : θ ≤ 2/3)
    (h : ℕ) (m : ℤ)
    (hm_s : (h : ZMod s) = (m : ZMod s)) (hm_r : (h : ZMod r) ≠ (m : ZMod r))
    (hm_small : 2 * |m| < (s : ℤ)) :
    ‖bernoulliCharFun θ ((h : ℝ) / ((r : ℝ) * (s : ℝ)))‖
      ≤ Real.sqrt (1 - (8/9) / (r : ℝ)^2) := by
  set t : ℝ := (h : ℝ) / ((r : ℝ) * (s : ℝ)) with ht
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hnd : 1 / (2 * (r : ℝ)) ≤ GlobalControl.nndist1 t :=
    gadget_nndist1_lower r s hr hs hrs h m hm_s hm_r hm_small
  -- sin²(πt) ≥ 1/r²
  have hsin : (1 : ℝ) / (r : ℝ)^2 ≤ Real.sin (Real.pi * t)^2 := by
    have h4 := sin_sq_pi_ge_four_nndist_sq t
    have hnd2 : (1 / (2 * (r : ℝ)))^2 ≤ (GlobalControl.nndist1 t)^2 :=
      pow_le_pow_left₀ (by positivity) hnd 2
    have heq : (1 : ℝ) / (r : ℝ)^2 = 4 * (1 / (2 * (r : ℝ)))^2 := by field_simp; ring
    rw [heq]; nlinarith [h4, hnd2]
  -- normSq ≤ 1 - (8/9)/r²
  have hnsq : Complex.normSq (bernoulliCharFun θ t) ≤ 1 - (8/9) / (r : ℝ)^2 := by
    have hb := bernoulliCharFun_normSq_le (1/3) θ t (by norm_num) (by norm_num)
      hθlb (by linarith)
    have hcoef : 4 * (1/3 : ℝ) * (1 - 1/3) = 8/9 := by norm_num
    rw [hcoef] at hb
    have hscaled : (8/9 : ℝ) * (1/(r : ℝ)^2) ≤ (8/9) * Real.sin (Real.pi * t)^2 :=
      mul_le_mul_of_nonneg_left hsin (by norm_num)
    have hdiv : (8/9 : ℝ) / (r : ℝ)^2 = (8/9) * (1/(r : ℝ)^2) := by ring
    rw [hdiv]; linarith [hb, hscaled]
  -- ‖·‖ = √normSq ≤ √(…)
  rw [Complex.norm_def]
  exact Real.sqrt_le_sqrt hnsq

end CircleMethod

end
