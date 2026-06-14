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
    rw [hM, crtRepr_congr_right r s _ _ hcop hr.pos hs.pos, hm_s]
  have hMr : (M : ZMod r) ≠ (m : ZMod r) := by
    rw [hM, crtRepr_congr_left r s _ _ hcop hr.pos hs.pos]; exact hm_r
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

end CircleMethod

end
