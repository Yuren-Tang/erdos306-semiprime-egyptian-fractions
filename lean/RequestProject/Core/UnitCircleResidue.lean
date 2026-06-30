import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Data.ZMod.ValMinAbs

/-! The canonical centered representative of a rational point on `ℝ / ℤ`. -/

namespace RequestProject

/-- The norm of `n / q` on the unit circle is the absolute value of the
centered representative of `n mod q`, divided by `q`. -/
theorem unitCircle_norm_int_div_nat
    (n : ℤ) (q : ℕ) (hq : 0 < q) :
    ‖(((n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ =
      |(((n : ZMod q).valMinAbs : ℝ) / (q : ℝ))| := by
  letI : NeZero q := ⟨hq.ne'⟩
  let r : ℤ := (n : ZMod q).valMinAbs
  have hr : (r : ZMod q) = n := by
    exact ZMod.coe_valMinAbs (n : ZMod q)
  calc
    ‖(((n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ =
        ‖ZMod.toAddCircle (n : ZMod q)‖ := by
          rw [ZMod.toAddCircle_intCast]
    _ = ‖(((r : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ := by
          rw [← ZMod.toAddCircle_intCast, hr]
    _ = |((r : ℝ) / (q : ℝ))| := by
      apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).2
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hrange := ZMod.valMinAbs_mem_Ioc (n : ZMod q)
      have hrange' : -(q : ℤ) < 2 * r ∧ 2 * r ≤ q := by
        simpa [Set.mem_Ioc, r, mul_comm] using hrange
      have hrangeR : -(q : ℝ) < 2 * (r : ℝ) ∧ 2 * (r : ℝ) ≤ q := by
        exact_mod_cast hrange'
      have hrabs : |(r : ℝ)| ≤ (q : ℝ) / 2 := by
        rw [abs_le]
        constructor <;> linarith [hrangeR.1, hrangeR.2]
      rw [abs_div, abs_of_pos hqR, abs_one, div_le_iff₀ hqR]
      linarith
    _ = |(((n : ZMod q).valMinAbs : ℝ) / (q : ℝ))| := rfl

/-- A small unit-circle norm supplies the canonical centered residue, with a
matching size bound and congruence. -/
theorem exists_centered_residue_of_unitCircle_norm_le
    (n : ℤ) (q : ℕ) (hq : 0 < q) (delta : ℝ)
    (hdelta : ‖(((n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ ≤ delta) :
    ∃ r : ℤ, |(r : ℝ)| ≤ delta * q ∧ (q : ℤ) ∣ n - r := by
  letI : NeZero q := ⟨hq.ne'⟩
  let r : ℤ := (n : ZMod q).valMinAbs
  refine ⟨r, ?_, ?_⟩
  · rw [unitCircle_norm_int_div_nat n q hq] at hdelta
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [abs_div, abs_of_pos hqR, div_le_iff₀ hqR] at hdelta
    simpa [r, mul_comm] using hdelta
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, ZMod.coe_valMinAbs]
    simp

/-- If `q` does not divide `n`, the distance of `n / q` to the nearest integer
is at least `1 / q`. -/
theorem inv_natCast_le_unitCircle_norm_int_div_nat
    (q : ℕ) (hq : 0 < q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    1 / (q : ℝ) ≤ ‖(((n : ℝ) / (q : ℝ) : ℝ) : UnitAddCircle)‖ := by
  rw [unitCircle_norm_int_div_nat n q hq]
  letI : NeZero q := ⟨hq.ne'⟩
  have hres : (n : ZMod q).valMinAbs ≠ 0 := by
    intro h
    apply hn
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.coe_valMinAbs (n : ZMod q), h]
    simp
  rw [abs_div, abs_of_pos (by exact_mod_cast hq)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Int.one_le_abs hres)
    (by positivity)

/-- Distance to the nearest integer is bounded by absolute value. -/
theorem unitCircle_norm_coe_le_abs (x : ℝ) :
    ‖(x : UnitAddCircle)‖ ≤ |x| := by
  rw [UnitAddCircle.norm_eq]
  simpa using round_le x 0

/-- The unit-circle norm is invariant under translation by an integer. -/
@[simp] theorem unitCircle_norm_add_intCast (x : ℝ) (n : ℤ) :
    ‖((x + (n : ℝ) : ℝ) : UnitAddCircle)‖ = ‖(x : UnitAddCircle)‖ := by
  simp

end RequestProject
