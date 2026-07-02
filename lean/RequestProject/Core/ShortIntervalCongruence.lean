import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Order.Interval.Finset.Nat

/-! Uniqueness of a residue-class representative in a short interval. -/

open Finset

namespace RequestProject

/-- If the width of `[a, b)` is at most the positive modulus `m`, two members
of the interval whose difference is divisible by `m` are equal. -/
theorem eq_of_dvd_sub_of_mem_Ico
    (a b m x y : ℕ) (hwidth : b ≤ a + m)
    (hx : x ∈ Finset.Ico a b) (hy : y ∈ Finset.Ico a b)
    (hdiv : (m : ℤ) ∣ (x : ℤ) - y) :
    x = y := by
  by_contra hxy
  have hne : (x : ℤ) - y ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hxy)
  have hlower : m ≤ Int.natAbs ((x : ℤ) - y) := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdiv hne
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  rcases le_total x y with hxy' | hyx'
  · rw [Int.natAbs_natCast_sub_natCast_of_le hxy'] at hlower
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hyx'] at hlower
    omega

/-- If the width of `[a, b]` is at most `m` and all members of `S` are
congruent modulo `m`, then `S` has at most two members.  The possible second
member is the right endpoint `b`. -/
theorem card_le_two_of_dvd_sub_of_mem_Icc
    (a b m : ℕ) (S : Finset ℕ) (hwidth : b ≤ a + m)
    (hS : ∀ x ∈ S, x ∈ Finset.Icc a b)
    (hmod : ∀ x ∈ S, ∀ y ∈ S, (m : ℤ) ∣ (x : ℤ) - y) :
    S.card ≤ 2 := by
  have herase : (S.erase b).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    have hxI := Finset.mem_Icc.mp (hS x (Finset.mem_erase.mp hx).2)
    have hyI := Finset.mem_Icc.mp (hS y (Finset.mem_erase.mp hy).2)
    apply eq_of_dvd_sub_of_mem_Ico a b m x y hwidth
    · exact Finset.mem_Ico.mpr ⟨hxI.1,
        lt_of_le_of_ne hxI.2 (Finset.mem_erase.mp hx).1⟩
    · exact Finset.mem_Ico.mpr ⟨hyI.1,
        lt_of_le_of_ne hyI.2 (Finset.mem_erase.mp hy).1⟩
    · exact hmod x (Finset.mem_erase.mp hx).2 y (Finset.mem_erase.mp hy).2
  by_cases hb : b ∈ S
  · rw [← Finset.card_erase_add_one hb]
    omega
  · simpa [Finset.erase_eq_of_notMem hb] using herase.trans (by omega)

end RequestProject
