/-
# Circle Method — finite no-wraparound indicator bridge

After the `spectral_existence` cannon (`SpectralCannon.lean`) absorbed the
arc-separation positivity, the finite Fourier identity, and the subset
extraction (see `CannonBridge.lean`), the only piece of this layer still needed
downstream is the **no-wraparound indicator equivalence** `fourier_indicator`:
under the divisibility hypotheses and the bound `∑_E L/e < L`, the divisibility
`L ∣ (∑_{e∈S} L/e − L/b)` is equivalent to the exact reciprocal identity
`∑_{e∈S} 1/e = 1/b`.  It is used by `CannonBridge` to decode a hitting
configuration into an Egyptian representation.
-/
import Mathlib
import RequestProject.Defs

open scoped BigOperators Classical
open Finset

noncomputable section

namespace CircleMethod

/-! ## Fourier identity — the indicator core

Under the no-wraparound hypotheses (`b ≥ 2` and the total mass
`∑_{e∈E} L/e < L`, i.e. `∑ 1/e < 1`), the divisibility
`L ∣ (∑_{e∈S} L/e − L/b)` is equivalent to the exact reciprocal identity
`∑_{e∈S} 1/e = 1/b`.  This is the only piece of the former circle-method
collector still used downstream (by `CannonBridge.decode_subset_sum`). -/

/-- For `e ∣ L` and `0 < e`, the reciprocal `1/e` equals `(L/e)/L` in `ℚ`. -/
lemma one_div_eq_div_of_dvd (e L : ℕ) (he : 0 < e) (hL : 0 < L) (hdvd : e ∣ L) :
    (1 : ℚ) / (e : ℚ) = ((L / e : ℕ) : ℚ) / (L : ℚ) := by
  have hmul : (e : ℕ) * (L / e) = L := Nat.mul_div_cancel' hdvd
  rw [div_eq_div_iff (by exact_mod_cast he.ne' : (e:ℚ) ≠ 0)
    (by exact_mod_cast hL.ne' : (L:ℚ) ≠ 0), one_mul]
  rw [mul_comm]
  exact_mod_cast hmul.symm

/-- **C0 indicator equivalence (no-wraparound).** -/
lemma fourier_indicator (E : Finset ℕ) (b L : ℕ) (hb : 2 ≤ b) (hL : 0 < L)
    (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L) (he0 : ∀ e ∈ E, 0 < e)
    (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (S : Finset ℕ) (hS : S ⊆ E) :
    ((L : ℤ) ∣ ((∑ e ∈ S, ((L / e : ℕ) : ℤ)) - ((L / b : ℕ) : ℤ)))
      ↔ (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / (b : ℚ) := by
  set mS := ∑ e ∈ S, (L / e : ℕ) with hmSdef
  set mb := (L / b : ℕ) with hmbdef
  have hsumcast : (∑ e ∈ S, ((L / e : ℕ) : ℤ)) = (mS : ℤ) := by
    rw [hmSdef, Nat.cast_sum]
  rw [hsumcast]
  have hmS_lt : mS < L := lt_of_le_of_lt (Finset.sum_le_sum_of_subset hS) hbound
  have hmb_lt : mb < L := Nat.div_lt_self hL (by omega)
  -- divisibility ↔ mS = mb
  have hdiv_iff : ((L : ℤ) ∣ ((mS : ℤ) - (mb : ℤ))) ↔ mS = mb := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h
      have hkabs : |(mS : ℤ) - (mb : ℤ)| < (L : ℤ) := by
        have h1 : (mS : ℤ) < L := by exact_mod_cast hmS_lt
        have h2 : (mb : ℤ) < L := by exact_mod_cast hmb_lt
        have h3 : (0 : ℤ) ≤ mS := Int.natCast_nonneg _
        have h4 : (0 : ℤ) ≤ mb := Int.natCast_nonneg _
        rw [abs_lt]; omega
      rw [hk, abs_mul] at hkabs
      have hLpos : (0 : ℤ) < L := by exact_mod_cast hL
      have hk0 : k = 0 := by
        rcases eq_or_ne k 0 with h | h
        · exact h
        · exfalso
          have hLabs : |(L : ℤ)| = L := abs_of_pos hLpos
          rw [hLabs] at hkabs
          have hk1 : (1 : ℤ) ≤ |k| := Int.one_le_abs h
          nlinarith [mul_le_mul_of_nonneg_left hk1 hLpos.le, hkabs]
      rw [hk0, mul_zero, sub_eq_zero] at hk
      exact_mod_cast hk
    · intro h; rw [h, sub_self]; exact dvd_zero _
  rw [hdiv_iff]
  -- ℚ bridge
  have hqS : (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (mS : ℚ) / (L : ℚ) := by
    rw [hmSdef]; push_cast [Finset.sum_div]
    exact Finset.sum_congr rfl (fun e he =>
      one_div_eq_div_of_dvd e L (he0 e (hS he)) hL (heL e (hS he)))
  have hqb : (1 : ℚ) / (b : ℚ) = (mb : ℚ) / (L : ℚ) :=
    one_div_eq_div_of_dvd b L (by omega) hL hbL
  have hLne : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [hqS, hqb, div_eq_div_iff hLne hLne]
  constructor
  · intro h; rw [h]
  · intro h; exact_mod_cast mul_right_cancel₀ hLne h

end CircleMethod

end
