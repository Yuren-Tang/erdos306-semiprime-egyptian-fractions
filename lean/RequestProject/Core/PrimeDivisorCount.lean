import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Prime.Fin

/-! Counting large prime divisors of a small nonzero integer. -/

open Finset

namespace RequestProject

/-- If every prime in `S` is at least `B` and `|d| < B ^ 2`, then at most one
member of `S` divides the nonzero integer `d`. -/
theorem card_filter_prime_dvd_le_one (S : Finset ℕ) (B : ℕ) (d : ℤ)
    (hd : d ≠ 0) (hprime : ∀ p ∈ S, p.Prime) (hlower : ∀ p ∈ S, B ≤ p)
    (hsmall : |d| < (B : ℤ) ^ 2) :
    (S.filter fun p => (p : ℤ) ∣ d).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun p hp q hq => ?_
  rw [Finset.mem_filter] at hp hq
  by_contra hpq
  have hcoprime : Nat.Coprime p q := Nat.coprime_primes (hprime p hp.1)
    (hprime q hq.1) hpq
  have hpqdvd : (p * q : ℤ) ∣ d := by
    convert Int.coe_lcm_dvd hp.2 hq.2 using 1
    exact_mod_cast hcoprime.lcm_eq_mul
  have hpq_le : (p * q : ℤ) ≤ |d| :=
    Int.le_of_dvd (abs_pos.mpr hd) (by simpa using hpqdvd)
  have hp_lower : (B : ℤ) ≤ p := by exact_mod_cast hlower p hp.1
  have hq_lower : (B : ℤ) ≤ q := by exact_mod_cast hlower q hq.1
  have hB : (0 : ℤ) ≤ B := by positivity
  nlinarith

end RequestProject
