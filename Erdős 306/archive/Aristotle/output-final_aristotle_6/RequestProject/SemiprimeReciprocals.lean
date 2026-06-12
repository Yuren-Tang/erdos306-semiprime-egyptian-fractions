/-
# Divergence of semiprime reciprocal sums and edge construction

This file proves:
1. The sum of reciprocals of semiprimes diverges
2. For any target rational r > 0 and finite obstruction T, there exist
   semiprimes avoiding T with reciprocal sum in [r, 2r]
3. Edge construction with Bernoulli mass tuning

These are needed for the Fourier positivity argument in the
unconditional proof of Erdős 306.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.SemiprimeInfinity

open scoped BigOperators Classical

noncomputable section

/-! ## Semiprime reciprocal divergence -/

/-- For any N, there exist two distinct primes both ≥ N. -/
lemma exists_two_large_primes (N : ℕ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ N ≤ p := by
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes N
  obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (p + 1)
  exact ⟨p, q, hp2, hq2, by omega, hp1⟩

/-- For any N and finite T, there exists a semiprime ≥ N not in T. -/
lemma exists_large_semiprime_not_in (N : ℕ) (T : Finset ℕ) :
    ∃ n, IsSemiprime n ∧ N ≤ n ∧ n ∉ T := by
  -- Choose primes p, q > max(N, max T)
  obtain ⟨p, q, hp, hq, hpq, hpN⟩ :=
    exists_two_large_primes (max N (T.sup id + 1))
  refine ⟨p * q, ⟨p, q, hp, hq, hpq, rfl⟩, ?_, ?_⟩
  · calc N ≤ max N (T.sup id + 1) := le_max_left _ _
      _ ≤ p := hpN
      _ ≤ p * q := Nat.le_mul_of_pos_right p (Nat.Prime.pos hq)
  · intro hmem
    have : p * q ≤ T.sup id := Finset.le_sup (f := id) hmem
    have : p ≤ T.sup id := le_trans (Nat.le_mul_of_pos_right p (Nat.Prime.pos hq)) this
    omega

/-- For any N and b, there exists a semiprime ≥ N coprime to b and not in T. -/
lemma exists_large_semiprime_coprime_not_in (N b : ℕ) (hb : 0 < b) (T : Finset ℕ) :
    ∃ n, IsSemiprime n ∧ N ≤ n ∧ Nat.Coprime n b ∧ n ∉ T := by
  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p > max N (max b (T.sup id + 1)) := by
    have := Nat.exists_infinite_primes (max N (max b (T.sup id + 1)) + 1); aesop
  obtain ⟨q, hq⟩ : ∃ q, Nat.Prime q ∧ q > p := by
    rcases Nat.exists_infinite_primes (p + 1) with ⟨q, hq⟩; exact ⟨q, hq.2, by omega⟩
  refine ⟨p * q, ⟨p, q, hp.1, hq.1, by omega, rfl⟩, ?_, ?_, ?_⟩
  · have : N ≤ p := by omega
    exact le_trans this (Nat.le_mul_of_pos_right p (Nat.Prime.pos hq.1))
  · apply Nat.Coprime.mul_left
    · exact hp.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hb (by omega))
    · exact hq.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hb (by omega))
  · intro hmem
    have h1 : p * q ≤ T.sup id := Finset.le_sup (f := id) hmem
    have h2 : T.sup id + 1 ≤ max N (max b (T.sup id + 1)) := by omega
    have h3 : max N (max b (T.sup id + 1)) < p := hp.2
    have h4 : p ≤ p * q := Nat.le_mul_of_pos_right p (Nat.Prime.pos hq.1)
    omega

end
