/-
  SemiprimeInfinity.lean

  Proves that for any finite set T of natural numbers, there exist
  semiprimes not in T. In fact, there are infinitely many semiprimes,
  and for any b, infinitely many semiprimes coprime to b.

  This supports the edge construction (Lemma 9.1): the free initial-scale
  parameter k₀ can be chosen large enough to avoid any finite set.
-/
import Mathlib
import RequestProject.Core.Semiprime

open Finset BigOperators

/-- There exist infinitely many primes (Euclid). This is in Mathlib. -/
example : ∀ N : ℕ, ∃ p, N ≤ p ∧ Nat.Prime p := Nat.exists_infinite_primes

/-
For any N, there exist two distinct primes both greater than N.
-/
theorem exists_two_primes_gt (N : ℕ) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ N < p := by
  rcases Nat.exists_infinite_primes ( N + 1 ) with ⟨ p, hp ⟩ ; rcases Nat.exists_infinite_primes ( p + 1 ) with ⟨ q, hq ⟩ ; use p, q ; aesop;

/-
For any N, there exists a semiprime greater than N.
-/
theorem exists_semiprime_gt (N : ℕ) : ∃ n > N, IsSemiprime n := by
  obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_infinite_primes ( N + 2 );
  obtain ⟨ q, hq₁, hq₂ ⟩ := Nat.exists_infinite_primes ( p + 1 ) ; exact ⟨ p * q, by nlinarith, ⟨ p, q, hp₂, hq₂, by linarith, by ring ⟩ ⟩ ;

/-
For any finite set T, there exists a semiprime not in T.
-/
theorem exists_semiprime_not_in (T : Finset ℕ) :
    ∃ n, IsSemiprime n ∧ n ∉ T := by
  -- By the previous theorem, there exists a semiprime n greater than the maximum element of T.
  obtain ⟨n, hn⟩ : ∃ n, IsSemiprime n ∧ T.sup id < n := by
    obtain ⟨ n, hn ⟩ := exists_semiprime_gt ( T.sup id );
    tauto;
  exact ⟨ n, hn.1, fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) hn.2 ⟩

/-
For any b and any finite set T, there exists a semiprime coprime to b
    and not in T. This is the key ingredient for the edge construction:
    we can always find fresh semiprimes to use as denominators.
-/
theorem exists_semiprime_coprime_not_in (b : ℕ) (hb : 0 < b) (T : Finset ℕ) :
    ∃ n, IsSemiprime n ∧ Nat.Coprime n b ∧ n ∉ T := by
  obtain ⟨p, hp⟩ : ∃ p, Nat.Prime p ∧ p > b ∧ p > T.sup id := by
    have := Nat.exists_infinite_primes ( Max.max ( b + 1 ) ( T.sup id + 1 ) ) ; aesop;
  obtain ⟨q, hq⟩ : ∃ q, Nat.Prime q ∧ q > p ∧ q > T.sup id := by
    rcases Nat.exists_infinite_primes ( p + 1 ) with ⟨ q, hq ⟩ ; exact ⟨ q, hq.2, by linarith, by linarith ⟩;
  refine' ⟨ p * q, ⟨ p, q, hp.1, hq.1, by linarith, rfl ⟩, _, _ ⟩;
  · exact Nat.Coprime.mul_left ( hp.1.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt hb hp.2.1 ) ( hq.1.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt hb <| by linarith );
  · exact fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) ( by norm_num; nlinarith )
