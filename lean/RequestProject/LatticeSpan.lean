/-
  LatticeSpan.lean

  **Lemma 10.1 (Lattice-span gadget)** from the Erdős 306 conditional proof.

  If P is a finite set of primes, L = ∏ P, E is a nonempty finite set of
  positive divisors of L, and every prime in P divides at least one element
  of E, then gcd{L/e : e ∈ E} = 1.
-/
import Mathlib

open Finset BigOperators

/-
The product of a finite set of distinct primes is squarefree.
-/
theorem prod_primes_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (P.prod id) := by
  induction P using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ];
  exact ⟨ Nat.Coprime.prod_right fun x hx => hP.1.coprime_iff_not_dvd.2 fun h => by have := Nat.prime_dvd_prime_iff_eq hP.1 ( hP.2 x hx ) ; aesop, hP.1.squarefree ⟩

/-
If L is squarefree, e ∣ L, e > 0, p is prime, and p ∣ e, then p ∤ L / e.
-/
theorem prime_not_dvd_quot_of_dvd_squarefree
    (L e p : ℕ) (hL : Squarefree L) (he : e ∣ L)
    (hp : Nat.Prime p) (hpe : p ∣ e) : ¬ (p ∣ L / e) := by
  exact fun h => absurd ( hL p ( by exact Nat.dvd_trans ( by exact Nat.mul_dvd_mul hpe h ) ( by rw [Nat.mul_div_cancel' he] ) ) ) ( by aesop )

/-
**Lemma 10.1 (Lattice-span gadget).**
If `P` is a finite set of primes, `L = ∏ P`, `E` is a nonempty finite set
of positive divisors of `L`, and every prime in `P` divides at least one
element of `E`, then `Finset.gcd E (fun e => L / e) = 1`.

This ensures there is no lattice-period obstruction in Fourier inversion.
-/
theorem lattice_span_gcd_eq_one
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (E : Finset ℕ) (hEne : E.Nonempty)
    (hEdvd : ∀ e ∈ E, e ∣ P.prod id)
    (_hEpos : ∀ e ∈ E, 0 < e)
    (hcover : ∀ p ∈ P, ∃ e ∈ E, p ∣ e) :
    E.gcd (fun e => P.prod id / e) = 1 := by
  -- By contradiction, assume there exists a prime $d$ that divides the gcd of the set $\{L/e \mid e \in E\}$.
  by_contra h_contra
  obtain ⟨d, hd_prime, hd_div⟩ : ∃ d, Nat.Prime d ∧ ∀ e ∈ E, d ∣ P.prod id / e := by
    exact Nat.exists_prime_and_dvd h_contra |> fun ⟨ d, hd₁, hd₂ ⟩ => ⟨ d, hd₁, fun e he => dvd_trans hd₂ <| Finset.gcd_dvd he ⟩;
  obtain ⟨ e, he, he' ⟩ := hcover d (by
  have hd_div_prod : d ∣ P.prod id := by
    exact dvd_trans ( hd_div _ hEne.choose_spec ) ( Nat.div_dvd_of_dvd ( hEdvd _ hEne.choose_spec ) );
  simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ];
  exact not_not.mp fun h => hd_div_prod <| Nat.Coprime.prod_right fun p hp => hd_prime.coprime_iff_not_dvd.mpr fun hpd => h <| by have := Nat.prime_dvd_prime_iff_eq hd_prime ( hP p hp ) ; aesop;);
  exact prime_not_dvd_quot_of_dvd_squarefree _ _ _ ( prod_primes_squarefree _ hP ) ( hEdvd _ he ) hd_prime he' ( hd_div _ he )