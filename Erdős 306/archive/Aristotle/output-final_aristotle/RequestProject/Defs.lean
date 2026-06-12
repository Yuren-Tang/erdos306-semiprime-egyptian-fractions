/-
# Basic Definitions for the Conditional Proof of Erdős Problem 306

This file defines the core mathematical objects:
- Squarefree semiprimes
- Egyptian fraction representations
- The necessity of the squarefree denominator condition
-/
import Mathlib

open scoped BigOperators Classical Finset

noncomputable section

/-! ## Semiprimes -/

/-- A natural number is a semiprime if it is the product of exactly two distinct primes. -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p * q

/-
Every semiprime (product of two distinct primes) is squarefree.
-/
lemma IsSemiprime.squarefree {n : ℕ} (h : IsSemiprime n) : Squarefree n := by
  obtain ⟨ p, q, hp, hq, hpq, rfl ⟩ := h;
  rw [ Nat.squarefree_mul_iff ];
  exact ⟨ hp.coprime_iff_not_dvd.mpr fun h => hpq.ne <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h, hp.squarefree, hq.squarefree ⟩

/-
Every semiprime is positive.
-/
lemma IsSemiprime.pos {n : ℕ} (h : IsSemiprime n) : 0 < n := by
  obtain ⟨ p, q, hp, hq, hpq, rfl ⟩ := h; exact Nat.mul_pos hp.pos hq.pos;

/-- Every semiprime, cast to ℚ, is nonzero. -/
lemma IsSemiprime.cast_ne_zero {n : ℕ} (h : IsSemiprime n) : (n : ℚ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (by linarith [h.pos])

/-! ## Egyptian fraction representations -/

/-- There exists a finite set S of distinct squarefree semiprimes such that
    ∑_{n ∈ S} 1/n = r. This is the Prop-valued version. -/
def HasEgyptianSemiprimeRepr (r : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, IsSemiprime n) ∧
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = r

/-! ## Necessity of the squarefree denominator -/

/-
**Remark 1.2 (Necessity of squarefree b).**
If each nᵢ is squarefree, then lcm(n₁,...,nₖ) is squarefree,
and the reduced denominator of ∑ 1/nᵢ divides this lcm,
hence is itself squarefree.

Therefore no rational with non-squarefree denominator admits
an Egyptian fraction representation using squarefree semiprimes.
-/
lemma necessity_squarefree_denom (S : Finset ℕ) (hS : ∀ n ∈ S, Squarefree n)
    (hpos : ∀ n ∈ S, 0 < n) :
    Squarefree (∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den := by
  -- Each semiprime is squarefree, so the denominator of the sum is a divisor of the lcm of the denominators.
  have h_denom_div : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den ∣ (∏ p ∈ Nat.primeFactors (∏ n ∈ S, n), p) := by
    -- The denominator of the sum divides the least common multiple of the denominators.
    have h_denom_div_lcm : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den ∣ Finset.lcm S id := by
      induction' S using Finset.induction with n S hnS ih;
      · norm_num;
      · rw [ Finset.sum_insert hnS ];
        -- The denominator of the sum of two fractions divides the least common multiple of their denominators.
        have h_denom_sum : ∀ (a b : ℚ), (a + b).den ∣ Nat.lcm a.den b.den := by
          exact fun a b => Rat.add_den_dvd_lcm a b;
        refine' dvd_trans ( h_denom_sum _ _ ) _;
        refine' Nat.lcm_dvd _ _;
        · simp +zetaDelta at *;
          exact if_neg hpos.1.ne' ▸ Nat.dvd_lcm_left _ _;
        · exact dvd_trans ( ih ( fun x hx => hS x ( Finset.mem_insert_of_mem hx ) ) ( fun x hx => hpos x ( Finset.mem_insert_of_mem hx ) ) ) ( Finset.lcm_mono ( Finset.subset_insert _ _ ) );
    refine dvd_trans h_denom_div_lcm ?_;
    refine' Finset.lcm_dvd fun n hn => _;
    rw [ ← Nat.prod_primeFactors_of_squarefree ( hS n hn ) ];
    apply_rules [ Finset.prod_dvd_prod_of_subset ];
    exact Nat.primeFactors_mono ( Finset.dvd_prod_of_mem _ hn ) ( Finset.prod_ne_zero_iff.mpr fun x hx => ne_of_gt ( hpos x hx ) );
  -- The product of distinct primes is squarefree.
  have h_prod_squarefree : ∀ {T : Finset ℕ}, (∀ p ∈ T, Nat.Prime p) → Squarefree (∏ p ∈ T, p) := by
    intros T hT; induction T using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
    exact ⟨ Nat.Coprime.prod_right fun p hp => hT.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hT.1 ( hT.2 p hp ) ; aesop, hT.1.squarefree ⟩;
  exact h_prod_squarefree ( fun p hp => Nat.prime_of_mem_primeFactors hp ) |> fun h => h.squarefree_of_dvd h_denom_div

end