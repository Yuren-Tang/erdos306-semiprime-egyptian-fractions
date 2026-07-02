import RequestProject.Core.EgyptianRepresentation
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

open scoped BigOperators Classical Finset

noncomputable section

/-- The denominator of a finite sum of reciprocals of positive squarefree
integers is squarefree. -/
lemma necessity_squarefree_denom (S : Finset ℕ) (hS : ∀ n ∈ S, Squarefree n)
    (hpos : ∀ n ∈ S, 0 < n) :
    Squarefree (∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den := by
  have h_denom_div : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den ∣
      (∏ p ∈ Nat.primeFactors (∏ n ∈ S, n), p) := by
    have h_denom_div_lcm : (∑ n ∈ S, (1 : ℚ) / (n : ℚ)).den ∣ Finset.lcm S id := by
      induction' S using Finset.induction with n S hnS ih
      · norm_num
      · rw [Finset.sum_insert hnS]
        have h_denom_sum : ∀ (a b : ℚ), (a + b).den ∣ Nat.lcm a.den b.den :=
          fun a b => Rat.add_den_dvd_lcm a b
        refine dvd_trans (h_denom_sum _ _) ?_
        refine Nat.lcm_dvd ?_ ?_
        · simp +zetaDelta at *
          exact if_neg hpos.1.ne' ▸ Nat.dvd_lcm_left _ _
        · exact dvd_trans
            (ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
              (fun x hx => hpos x (Finset.mem_insert_of_mem hx)))
            (Finset.lcm_mono (Finset.subset_insert _ _))
    refine dvd_trans h_denom_div_lcm ?_
    refine Finset.lcm_dvd fun n hn => ?_
    rw [← Nat.prod_primeFactors_of_squarefree (hS n hn)]
    apply_rules [Finset.prod_dvd_prod_of_subset]
    exact Nat.primeFactors_mono (Finset.dvd_prod_of_mem _ hn)
      (Finset.prod_ne_zero_iff.mpr fun x hx => ne_of_gt (hpos x hx))
  have h_prod_squarefree : ∀ {T : Finset ℕ},
      (∀ p ∈ T, Nat.Prime p) → Squarefree (∏ p ∈ T, p) := by
    intros T hT
    induction T using Finset.induction <;> simp_all +decide [Nat.squarefree_mul_iff]
    exact ⟨Nat.Coprime.prod_right fun p hp =>
        hT.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by
          have := Nat.prime_dvd_prime_iff_eq hT.1 (hT.2 p hp)
          aesop,
      hT.1.squarefree⟩
  exact (h_prod_squarefree fun p hp => Nat.prime_of_mem_primeFactors hp).squarefree_of_dvd
    h_denom_div

end
