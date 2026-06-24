import RequestProject.Erdos306Final

/-!
# Erdős 306 — alignment with `google-deepmind/formal-conjectures`

This leaf restates Erdős Problem 306 **exactly as in
`FormalConjectures/ErdosProblems/306.lean`** of the
`google-deepmind/formal-conjectures` repository (the proposition that file
states and leaves as `sorry`), and discharges it from our
`erdos_306_unconditional`.

The benefit is external auditability: a reviewer who trusts that community
formulation (it uses Mathlib's `ω`/`Ω` = `ArithmeticFunction.cardDistinctFactors`
/ `cardFactors`) need only check the short bridge below, without unfolding our
project-local `HasEgyptianSemiprimeRepr`.

Source of the problem: P. Erdős and R. Graham, *Old and new problems and results
in combinatorial number theory*, Monographies de L'Enseignement Mathématique
(1980); see also T. F. Bloom, Erdős Problem #306,
https://www.erdosproblems.com/306.
-/

open scoped BigOperators Finset ArithmeticFunction.omega ArithmeticFunction.Omega

namespace Erdos306

/-- A squarefree semiprime `p·q` (`p < q` primes) has exactly two distinct prime
factors and exactly two prime factors with multiplicity: `ω = Ω = 2`. -/
lemma isSemiprime_omega_Omega {x : ℕ} (h : IsSemiprime x) :
    ω x = 2 ∧ Ω x = 2 := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  refine ⟨?_, ?_⟩
  · rw [ArithmeticFunction.cardDistinctFactors_mul ((Nat.coprime_primes hp hq).mpr hpq.ne),
      ArithmeticFunction.cardDistinctFactors_apply_prime hp,
      ArithmeticFunction.cardDistinctFactors_apply_prime hq]
  · rw [ArithmeticFunction.cardFactors_mul hp.pos.ne' hq.pos.ne',
      ArithmeticFunction.cardFactors_apply_prime hp,
      ArithmeticFunction.cardFactors_apply_prime hq]

/-- Every squarefree semiprime is `> 1` (the smallest is `2·3 = 6`). -/
lemma isSemiprime_one_lt {x : ℕ} (h : IsSemiprime x) : 1 < x := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  nlinarith [hp.two_le, hq.two_le]

/-- **Erdős Problem 306, in the `google-deepmind/formal-conjectures` formulation**
(`ErdosProblems/306.lean`).  For every positive rational `q` with squarefree
denominator there is a strictly increasing tuple `1 = n₀ < n₁ < … < n_k` whose
non-initial entries are squarefree semiprimes (`ω = Ω = 2`) with
`q = ∑_{i=1}^{k} 1/nᵢ`.  Proved here from `erdos_306_unconditional`. -/
theorem erdos_306 :
    ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
        (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
        q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) := by
  intro q hq hsf
  -- Write `q = a / b` with `a, b : ℕ`, `b = q.den`.
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  set a : ℕ := q.num.toNat with ha_def
  set b : ℕ := q.den with hb_def
  have ha : 0 < a := by rw [ha_def]; omega
  have hb : 0 < b := by rw [hb_def]; exact q.den_pos
  have hbsf : Squarefree b := hsf
  have hacast : (a : ℚ) = (q.num : ℚ) := by
    rw [ha_def]; exact_mod_cast Int.toNat_of_nonneg hnum.le
  have hqab : (a : ℚ) / (b : ℚ) = q := by
    rw [hacast, hb_def]; exact_mod_cast q.num_div_den
  -- Our unconditional theorem supplies the semiprime set.
  obtain ⟨S, hSsemi, hSsum⟩ := erdos_306_unconditional a b ha hb hbsf
  rw [hqab] at hSsum
  -- `S` is nonempty (the sum is `q > 0`), so `S.card = m + 1`.
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at hSsum; exact absurd hSsum (ne_of_lt hq)
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
    ⟨S.card - 1, by have := Finset.card_pos.mpr hSne; omega⟩
  set g := S.orderEmbOfFin hm with hg_def
  have hg_mem : ∀ j, g j ∈ S := fun j => Finset.orderEmbOfFin_mem S hm j
  refine ⟨m + 1, Fin.cons 1 (fun j => g j), Fin.cons_zero _ _, ?_, ?_, ?_⟩
  · -- StrictMono.
    intro x y hxy
    rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨x', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · exact absurd hxy (lt_irrefl 0)
      · rw [Fin.cons_zero, Fin.cons_succ]
        exact isSemiprime_one_lt (hSsemi _ (hg_mem y'))
    · rcases Fin.eq_zero_or_eq_succ y with rfl | ⟨y', rfl⟩
      · exact absurd hxy (Fin.not_lt_zero _)
      · rw [Fin.cons_succ, Fin.cons_succ]
        exact g.strictMono (Fin.succ_lt_succ_iff.mp hxy)
  · -- `ω = Ω = 2` for the non-initial entries.
    intro i hi
    have hi0 : i ≠ 0 := by
      rw [Finset.mem_Icc] at hi
      rintro rfl
      rw [Fin.le_def, Fin.val_zero, Fin.val_one] at hi
      omega
    obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero hi0
    rw [Fin.cons_succ]
    exact isSemiprime_omega_Omega (hSsemi _ (hg_mem i'))
  · -- The sum equals `q`.
    set n : Fin (m + 1 + 1) → ℕ := Fin.cons 1 (fun j => g j) with hn_def
    have hn0 : n 0 = 1 := by rw [hn_def, Fin.cons_zero]
    have hnsucc : ∀ j : Fin (m + 1), n j.succ = g j := by
      intro j; rw [hn_def, Fin.cons_succ]
    have hSj : ∑ j : Fin (m + 1), (1 : ℚ) / (g j : ℚ) = ∑ x ∈ S, (1 : ℚ) / (x : ℚ) := by
      rw [← Finset.image_orderEmbOfFin_univ S hm,
        Finset.sum_image (fun x _ y _ h => g.injective h)]
    have huniv : ∑ i, (1 : ℚ) / ((n i : ℕ) : ℚ) = 1 + q := by
      rw [Fin.sum_univ_succ]
      simp only [hn0, hnsucc, Nat.cast_one, div_one]
      rw [hSj, hSsum]
    have hmem : ∀ i : Fin (m + 1 + 1),
        i ∈ Finset.Icc (1 : Fin (m + 1 + 1)) (Fin.last (m + 1)) ↔ i ≠ 0 := by
      intro i
      simp only [Finset.mem_Icc, Fin.le_last, and_true]
      constructor
      · rintro h1 rfl
        rw [Fin.le_def, Fin.val_zero, Fin.val_one] at h1; omega
      · intro hi0
        rw [Fin.le_def, Fin.val_one]
        have : i.val ≠ 0 := fun hv => hi0 (Fin.ext hv)
        omega
    have h0notin : (0 : Fin (m + 1 + 1)) ∉
        Finset.Icc (1 : Fin (m + 1 + 1)) (Fin.last (m + 1)) := by
      rw [hmem]; exact fun h => h rfl
    have hunion : insert (0 : Fin (m + 1 + 1))
        (Finset.Icc (1 : Fin (m + 1 + 1)) (Fin.last (m + 1))) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i; rw [Finset.mem_insert, hmem]; exact em (i = 0)
    have hins := Finset.sum_insert (f := fun i => (1 : ℚ) / ((n i : ℕ) : ℚ)) h0notin
    rw [hunion, huniv] at hins
    simp only [hn0, Nat.cast_one, div_one] at hins
    linarith [hins]

-- The axiom audit (`#print axioms erdos_306`) and the structural analytic axiom statements
-- are emitted by `RequestProject.Audit`, which CI runs and gates on.

end Erdos306
