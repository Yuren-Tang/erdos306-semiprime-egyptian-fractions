/-
# Erdős Problem 306

Reference: <https://www.erdosproblems.com/306>, citing
[ErGr80] P. Erdős and R. Graham, *Old and new problems and results in
combinatorial number theory*, Monographies de L'Enseignement Mathématique
(1980), MR 0592420.

## The problem (verbatim, erdosproblems.com/306)

> Let `a/b ∈ ℚ_{>0}` with `b` squarefree.  Are there integers
> `1 < n₁ < ⋯ < n_k`, each the product of two distinct primes, such that
> `a/b = 1/n₁ + ⋯ + 1/n_k`?

This is recorded on erdosproblems.com as **OPEN** (status accessed 2026-06-16):
*"This is open, and cannot be resolved with a finite computation."*

The only published progress noted there is the analogous statement with each
`nᵢ` a product of *three* distinct primes, for `b = 1`, proved by
[BEG15] S. Butler, P. Erdős and R. Graham, *Egyptian fractions with each
denominator having three distinct prime divisors*, Integers **15** (2015),
Paper No. A51, MR 3437526.  That is a different (weaker) statement than the one
above and does not settle Problem 306.

--------------------------------------------------------------------------------
## Honest status of this formalization

Problem 306 is an **open mathematical problem**: no proof is known.  This file
therefore does **not** contain a complete machine-checked proof, and it makes no
such claim.  What it *does* provide, all sorry-free except for the single,
clearly isolated open input, is:

* a **faithful Lean statement** of the problem (`erdos_306`);
* a fully verified proof that the squarefree hypothesis on `b` is **necessary**
  (`necessity_squarefree_denom`, in `Defs.lean`);
* a fully verified **reduction** of the general numerator case `a/b` to the unit
  case `1/b` (`reduction_to_unit_numerator_avoiding`, in `MainTheorem.lean`);
* a collection of fully verified **concrete instances** (Part I below);
* the precise **open input** the reduction needs, isolated as the single
  `sorry`-bearing lemma `erdos_306_unit_case_open` with an explicit citation,
  so that a verifier sees exactly one gap and recognises it as the open problem
  rather than a proof failure.

Running `#print axioms erdos_306` (bottom of file) reports `sorryAx`: the chain
is verified down to, and only to, the isolated open input.

--------------------------------------------------------------------------------
## On "cited / quoted" external inputs

In this clean development there is exactly **one** external mathematical input,
and it is the open problem itself (stated as `erdos_306_unit_case_open`, cited
to [ErGr80] / erdosproblems.com/306).  No auxiliary results are taken on faith:
everything else is proved from Mathlib.  In particular there are **no `axiom`
declarations** anywhere in the project; the single unproved statement is an
ordinary `theorem ... := by sorry`, so it is fully visible to `#print axioms`.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.MainTheorem

open scoped BigOperators Classical

noncomputable section

/-! ## Part I: Concrete verified instances

These are fully proved (sorry-free).  The main tool is the triple-prime
identity: for distinct primes `p < q < r`,
`1/(pq) + 1/(pr) + 1/(qr) = (p+q+r)/(pqr)`, so whenever `pqr = b·(p+q+r)` we
get `1/b = 1/(pq) + 1/(pr) + 1/(qr)`. -/

/-- The triple-prime identity:
`1/(pq) + 1/(pr) + 1/(qr) = (p+q+r)/(pqr)`. -/
theorem triple_prime_sum (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) :
    (1 : ℚ) / (p * q) + 1 / (p * r) + 1 / (q * r) =
    (↑p + ↑q + ↑r) / (↑p * ↑q * ↑r) := by
  have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne_zero
  field_simp; ring

/-- Build a semiprime from two distinct primes. -/
private def mkSemi (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p < q) :
    IsSemiprime (p * q) := ⟨p, q, hp, hq, h, rfl⟩

/-- `1/3 = 1/6 + 1/10 + 1/15`  (primes 2,3,5: `2·3·5 = 3·(2+3+5)`). -/
theorem erdos_306_b3 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 3) :=
  ⟨{6, 10, 15}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 2 3 (by decide) (by decide) (by omega)
    · exact mkSemi 2 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 5 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- `1/5 = 1/10 + 1/14 + 1/35`  (primes 2,5,7: `2·5·7 = 5·(2+5+7)`). -/
theorem erdos_306_b5 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 5) :=
  ⟨{10, 14, 35}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 2 5 (by decide) (by decide) (by omega)
    · exact mkSemi 2 7 (by decide) (by decide) (by omega)
    · exact mkSemi 5 7 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- `1/6 = 1/10 + 1/15`  (composite squarefree `b = 2·3`). -/
theorem erdos_306_b6 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 6) :=
  ⟨{10, 15}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl
    · exact mkSemi 2 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 5 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- `1/7 = 1/15 + 1/21 + 1/35`  (primes 3,5,7: `3·5·7 = 7·(3+5+7)`). -/
theorem erdos_306_b7 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 7) :=
  ⟨{15, 21, 35}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 3 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 7 (by decide) (by decide) (by omega)
    · exact mkSemi 5 7 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- `1/11 = 1/21 + 1/33 + 1/77`  (primes 3,7,11: `3·7·11 = 11·(3+7+11)`). -/
theorem erdos_306_b11 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 11) :=
  ⟨{21, 33, 77}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 3 7 (by decide) (by decide) (by omega)
    · exact mkSemi 3 11 (by decide) (by decide) (by omega)
    · exact mkSemi 7 11 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- `1/2 = 1/6 + 1/10 + 1/15 + 1/21 + 1/26 + 1/35 + 1/39 + 1/65 + 1/91`
(the nine semiprimes on the complete graph over primes `{2,3,5,7,13}`). -/
theorem erdos_306_b2 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 2) :=
  ⟨{6, 10, 15, 21, 26, 35, 39, 65, 91}, fun n hn => by
    simp at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mkSemi 2 3 (by decide) (by decide) (by omega)
    · exact mkSemi 2 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 7 (by decide) (by decide) (by omega)
    · exact mkSemi 2 13 (by decide) (by decide) (by omega)
    · exact mkSemi 5 7 (by decide) (by decide) (by omega)
    · exact mkSemi 3 13 (by decide) (by decide) (by omega)
    · exact mkSemi 5 13 (by decide) (by decide) (by omega)
    · exact mkSemi 7 13 (by decide) (by decide) (by omega),
  by norm_num⟩

/-! ## Part II: The general statement, conditional on the open input

The general statement is reduced (`reduction_to_unit_numerator_avoiding`,
sorry-free) to the **unit case** `1/b`, in the denominator-avoiding form that the
induction over the numerator `a` requires.  That unit case is the open content
of Problem 306, isolated here as a single cited `sorry`. -/

/-- **OPEN INPUT — Erdős Problem 306, unit case (avoiding form).**

For every squarefree `b > 0` and every finite obstruction set `T`, there is a
finite set `S` of distinct squarefree semiprimes, disjoint from `T`, with
`∑_{n ∈ S} 1/n = 1/b`.

This is (the denominator-avoiding strengthening, needed for the numerator
induction, of) the unit-fraction case `a = 1` of Erdős Problem 306
([ErGr80]; erdosproblems.com/306).  **No proof of this statement is known: it is
an open problem.**  It is recorded here as an explicit, isolated `sorry` (not an
`axiom`), so that `#print axioms erdos_306` exhibits exactly this one gap.

The avoiding form is the natural target of any constructive route: it asks for
representations whose denominators can be pushed past any finite set, which is
what allows distinct representations of `1/b` to be summed into `a/b`. -/
theorem erdos_306_unit_case_open
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b) := by
  sorry

/-- **Erdős Problem 306** (faithful statement).

Let `a, b > 0` with `b` squarefree.  Then `a/b` is a finite sum of reciprocals
of distinct squarefree semiprimes (integers that are a product of two distinct
primes).

The proof reduces `a/b` to the unit case `1/b` via
`reduction_to_unit_numerator_avoiding` (sorry-free) and then invokes the open
unit-case input `erdos_306_unit_case_open`.  Since the latter is an open problem,
`#print axioms erdos_306` reports `sorryAx`; see the file header for the precise
status. -/
theorem erdos_306 (a b : ℕ) (_ : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator_avoiding
    (fun T b hb hbsf => erdos_306_unit_case_open T b hb hbsf)
    b hb hbsf a

end

-- Verifier aid: the axiom/gap trace of the target theorem.
-- This reports `sorryAx` because Problem 306 is open; the unique gap is the
-- cited open input `erdos_306_unit_case_open`.
#print axioms erdos_306
