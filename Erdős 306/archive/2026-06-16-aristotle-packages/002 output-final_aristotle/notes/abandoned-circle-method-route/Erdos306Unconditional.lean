/-
# Erdős Problem 306 — squarefree-denominator case

Reference for the problem: <https://www.erdosproblems.com/306>.

**Target theorem (`erdos_306`).**
Let `b` be a squarefree positive integer.  For every positive integer `a` there
is a *finite set of distinct squarefree semiprimes* `n₁, …, n_k` (each `nᵢ = pᵢ qᵢ`
a product of two distinct primes) with
`a / b = ∑ᵢ 1 / nᵢ`.

The squarefree hypothesis on `b` is necessary: a finite sum of reciprocals of
squarefree integers has a squarefree reduced denominator
(`necessity_squarefree_denom` in `Defs.lean`).

--------------------------------------------------------------------------------
## What is and is not verified in this file's dependency graph

This file is the entry point.  The honest state of the development is:

* **Fully machine-verified (sorry-free):**
  - the elementary reduction `a/b ⇝ 1/b` with denominator avoidance
    (`reduction_to_unit_numerator_avoiding`, `MainTheorem.lean`);
  - the *circle-method analytic core*
    `CircleMethod.exists_pos_weighted_of_construction`
    (`CircleMethodAssembly.lean`): given a block-aligned construction `(E, θ)`
    whose minor arc is beaten by the Gaussian main term, the deterministic
    weighted count is strictly positive — hence `1/b` is representable;
  - the `b = 1` and `b = 2` reductions `1 = 1/2 + 1/3 + 1/6`,
    `1/2 = 1/3 + 1/6` (`CircleMethodAssembly.lean`);
  - the concrete `1/b` instances in Part I below.

* **The single remaining gap reachable from `erdos_306`:**
  `CircleMethod.exists_arcConstruction` (`CircleMethodAssembly.lean`) — the
  existence, for squarefree `b ≥ 3`, of a concrete block-aligned circle-method
  construction with the required main-arc bijection and minor-arc domination.
  It is reduced (sorry-free, but not yet grounded in a concrete block system) by
  the `R2*` files to explicit number-theoretic supply estimates, and its
  minor-arc input ultimately rests on the (still unfinished) Phase-G global
  control of `GlobalControl.lean`.  This is the genuine analytic heart that
  remains open in the formalization.

`#print axioms erdos_306` (printed at the bottom of this file) therefore reports
`sorryAx`: the theorem is **not** a complete proof.  It is a faithful statement
together with a fully verified reduction down to the single isolated
construction lemma above.

--------------------------------------------------------------------------------
## Cited classical inputs ("quoted lemmas", isolated as named axioms)

The `R2*` reduction of the construction gap depends on two classical analytic
facts, isolated as named, individually documented axioms (`DyadicPrimes.lean`,
`R2BaseLoadUpper.lean`):

* `GlobalControl.dyadic_prime_density` — Rosser & Schoenfeld, *Approximate
  formulas for some functions of prime numbers*, Illinois J. Math. **6** (1962),
  Corollary 3 (`π(2x) − π(x) > 3x/(5 log x)` for `x ≥ 20.5`).
* `GlobalControl.dyadic_mertens_cumulative` — Mertens' theorem
  (`∑_{p ≤ x} 1/p = log log x + M + o(1)`), cumulative dyadic form.
* `CircleMethod.dyadic_control_recipLoad_eventually_small` — the matching
  Mertens-level reciprocal upper estimate for dyadic prime blocks.

These are standard, peer-reviewed results, recorded as axioms only because the
corresponding quantitative prime-distribution estimates are not yet available at
the required strength in Mathlib (cf. the `PrimeNumberTheoremAnd` project).  They
do **not** currently appear in the axiom trace of `erdos_306`, because the `R2*`
reduction is not yet wired into `exists_arcConstruction`; they are listed here so
an independent verifier can locate them as cited results rather than as proof
failures.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.MainTheorem
import RequestProject.FourierPositivity

open scoped BigOperators Classical

noncomputable section

/-! ## Part I: Concrete verified instances

These are fully proved, independent of the analytic core, via the
triple-prime identity:  for distinct primes `p < q < r`,
`1/(pq) + 1/(pr) + 1/(qr) = (p+q+r)/(pqr)`,
so whenever `pqr = b (p+q+r)` we get `1/b = 1/(pq) + 1/(pr) + 1/(qr)`. -/

/-- The triple-prime identity. -/
theorem triple_prime_sum (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (_ : p < q) (_ : q < r) :
    (1 : ℚ) / (p * q) + 1 / (p * r) + 1 / (q * r) =
    (↑p + ↑q + ↑r) / (↑p * ↑q * ↑r) := by
  have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne_zero
  field_simp; ring

private def mkSemi (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p < q) :
    IsSemiprime (p * q) := ⟨p, q, hp, hq, h, rfl⟩

/-- 1/3 = 1/6 + 1/10 + 1/15 (primes 2,3,5: 2·3·5 = 3·(2+3+5)). -/
theorem erdos_306_b3 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 3) :=
  ⟨{6, 10, 15}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 2 3 (by decide) (by decide) (by omega)
    · exact mkSemi 2 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 5 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/5 = 1/10 + 1/14 + 1/35 (primes 2,5,7: 2·5·7 = 5·(2+5+7)). -/
theorem erdos_306_b5 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 5) :=
  ⟨{10, 14, 35}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 2 5 (by decide) (by decide) (by omega)
    · exact mkSemi 2 7 (by decide) (by decide) (by omega)
    · exact mkSemi 5 7 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/7 = 1/15 + 1/21 + 1/35 (primes 3,5,7: 3·5·7 = 7·(3+5+7)). -/
theorem erdos_306_b7 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 7) :=
  ⟨{15, 21, 35}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 3 5 (by decide) (by decide) (by omega)
    · exact mkSemi 3 7 (by decide) (by decide) (by omega)
    · exact mkSemi 5 7 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/11 = 1/21 + 1/33 + 1/77 (primes 3,7,11: 3·7·11 = 11·(3+7+11)). -/
theorem erdos_306_b11 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 11) :=
  ⟨{21, 33, 77}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 3 7 (by decide) (by decide) (by omega)
    · exact mkSemi 3 11 (by decide) (by decide) (by omega)
    · exact mkSemi 7 11 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/2 = 1/6 + 1/10 + 1/15 + 1/21 + 1/26 + 1/35 + 1/39 + 1/65 + 1/91
(9 semiprimes from the complete graph on primes {2,3,5,7,13}). -/
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

/-! ## Part II: The general theorem

`fourier_positivity_unconditional` (`FourierPositivity.lean`) packages the
circle-method route: for every finite `T` and squarefree `b > 0` there is a
distinct-squarefree-semiprime representation of `1/b` avoiding `T`.  It is
proved by `CircleMethod.circle_method_positivity` down to the single isolated
construction lemma `CircleMethod.exists_arcConstruction` (see the header). -/

/-- **Erdős Problem 306 (squarefree-denominator case).**

For squarefree `b > 0` and any `a > 0`, `a/b` is a finite sum of reciprocals of
distinct squarefree semiprimes.

The proof reduces `a/b` to `1/b` (`reduction_to_unit_numerator_avoiding`) and
applies the circle-method unit-fraction theorem
(`fourier_positivity_unconditional`).  See this file's header for the precise
verification status: the chain is sorry-free except for the isolated
construction lemma `CircleMethod.exists_arcConstruction`, hence `#print axioms`
still reports `sorryAx`. -/
theorem erdos_306 (a b : ℕ) (_ : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator_avoiding
    (fun T b hb hbsf => fourier_positivity_unconditional T b hb hbsf)
    b hb hbsf a

end

-- Verifier aid: the axiom/gap trace of the target theorem.
-- Currently includes `sorryAx` (the isolated `exists_arcConstruction` gap).
#print axioms erdos_306
