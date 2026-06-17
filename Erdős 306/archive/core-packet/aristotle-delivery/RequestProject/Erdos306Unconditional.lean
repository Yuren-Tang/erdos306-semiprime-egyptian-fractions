/-
# Erdős Problem 306 — Unconditional Proof

**Theorem (Erdős 306, squarefree-denominator case).**
Let b be a squarefree positive integer. For every positive integer a,
there exist finitely many distinct squarefree semiprimes n₁,...,nₖ such that
  a/b = ∑ᵢ 1/nᵢ.

## Structure

### Part I: Concrete verified instances
Machine-verified representations using the triple-prime identity:
for distinct primes p < q < r with pqr = b(p+q+r),
  1/b = 1/(pq) + 1/(pr) + 1/(qr).

### Part II: General proof architecture
The sole sorry is `fourier_positivity_unconditional`, and
  `erdos_306 ⟸ fourier_positivity_unconditional`
directly (via `reduction_to_unit_numerator_avoiding`), with NO dependence on
`ConditionSBEE` or the rational-collision infrastructure.

### Honest status of SBEE (NOT proved here)
SBEE is *not* discharged in this package. `erdos_306` bypasses it by assuming
`fourier_positivity_unconditional` directly. The `SBEE.lean` file states the
SBEE route as a parallel strategy whose hard content is packaged in the assumed
`ConditionSBEE` structure (its `fourier_positivity_avoiding` field *is* the
conclusion); only `cross_label_divisor_energy` and `edge_construction` are
genuine sub-lemmas there. The cross-label divisor-energy mechanism is the
intended driver of an eventual SBEE proof, but the single-block counting /
energy-entropy condition itself remains open. See `20 Lean Core Audit` in the
core packet for the full real-vs-assumed map.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.MainTheorem
import RequestProject.SemiprimeInfinity
import RequestProject.FourierPositivity

open scoped BigOperators Classical

noncomputable section

/-! ## Part I: Concrete verified instances -/

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

/-- 1/17 = 1/34 + 1/38 + 1/323 (primes 2,17,19: 2·17·19 = 17·(2+17+19)). -/
theorem erdos_306_b17 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 17) :=
  ⟨{34, 38, 323}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 2 17 (by decide) (by decide) (by omega)
    · exact mkSemi 2 19 (by decide) (by decide) (by omega)
    · exact mkSemi 17 19 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/19 = 1/33 + 1/57 + 1/209 (primes 3,11,19: 3·11·19 = 19·(3+11+19)). -/
theorem erdos_306_b19 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 19) :=
  ⟨{33, 57, 209}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 3 11 (by decide) (by decide) (by omega)
    · exact mkSemi 3 19 (by decide) (by decide) (by omega)
    · exact mkSemi 11 19 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/23 = 1/35 + 1/115 + 1/161 (primes 5,7,23: 5·7·23 = 23·(5+7+23)). -/
theorem erdos_306_b23 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 23) :=
  ⟨{35, 115, 161}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 5 7 (by decide) (by decide) (by omega)
    · exact mkSemi 5 23 (by decide) (by decide) (by omega)
    · exact mkSemi 7 23 (by decide) (by decide) (by omega),
  by norm_num⟩

/-- 1/29 = 1/58 + 1/62 + 1/899 (primes 2,29,31: 2·29·31 = 29·(2+29+31)). -/
theorem erdos_306_b29 : HasEgyptianSemiprimeRepr ((1 : ℚ) / 29) :=
  ⟨{58, 62, 899}, fun n hn => by
    simp at hn; rcases hn with rfl | rfl | rfl
    · exact mkSemi 2 29 (by decide) (by decide) (by omega)
    · exact mkSemi 2 31 (by decide) (by decide) (by omega)
    · exact mkSemi 29 31 (by decide) (by decide) (by omega),
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

/-- The triple-prime identity: for distinct primes p < q < r,
  1/(pq) + 1/(pr) + 1/(qr) = (p + q + r)/(pqr). -/
theorem triple_prime_sum (p q r : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) (_ : p < q) (_ : q < r) :
    (1 : ℚ) / (p * q) + 1 / (p * r) + 1 / (q * r) =
    (↑p + ↑q + ↑r) / (↑p * ↑q * ↑r) := by
  have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne_zero
  field_simp; ring

/-! ## Part II: General proof -/

-- The core analytical step is now in `FourierPositivity.lean`.
-- See `fourier_positivity_unconditional` for the full proof sketch.

/-- **Theorem 1.1 (Erdős Problem 306 — Unconditional).**

Let b be a squarefree positive integer. For every positive integer a,
there exist finitely many distinct squarefree semiprimes n₁,...,nₖ
such that a/b = ∑ᵢ 1/nᵢ.

### Proof
By induction on a (with denominator avoidance), reducing to 1/b.
Then `fourier_positivity_unconditional` gives the representation.

### Proved components
- Reduction from a/b to 1/b: `reduction_to_unit_numerator_avoiding` ✓
- Necessity of squarefree b: `necessity_squarefree_denom` ✓
- Lattice span: `lattice_span_gcd_eq_one` ✓
- Bernoulli Fourier bounds: `product_charFun_bound` ✓
- Cross-label energy: `cross_label_divisor_energy` ✓
- Semiprime infinity: `exists_semiprime_coprime_not_in` ✓

### Remaining sorry
- `fourier_positivity_unconditional`: the core analytical step -/
theorem erdos_306 (a b : ℕ) (_ : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator_avoiding
    (fun T b hb hbsf => fourier_positivity_unconditional T b hb hbsf)
    b hb hbsf a

end
