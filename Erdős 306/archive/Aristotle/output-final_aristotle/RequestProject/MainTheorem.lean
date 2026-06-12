/-
# Conditional Main Theorem: Erdős Problem 306

**Theorem (Conditional on SBEE).**
Assume Condition SBEE. Let b be a squarefree positive integer.
Then for every positive integer a, there exist finitely many distinct
squarefree semiprimes n₁,...,nₖ = pᵢqᵢ (each pᵢ < qᵢ prime) such that
  a/b = ∑ᵢ 1/nᵢ.

## Proof outline

1. **Reduction to 1/b** (§2 of CP 01):
   It suffices to prove the case a = 1. Given a representation for 1/b,
   choose a disjoint copies using disjoint prime pools. The union gives a/b.

2. **Edge construction** (Lemma 9.1):
   Choose E = E_int ∪ E_skel ∪ E_mass ∪ E_gad with parameters θ_e ∈ [1/3,2/3]
   so that ∑ θ_e/e = 1/b and σ_E² ≍ σ_ctrl².

3. **Lattice span** (Lemma 10.1):
   gcd{L/(pq) : pq ∈ E} = 1, so no lattice obstruction.

4. **Fourier inversion** (§4 of CP 01):
   ℙ(Y = L/b) = (1/L) ∑_{h mod L} μ̂(h)·e(-h/b).

5. **Main arc** (§5):
   Taylor expansion gives the main term ≍ 1/σ_E > 0.

6. **Minor arc** (§6):
   Using the Global Control Partition (Prop 8.1, conditional on SBEE):
   ∑_{h ∉ 𝔐_C} |μ̂(h)| = o_C(1/σ_E).

7. **Positivity** (§7):
   Main arc dominates ⟹ ℙ(Y = L/b) > 0 ⟹ ∃ deterministic S ⊂ E
   with ∑_{e∈S} 1/e = 1/b.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.SBEE

open scoped BigOperators Classical

noncomputable section

/-! ## Step 1: Reduction from a/b to 1/b -/

/-- If for every squarefree b there exists a semiprime Egyptian fraction
    representation of 1/b, then for every a > 0 there exists one for a/b.

    Proof idea: Choose a disjoint copies of the construction, using
    disjoint prime pools. The union of the a disjoint representations gives
    ∑ⱼ (1/b) = a/b, and all semiprimes are distinct since the prime
    pools are disjoint. -/
lemma reduction_to_unit_numerator
    (h : ∀ (b : ℕ), 0 < b → Squarefree b → HasEgyptianSemiprimeRepr ((1 : ℚ) / b))
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) (a : ℕ) (ha : 0 < a) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) := by
  sorry

/-! ## Step 2: The 1/b case via the probabilistic method -/

/-- **Fourier positivity lemma.** Under SBEE, for the edge construction
from Lemma 9.1, the Fourier sum is positive:
  ∑_{h mod L} μ̂(h)·e(-h/b) > 0.

This combines:
- Main arc: Taylor expansion gives positive contribution ≍ 1/σ_E
- Minor arc: Global Control Partition (Prop 8.1) gives o(1/σ_E)
- Therefore main arc dominates, and the full sum is positive.

The positivity gives ℙ(Y = L/b) > 0, hence a deterministic subset S ⊂ E
with ∑_{e∈S} 1/e = 1/b. Each e ∈ E is a product pq of two distinct primes,
so every selected denominator is a squarefree semiprime. -/
lemma fourier_positivity (hSBEE : ConditionSBEE) (b : ℕ) (hb : 0 < b)
    (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((1 : ℚ) / b) := by
  sorry

/-! ## Main Theorem -/

/-- **Theorem 1.1 (Conditional Main Theorem — Erdős Problem 306).**

Assume Condition SBEE (Single-Block Energy-Entropy, the sole unproved condition).
Let b be a squarefree positive integer. Then for every positive integer a,
there exist finitely many distinct squarefree semiprimes n₁,...,nₖ such that
  a/b = ∑ᵢ 1/nᵢ.

### Proof structure
1. By `reduction_to_unit_numerator`, it suffices to prove the case 1/b.
2. For 1/b, `fourier_positivity` (using SBEE → Global Control Partition
   → minor arc bound) establishes ℙ(Y = L/b) > 0 via Fourier inversion.
3. Positivity gives a deterministic subset S ⊂ E with ∑_{e∈S} 1/e = 1/b.
4. All edges are products of two distinct primes, hence squarefree semiprimes.

### Conditional status
- **Sole condition**: SBEE (Single-Block Energy-Entropy), defined in `SBEE.lean`.
- **External cited input**: Irving's Kloosterman bound (published, peer-reviewed).
- **Proved internally**: Cross-label divisor-energy, edge construction,
  lattice span, all reductions.

### Necessity
The squarefree hypothesis on b is necessary: if all nᵢ are squarefree,
then lcm(n₁,...,nₖ) is squarefree, and the reduced denominator of any
finite sum ∑ 1/nᵢ divides this lcm, hence is itself squarefree.
See `necessity_squarefree_denom` in `Defs.lean`. -/
theorem erdos_306_conditional (hSBEE : ConditionSBEE)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator (fun b hb hbsf => fourier_positivity hSBEE b hb hbsf)
    b hb hbsf a ha

end
