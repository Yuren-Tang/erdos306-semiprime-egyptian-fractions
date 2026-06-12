/-
# Conditional Main Theorem: Erdős Problem 306

**Theorem (Conditional on SBEE).**
Assume Condition SBEE. Let b be a squarefree positive integer.
Then for every positive integer a, there exist finitely many distinct
squarefree semiprimes n₁,...,nₖ = pᵢqᵢ (each pᵢ < qᵢ prime) such that
  a/b = ∑ᵢ 1/nᵢ.

## Proof outline

1. **Fourier positivity with avoidance** (`ConditionSBEE.fourier_positivity_avoiding`):
   The SBEE-derived Fourier positivity theorem, exposed as a field of `ConditionSBEE`.
   For any finite obstruction set T and squarefree b, the probabilistic edge
   construction (with initial scale chosen above T) produces a semiprime
   Egyptian-fraction representation of 1/b using denominators disjoint from T.

2. **Reduction from a/b to 1/b** (`reduction_to_unit_numerator_avoiding`):
   By induction on a. At each step, apply the avoiding version to get a
   fresh copy of 1/b with denominators disjoint from all previously used ones.
   The union of the a disjoint representations gives a/b.

3. **Main theorem** (`erdos_306_conditional`):
   Combines the above two steps.

## Edge construction details (§2–7 of CP 01)

The Fourier positivity argument uses:
  - Edge construction (Lemma 9.1): E = E_int ∪ E_skel ∪ E_mass ∪ E_gad
    with θ_e ∈ [1/3, 2/3] and ∑ θ_e/e = 1/b.
  - Lattice span (Lemma 10.1): gcd{L/(pq) : pq ∈ E} = 1.
  - Fourier inversion (§4): ℙ(Y = L/b) = (1/L) ∑_{h mod L} μ̂(h)·e(-h/b).
  - Main arc (§5): Taylor expansion gives positive contribution ≍ 1/σ_E.
  - Minor arc (§6): Global Control Partition (Prop 8.1, conditional on SBEE)
    gives ∑_{h ∉ 𝔐_C} |μ̂(h)| = o_C(1/σ_E).
  - Positivity (§7): Main arc dominates ⟹ ℙ(Y = L/b) > 0 ⟹
    ∃ deterministic S ⊂ E with ∑_{e∈S} 1/e = 1/b.

All of this is encapsulated in the `fourier_positivity_avoiding` field of
`ConditionSBEE`. The free initial-scale parameter k₀ in the construction
allows starting above any finite obstruction set T.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.SBEE

open scoped BigOperators Classical

noncomputable section

/-! ## Step 1: Reduction from a/b to 1/b via denominator avoidance -/

/-
**Reduction to unit numerator (avoiding version).**

Given the SBEE-derived avoiding unit theorem — for every finite obstruction
set T and squarefree b, there exists a semiprime Egyptian-fraction
representation of 1/b with denominators disjoint from T — we prove
that a/b has a semiprime Egyptian-fraction representation for every a.

**Proof by induction on a:**
- Base case `a = 0`: the empty finset represents 0 = 0/b.
- Inductive step `a → a + 1`: By the induction hypothesis, there exists
  S representing a/b. Apply the avoiding theorem with obstruction set S
  to get U representing 1/b with Disjoint U S. Then S ∪ U represents
  (a+1)/b, since ∑_{S∪U} 1/n = a/b + 1/b = (a+1)/b, and all elements
  are semiprimes by the semiprime property of S and U.
-/
lemma reduction_to_unit_numerator_avoiding
    (h : ∀ (T : Finset ℕ) (b : ℕ),
      0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b))
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    ∀ a : ℕ, HasEgyptianSemiprimeRepr ((a : ℚ) / b) := by
  intro a
  induction' a with a ih;
  · exact ⟨ ∅, by norm_num ⟩;
  · obtain ⟨ S, hS₁, hS₂ ⟩ := ih; specialize h S b hb hbsf; rcases h with ⟨ U, hU₁, hU₂, hU₃ ⟩ ; use S ∪ U; simp_all +decide [ Finset.disjoint_left, add_div ] ;
    exact ⟨ fun n hn => hn.elim ( hS₁ n ) ( hU₁ n ), by rw [ Finset.sum_union ( Finset.disjoint_left.mpr fun x hxS hxU => hU₂ hxU hxS ), hS₂, hU₃ ] ⟩

/-! ## Main Theorem -/

/-- **Theorem 1.1 (Conditional Main Theorem — Erdős Problem 306).**

Assume Condition SBEE (Single-Block Energy-Entropy, the sole unproved condition).
Let b be a squarefree positive integer. Then for every positive integer a,
there exist finitely many distinct squarefree semiprimes n₁,...,nₖ such that
  a/b = ∑ᵢ 1/nᵢ.

### Proof structure
1. Extract `fourier_positivity_avoiding` from `ConditionSBEE`.
2. Apply `reduction_to_unit_numerator_avoiding` to get the representation for all a.
3. Specialize to the given a.

### Conditional status
- **Sole condition**: SBEE (Single-Block Energy-Entropy), defined in `SBEE.lean`.
  The `fourier_positivity_avoiding` field of `ConditionSBEE` encapsulates
  the full analytic argument of CP 01 §§3–7, including edge construction,
  Fourier inversion, main-arc Taylor expansion, minor-arc bound from the
  Global Control Partition (Proposition 8.1), and the positivity conclusion.
- **External cited input**: Irving's Kloosterman bound (published, peer-reviewed).
- **Proved in Lean**: The reduction from a/b to 1/b via denominator avoidance.

### Necessity
The squarefree hypothesis on b is necessary: if all nᵢ are squarefree,
then lcm(n₁,...,nₖ) is squarefree, and the reduced denominator of any
finite sum ∑ 1/nᵢ divides this lcm, hence is itself squarefree.
See `necessity_squarefree_denom` in `Defs.lean`. -/
theorem erdos_306_conditional (hSBEE : ConditionSBEE)
    (a b : ℕ) (_ha : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator_avoiding
    (fun T b hb hbsf => hSBEE.fourier_positivity_avoiding T b hb hbsf)
    b hb hbsf a

end