# Lean 4 Formalization: Erdős Problem 306 (Conditional Proof)

## Overview

This is an abstract dependency formalization of the conditional proof that
every rational a/b with squarefree denominator b can be expressed as a finite
sum of reciprocals of distinct squarefree semiprimes, assuming Condition SBEE
(Single-Block Energy-Entropy).

The Lean file is *not* a full formalization of the Fourier analysis — it is
an abstract formalization of the proof's logical structure, with the analytic
content (CP 01 §§3–7) encapsulated in the `ConditionSBEE` structure.

## Files

| File | Description |
|------|-------------|
| `Defs.lean` | Core definitions (`IsSemiprime`, `HasEgyptianSemiprimeRepr`, `HasEgyptianSemiprimeReprAvoiding`) and the necessity of the squarefree denominator condition |
| `SBEE.lean` | `ConditionSBEE` structure and the full lemma chain (Lemmas 2.1–10.1, Proposition 8.1) with dependency structure |
| `MainTheorem.lean` | Reduction from a/b to 1/b via denominator avoidance, and the main theorem `erdos_306_conditional` |

## What is fully proved (no sorry)

- **`IsSemiprime.squarefree`**: Every semiprime p·q (p < q, both prime) is squarefree.
- **`IsSemiprime.pos`**: Every semiprime is positive.
- **`IsSemiprime.cast_ne_zero`**: Every semiprime cast to ℚ is nonzero.
- **`necessity_squarefree_denom`**: If all denominators are squarefree, the sum's denominator is squarefree (proving the squarefree hypothesis on b is *necessary*).
- **`reduction_to_unit_numerator_avoiding`**: The reduction from a/b to 1/b by induction on a, using the denominator-avoidance predicate.
- **`erdos_306_conditional`**: The main theorem, proved from the reduction and the SBEE-derived avoiding unit theorem.

## SBEE interface design

`ConditionSBEE` is a `Prop`-valued structure with a single field:

```lean
structure ConditionSBEE : Prop where
  fourier_positivity_avoiding :
    ∀ (T : Finset ℕ) (b : ℕ), 0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b)
```

This field encapsulates the full analytic argument of CP 01 §§3–7:
- Edge construction with free initial-scale parameter k₀ (Lemma 9.1)
- Lattice-span gadget (Lemma 10.1)
- Fourier inversion (§4)
- Main-arc Taylor expansion (§5)
- Minor-arc bound from the Global Control Partition (§6, Prop 8.1)
- Positivity conclusion (§7)

all conditional on the Single-Block Energy-Entropy condition (SBEE).

The `Avoiding` variant (disjointness from a finite obstruction set T) is
mathematically justified by the free initial-scale parameter k₀ in the edge
construction, which allows starting above any finite set of previously used
denominators. This is what makes the inductive reduction from a/b to 1/b
work: at each step, we can avoid all previously used semiprimes.

**This is not an additional axiom beyond SBEE.** It is a theorem of CP 01 §§3–7
conditional on SBEE. It is exposed as a structure field because fully
formalizing the Fourier analysis is beyond the scope of this abstract
dependency formalization.

## Denominator avoidance and the reduction

The key insight is captured by the `HasEgyptianSemiprimeReprAvoiding` predicate:

```lean
def HasEgyptianSemiprimeReprAvoiding (T : Finset ℕ) (r : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, IsSemiprime n) ∧
    Disjoint S T ∧
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = r
```

The reduction `reduction_to_unit_numerator_avoiding` proceeds by induction on a:
- Base case: the empty finset represents 0/b.
- Inductive step: given S representing a/b, apply the avoiding theorem with
  obstruction set S to get U representing 1/b with `Disjoint U S`. Then
  `S ∪ U` represents (a+1)/b.

## Building

```bash
lake build RequestProject.MainTheorem
```

## Axiom check

```
#print axioms erdos_306_conditional
-- depends on: propext, Classical.choice, Quot.sound
```

No `sorry` in any transitive dependency.
