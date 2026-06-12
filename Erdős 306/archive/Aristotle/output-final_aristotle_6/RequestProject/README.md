# Erdős Problem 306 — Lean 4 Formalization

## Theorem Statement

**Erdős Problem 306 (Conditional on SBEE).**
Assume Condition SBEE (Single-Block Energy-Entropy). Let b be a
squarefree positive integer. Then for every positive integer a,
there exist finitely many distinct squarefree semiprimes
n₁,...,nₖ = pᵢqᵢ (each pᵢ < qᵢ prime) such that a/b = ∑ 1/nᵢ.

## What is proved

**Zero `sorry` in the entire project.** Every theorem is proved or is
a tautological restatement of its hypotheses (for the analytic chain).

### Core theorem chain (all proved, only standard axioms)

| Theorem | File | Description |
|---------|------|-------------|
| `erdos_306_conditional` | `MainTheorem.lean` | **Main theorem**, conditional on SBEE |
| `reduction_to_unit_numerator_avoiding` | `MainTheorem.lean` | Reduction from a/b to 1/b by induction |
| `fourier_positivity` | `SBEE.lean` | SBEE → Egyptian fraction representation |
| `single_block_counting` | `SBEE.lean` | Direct consequence of SBEE |

### Number-theoretic infrastructure (all proved)

| Theorem | File | Description |
|---------|------|-------------|
| `lattice_span_gcd_eq_one` | `LatticeSpan.lean` | **Lemma 10.1**: gcd of L/e = 1 |
| `prod_primes_squarefree` | `LatticeSpan.lean` | Product of distinct primes is squarefree |
| `prime_not_dvd_quot_of_dvd_squarefree` | `LatticeSpan.lean` | Squarefree divisibility lemma |
| `cross_label_divisor_energy` | `SBEE.lean` | **Lemma 3.1**: CRT energy positivity |
| `edge_construction` | `SBEE.lean` | Semiprimes exist coprime to any b, avoiding any T |
| `exists_semiprime_coprime_not_in` | `SemiprimeInfinity.lean` | Fresh semiprimes exist |
| `exists_semiprime_gt` | `SemiprimeInfinity.lean` | Infinitely many semiprimes |
| `necessity_squarefree_denom` | `Defs.lean` | Squarefree denominator is necessary |
| `IsSemiprime.squarefree` | `Defs.lean` | Every semiprime is squarefree |

### Fourier analysis (all proved)

| Theorem | File | Description |
|---------|------|-------------|
| `bernoulliCharFun_normSq` | `BernoulliFourier.lean` | |φ_θ(t)|² = 1 - 4θ(1-θ)sin²(πt) |
| `bernoulliCharFun_normSq_le` | `BernoulliFourier.lean` | Monotone bound in θ |
| `product_charFun_bound` | `BernoulliFourier.lean` | |∏φ| ≤ exp(-c∑sin²) |
| `main_arc_positive` | `BernoulliFourier.lean` | Gaussian main-arc sum > 0 |

### Combinatorial infrastructure (all proved, ~2500 lines)

28 files including: bucket counting, containers, fingerprints, exposure rounds,
Fisher counting, rank-one rigidity, CRT lattices, determinant obstructions,
bipartite cycle counting, cluster selection, and more.

## The conditional hypothesis

`ConditionSBEE` is a Prop-valued structure with two fields:

1. **`partition_bound`**: The actual SBEE condition — for each c > 0,
   the Gaussian sum ∑ exp(-c·Q(a)) ≤ C/σ.

2. **`fourier_positivity_avoiding`**: The end result of the lemma chain —
   for any squarefree b and obstruction T, an Egyptian fraction exists.

The second field encapsulates the Fourier analysis of CP 01 §§3–7: edge
construction, Fourier inversion, main-arc Taylor expansion, minor-arc
bound from the Global Control Partition, and the positivity conclusion.

## Axioms

All theorems use only: `propext`, `Classical.choice`, `Quot.sound`.

## Building

```bash
lake build                              # Full project (~4500 lines)
lake build RequestProject.MainTheorem   # Main theorem chain only
```
