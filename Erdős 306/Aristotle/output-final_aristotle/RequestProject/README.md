# Lean 4 Formalization: Conditional Proof of Erdős Problem 306

## Main Result

**Theorem** (`erdos_306_conditional` in `MainTheorem.lean`):
Assuming Condition SBEE, for every squarefree positive integer `b` and every
positive integer `a`, there exist finitely many distinct squarefree semiprimes
`n₁, ..., nₖ` such that `a/b = ∑ 1/nᵢ`.

## File Structure

| File | Contents |
|------|----------|
| `Defs.lean` | Core definitions: `IsSemiprime`, `HasEgyptianSemiprimeRepr`, necessity of squarefree denominator |
| `SBEE.lean` | Condition SBEE statement, Irving's Kloosterman bound, full lemma chain (Lemmas 2.1–10.1) |
| `MainTheorem.lean` | Main theorem `erdos_306_conditional`, reduction to 1/b, Fourier positivity |

## Proof Status

### Fully proved (no sorry)
- `IsSemiprime.squarefree`: every semiprime is squarefree
- `IsSemiprime.pos`: every semiprime is positive
- `IsSemiprime.cast_ne_zero`: cast to ℚ is nonzero
- `necessity_squarefree_denom`: squarefree denominator is necessary
- `erdos_306_conditional`: main theorem (modulo the two lemmas below)

### Sorry'd (deep mathematical content)
- `reduction_to_unit_numerator`: reduction from a/b to 1/b via disjoint prime pools
- `fourier_positivity`: the probabilistic method via Fourier inversion (the core argument)

### Conditional on SBEE
The entire proof depends on `ConditionSBEE`, which is the sole unproved
mathematical condition. It is passed as a hypothesis `(hSBEE : ConditionSBEE)`
to the main theorem.

## Dependency Graph

```
ConditionSBEE (hypothesis)
    │
    ├── single_block_counting (Lemma 4.1)
    ├── peierls_collapse (Lemma 6.1)
    ├── ordinary_diagonal_counting (Lemma 7.1)
    └── global_control_partition (Prop 8.1)
            │
            ▼
    fourier_positivity ← edge_construction, lattice_span_gadget
            │
            ▼
    reduction_to_unit_numerator
            │
            ▼
    erdos_306_conditional
```

## Building

```bash
lake build RequestProject.MainTheorem
```
