# Aristotle Task: R2 Component Numeric Bounds

You are working in the Lean project.  The target is not the whole Erdős 306
proof.  The target is a bounded, structural/numeric helper layer for the final
R2 assembly.

## Read first

```lean
RequestProject/R2ComponentBounds.lean
RequestProject/R2FinalAssemblyRaw.lean
RequestProject/R2NumericFields.lean
RequestProject/R2ConcreteData.lean
RequestProject/R2AssemblySkeleton.lean
```

## Goal

Create a new thin file:

```lean
RequestProject/R2ComponentNumeric.lean
```

It should import:

```lean
import RequestProject.R2ComponentBounds
```

The purpose is to make the numeric hypotheses of

```lean
CircleMethod.exists_arcConstruction_of_component_numeric_minor_sets
```

easier to supply from component-level parameter choices.

## Desired results

### 1. Uniform lower-bound-to-ratio helpers

Prove generic lemmas of this shape:

```lean
lemma ratio_bound_of_abs_le_and_edge_lower
    (N : ℤ) (ρ : ℝ)
    (hρpos : 0 < ρ)
    (hNabs : ∀ m ∈ Finset.Icc (-N) N, |(m : ℝ)| ≤ (N : ℝ))
    (hedge : ∀ e ∈ E, (N : ℝ) ≤ ρ * (e : ℝ))
    (hepos : ∀ e ∈ E, 0 < e) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E,
      |(m : ℝ) / (e : ℝ)| ≤ ρ
```

You may choose a cleaner signature.  The intended paper use is:

```lean
|m/e| <= ρ
```

from `|m| <= N` and `N <= ρ e`.

### 2. Component ratio wrappers

Using result 1, prove wrappers that separately handle:

```lean
ctrlEdges D.BS
D.Q
gadgetEdges D.R D.S
```

and then call:

```lean
R2ConcreteData.ratio_bound_of_components
```

to obtain the final `hratio`.

### 3. Cardinality upper bound for the R2 edge set

Prove a clean bound such as:

```lean
lemma r2Edges_card_le_components
    (D : R2ConcreteData T b) :
    D.E.card ≤ (ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card
```

Then prove a real-valued consequence useful for the cubic condition:

```lean
lemma cubic_card_bound_of_component_card_bound
    (D : R2ConcreteData T b) (ρ K : ℝ)
    (hρnonneg : 0 ≤ ρ)
    (hcard : ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10) :
    (D.E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10
```

Adjust signatures if Lean needs more explicit nonnegativity assumptions.

### 4. Packaged numeric data

If convenient, define a structure that packages:

```lean
hNscale
hctrlEdge
hQEdge
hgadgetEdge
hρnonneg
hctrlRatio
hQRatio
hgadgetRatio
hcard
hNL
```

This is optional, but useful if it stays lightweight.

## Constraints

- Do not edit thick upstream files.
- Keep all work in one or more thin downstream files.
- Avoid new axioms.
- Preferred final check:

```bash
lake build RequestProject.R2ComponentNumeric
```

Report theorem names, build status, and any remaining gaps.

