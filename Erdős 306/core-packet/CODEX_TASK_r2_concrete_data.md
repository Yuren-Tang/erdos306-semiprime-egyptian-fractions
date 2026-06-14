# CODEX TASK — R2 Concrete Construction Data Skeleton

Work in:

```text
/Users/david/erdos-lean-build
```

Do **not** work on `R2MinorEstimateInterface.lean`; that is the Aristotle lane.
This task is the parallel local-Codex lane: expose the concrete data fields for
the final `CircleMethod.exists_arcConstruction` assembly.

## Imports

Create a new leaf file:

```text
RequestProject/R2ConcreteData.lean
```

with imports:

```lean
import RequestProject.R2AssemblySkeleton
import RequestProject.BlockMassPool
import RequestProject.ArcConstructionSigma
import RequestProject.CircleMethodAssembly
```

## Goal

Do not attempt `exists_arcConstruction` directly.  Define the concrete R2 data
shape and prove the easy structural fields that are independent of the final
minor-arc estimates.

Use the already verified pieces:

```lean
CircleMethod.exists_blockAligned_mass_batch
CircleMethod.exists_subset_recip_window
CircleMethod.r2Edges
CircleMethod.r2_edges_semiprime
CircleMethod.r2_edges_avoid
CircleMethod.r2_edges_dvd_period
CircleMethod.sigmaE_le_sigmaCtrl_of_extra_light
```

## Suggested Targets

1. Define a structure, for example:

```lean
structure R2ConcreteData (T : Finset ℕ) (b : ℕ) where
  BS : GlobalControl.BlockSystem
  Q : Finset ℕ
  R : Finset ℕ
  S : Finset ℕ
  E : Finset ℕ := CircleMethod.r2Edges BS Q R S
  L : ℕ := CircleMethod.primeSupportPeriod b (GlobalControl.blockSupport BS)
```

If default fields are awkward, use explicit fields and equations.

2. Prove wrapper lemmas for this data:

```lean
lemma r2Concrete_semiprime ...
lemma r2Concrete_avoid ...
lemma r2Concrete_dvd_period ...
lemma r2Concrete_edges_pos ...
lemma r2Concrete_nonempty ...
```

3. Prove a light-extra sigma wrapper:

```lean
lemma r2Concrete_sigma_le_sigmaCtrl_of_light ...
```

It may take the actual light-extra hypothesis
`∑ e ∈ E \ ctrlEdges BS, (1/e^2) ≤ 3 * sigmaCtrl BS ^ 2`
explicitly.  The aim is to expose the final hypothesis list, not to close the
numerical large-`k0` estimate here.

4. If time remains, define a common-weight function

```lean
thetaOfLoad (b : ℕ) (Q : Finset ℕ) : ℕ → ℝ
```

or a more abstract `theta` wrapper whose hypotheses are exactly:

```lean
∀ e ∈ E, 1/3 ≤ theta e
∀ e ∈ E, theta e ≤ 2/3
∑ e ∈ E, theta e / (e : ℝ) = 1 / (b : ℝ)
```

Do not spend long on exact mass if it becomes coupled to final parameter choices.

## Important Mass Correction

Do **not** directly use `exists_blockAligned_mass_batch` as the final mass batch
for `E = ctrlEdges ∪ Q ∪ gadgetEdges`.  That lemma makes the `Q`-load itself lie
in `[3/(2b), 3/b]`; after adding control and gadget edges, the total load could
exceed `3/b`.

The final common-theta construction needs the **total** load:

```lean
loadE := ∑ e ∈ E, (1 : ℝ) / (e : ℝ)
```

to satisfy:

```text
3/(2b) ≤ loadE ≤ 3/b.
```

If you touch mass at all, prove a residual wrapper instead.  Given a fixed
nonnegative base load

```lean
baseLoad :=
  ∑ e ∈ ctrlEdges BS ∪ gadgetEdges R S, (1 : ℝ) / (e : ℝ)
```

and `baseLoad < 3/(2b)`, apply `exists_subset_recip_window` with:

```text
target = 3/(2b) - baseLoad
gap    = 3/(2b)
```

to obtain `Q` with:

```text
3/(2b) ≤ baseLoad + loadQ
baseLoad + loadQ ≤ 3/b
```

This residual lemma is more valuable than a direct call to
`exists_blockAligned_mass_batch`.

## Deliverable

Return:

1. files changed;
2. theorem names proved;
3. `lake build RequestProject.R2ConcreteData`;
4. axiom traces for the endpoint lemmas;
5. the exact remaining fields of `ArcConstruction` after these wrappers.

Keep the file sorry-free if possible.  If not, isolate only the smallest precise
construction hypothesis as a named `sorry`.
