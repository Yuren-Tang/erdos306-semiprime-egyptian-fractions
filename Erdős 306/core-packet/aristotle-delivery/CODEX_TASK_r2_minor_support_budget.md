# Codex Task: R2 Minor Support and Budget Lane

Worktree: `/Users/david/Obsidian/Math/Erdős 306/core-packet/lean`

## Goal

Advance the minor-arc lane feeding:

```lean
RequestProject.R2ComponentBounds
CircleMethod.exists_arcConstruction_of_component_numeric_minor_sets
```

Do **not** try to prove Erdős 306 directly.  Build thin helper files that make
the hypotheses

```lean
Sblock Sextra : MainArcFields D.E W.theta b D.L N → Finset ℕ
hcover : ∀ MA, MA.Sm ⊆ Sblock MA ∪ Sextra MA
hblock : ∀ MA, ∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
  fourierNormWeight D.E W.theta b D.L h ≤ Bblock
hextra : ∀ MA, ∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
  fourierNormWeight D.E W.theta b D.L h ≤ Bextra
hminorCtrl : Bblock + Bextra < c3 / sigmaCtrl D.BS
```

more concrete and easier to discharge.

## Files to read first

```lean
RequestProject/R2ComponentBounds.lean
RequestProject/R2FinalAssemblyRaw.lean
RequestProject/R2MinorCover.lean
RequestProject/R2MinorEstimateInterface.lean
RequestProject/R2MinorAssembly.lean
RequestProject/ExtraEnergyMinorArc.lean
RequestProject/ExtraMinorDamping.lean
RequestProject/FiberCount.lean
```

## Suggested implementation

Create a new thin file:

```lean
RequestProject/R2MinorSupportBudget.lean
```

Import only what you need, probably:

```lean
import RequestProject.R2ComponentBounds
import RequestProject.FiberCount
```

Useful subtasks:

1. Define paper-facing predicates/structures for the minor lane, e.g.

```lean
structure R2MinorSupportBudgetData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra : ℝ) where
  Sblock : MainArcFields D.E W.theta b D.L N → Finset ℕ
  Sextra : MainArcFields D.E W.theta b D.L N → Finset ℕ
  hcover : ∀ MA, MA.Sm ⊆ Sblock MA ∪ Sextra MA
  hblock : ∀ MA, ∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
    fourierNormWeight D.E W.theta b D.L h ≤ Bblock
  hextra : ∀ MA, ∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
    fourierNormWeight D.E W.theta b D.L h ≤ Bextra
```

2. Prove a wrapper theorem that consumes `R2MinorSupportBudgetData` and calls
   `exists_arcConstruction_of_component_numeric_minor_sets`.

3. If feasible, define canonical candidates:
   - `Sblock MA`: frequencies whose block-support assignment is outside the
     main arc but controlled by the block/fiber estimate.
   - `Sextra MA`: the complementary frequencies detected by the R2 gadget
     condition.

4. Prove any pure finite-set facts needed for `hcover`; keep analytic estimates
   as named hypotheses if necessary.

5. If you use `mainArc_fiber_card_le`, expose a clean wrapper that produces the
   multiplicity input expected by the block estimate.

## Engineering constraints

- Keep this as thin downstream work.  Do not edit thick files unless absolutely
  necessary.
- Split helper lemmas into small files if the file starts to become heavy.
- Build only meaningful targets.  Preferred final check:

```bash
lake build RequestProject.R2MinorSupportBudget
```

- Report exact theorem names and whether the new file is sorry-free.

