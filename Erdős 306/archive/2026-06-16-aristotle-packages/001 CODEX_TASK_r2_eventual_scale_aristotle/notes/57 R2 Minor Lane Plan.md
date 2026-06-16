# R2 Minor Lane Plan

Back to [[56 R2 Endgame Map and Parallel Tasks]].

## Current Endpoint

The strongest clean local socket is now:

```lean
RequestProject/R2MassBatchWeights.lean

CircleMethod.exists_arcConstruction_of_selectedQ_coreSupply_autoWeights
```

It consumes:

- pre-selected component core data `R2ComponentScaleCoreSupply D N rho`;
- a selected residual set `Q`;
- a mass-batch package `R2MassBatchSupply (D.withQ Q)`;
- automatic weights `QB.weights hbpos`;
- numeric parameters `N, rho, K`;
- the remaining minor package
  `R2MinorSupportBudgetData (D.withQ Q) (QB.weights hbpos) N Bblock Bextra`;
- light-extra and final budget inequalities.

Thus the mass-selection/weight side is no longer the main obstruction.

## Remaining Mathematical Core

The remaining core is the construction of:

```lean
R2MinorSupportBudgetData D W N Bblock Bextra
```

for the concrete R2 edge set.  This means, for each generated main-arc package

```lean
MA : MainArcFields D.E W.theta b D.L N
```

we must provide:

```lean
Sblock MA : Finset Nat
Sextra MA : Finset Nat
MA.Sm ⊆ Sblock MA ∪ Sextra MA

∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
  fourierNormWeight D.E W.theta b D.L h ≤ Bblock

∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
  fourierNormWeight D.E W.theta b D.L h ≤ Bextra
```

This is not just record plumbing.  It is the R2 minor-arc decomposition.

## Existing Inputs

Already available:

```lean
RequestProject/R2MinorAssembly.lean
r2_minor_bound_split
blockMinorPart
extraMinorPart

RequestProject/R2MinorCover.lean
R2MinorCoverData
fourierNormWeight
hminor_of_block_extra_norm_bounds

RequestProject/R2MinorEstimateInterface.lean
block_part_bound
extra_part_bound
r2_hminor_bound_from_block_and_extra

RequestProject/ExtraEnergyMinorArc.lean
minor_arc_bound_fiber_tail

RequestProject/ExtraMinorDamping.lean
gadget_charFun_damp
```

The missing work is to specialize these abstract interfaces to the actual R2
sets and parameters.

## Block Minor Lane

Goal: prove the block-side norm-sum estimate.

Proposed endpoint:

```lean
theorem r2_block_minor_budget
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D)
    (N : Int) (Bblock : Real)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock : Finset Nat)
    (... block hypotheses ...) :
    ∑ h ∈ blockMinorPart MA.Sm Sblock,
      fourierNormWeight D.E W.theta b D.L h ≤ Bblock
```

Mathematical route:

1. Convert `fourierNormWeight` to the `QE` exponential bound.
2. Use `block_part_bound` / `minor_arc_bound_fiber_tail`.
3. Supply:
   - `Qctrl + Qextra ≤ QE`;
   - off-main property for the block part;
   - fiber-tail bound in each global-control assignment fiber.
4. Convert the resulting G7 expression into the chosen `Bblock`.

This is the hardest lane.  It is coupled to G7/global control and should remain
local unless it can be split further into a clean sublemma.

## Extra Minor Lane

Goal: prove the extra-side norm-sum estimate.

Proposed endpoint:

```lean
theorem r2_extra_minor_budget
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D)
    (N : Int) (Bextra : Real)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset Nat)
    (... extra hypotheses ...) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra
```

Mathematical route:

1. For every `h` in the extra part, choose a gadget edge `r*s`.
2. Prove the sibling congruence hypotheses:
   - diagonal modulo `s`;
   - offset modulo `r`;
   - small label `2 * |m| < s`.
3. Apply `gadget_charFun_damp`.
4. Sum the pointwise damping bound with `extra_part_bound`.
5. Choose enough gadget repetitions / enough large `r` scale so the total is
   at most `Bextra`.

This lane is plausibly suitable for Aristotle after the exact endpoint is
fixed.  It is more local than the block lane.

## Classification Lane

Goal: construct the cover `MA.Sm ⊆ Sblock MA ∪ Sextra MA`.

Proposed endpoint:

```lean
def r2MinorSupportSets
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : Int)
    (MA : MainArcFields D.E W.theta b D.L N) :
    Finset Nat × Finset Nat

theorem r2_minor_support_cover
    ... :
    MA.Sm ⊆ (r2MinorSupportSets ... MA).1 ∪
             (r2MinorSupportSets ... MA).2
```

Mathematical route:

For `h ∈ MA.Sm`, compare its global-control assignment with the main-arc label:

- If the block-support assignment is off-main with sufficient control energy,
  put `h` in `Sblock`.
- Otherwise it must be a sibling of a main-arc frequency; use a denominator
  prime `r ∣ b` and a gadget edge to put `h` in `Sextra`.

This lane is also suitable for external assignment, but only after its exact
definitions are chosen.  It should not be asked as a vague exploration task.

## Budget Lane

Goal: choose explicit `Bblock`, `Bextra`, `rho`, `K`, and `N` inequalities so:

```lean
Bblock + Bextra <
  (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS
```

and the numeric hypotheses in `R2MassBatchWeights` are satisfied.

This should be handled after the block/extra estimates are stated, otherwise
we risk guessing the wrong budget form.

## Recommended Next Move

Do not add more tiny wrapper files now.

Next implementation phase should create one coherent file:

```lean
RequestProject/R2MinorSupportPipeline.lean
```

containing only:

1. definitions for `Sblock`, `Sextra`, and any per-frequency witness data;
2. theorem statements for the three lanes above;
3. a final theorem assembling them into `R2MinorSupportBudgetData`.

Initially, if needed, the three hard lane theorems may be hypotheses to the
final assembler.  That still improves the project because it fixes the exact
shape of the remaining mathematical tasks.  Only after this shape is stable
should we build once and then dispatch independent tasks.

## External Task Shape

When ready, Aristotle should receive one of:

1. Extra minor lane only, with exact theorem statement and all helper lemmas
   named.
2. Classification lane only, with exact definitions of `Sblock` and `Sextra`.

Codex should receive:

1. Budget lane or block-lane sublemmas, because these may require iteration and
   access to the local tree.

Do not send another task consisting only of constructor wrappers.
