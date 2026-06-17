# Codex Task: R2 Minor Classification and Support Pipeline

## Context

Work in `/Users/david/erdos-lean-build` if assigned externally, or in the main
core packet if working locally.

Read:

```lean
RequestProject/R2MinorSupportBudget.lean
RequestProject/R2MinorCover.lean
RequestProject/R2MinorEstimateInterface.lean
RequestProject/R2MassBatchWeights.lean
RequestProject/R2AssemblyFields.lean
RequestProject/ArcConstruction.lean
RequestProject/ExtraEnergyMinorArc.lean
```

The current clean endpoint is:

```lean
CircleMethod.exists_arcConstruction_of_selectedQ_coreSupply_autoWeights
```

The missing object is:

```lean
R2MinorSupportBudgetData (D.withQ Q) (QB.weights hbpos) N Bblock Bextra
```

## Goal

Create a downstream file:

```lean
RequestProject/R2MinorSupportPipeline.lean
```

Do not edit large upstream files.

The file should define the exact pipeline shape from three independent lanes to
`R2MinorSupportBudgetData`.

## Required Endpoint

The main theorem should look like:

```lean
theorem r2_minorSupportBudget_of_lanes
    {T : Finset Nat} {b : Nat}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : Int)
    (Bblock Bextra : Real)
    (Sblock Sextra :
      MainArcFields D.E W.theta b D.L N -> Finset Nat)
    (hcover : forall MA : MainArcFields D.E W.theta b D.L N,
      MA.Sm ⊆ Sblock MA ∪ Sextra MA)
    (hblock : forall MA : MainArcFields D.E W.theta b D.L N,
      sum h in blockMinorPart MA.Sm (Sblock MA),
        fourierNormWeight D.E W.theta b D.L h <= Bblock)
    (hextra : forall MA : MainArcFields D.E W.theta b D.L N,
      sum h in extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
        fourierNormWeight D.E W.theta b D.L h <= Bextra) :
    R2MinorSupportBudgetData D W N Bblock Bextra
```

This theorem is mostly a constructor, but it fixes the stable pipeline endpoint.

## Then Add Classification Hooks

Add definitions or structures for a classification lane without proving the hard
mathematics:

```lean
structure R2MinorClassificationData
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : Int) where
  Sblock : MainArcFields D.E W.theta b D.L N -> Finset Nat
  Sextra : MainArcFields D.E W.theta b D.L N -> Finset Nat
  hcover : forall MA, MA.Sm ⊆ Sblock MA ∪ Sextra MA
```

and:

```lean
structure R2MinorBudgetLanes ... where
  hblock : ...
  hextra : ...
```

then:

```lean
theorem r2_minorSupportBudget_of_classification_and_budgetLanes :
  ... -> R2MinorSupportBudgetData D W N Bblock Bextra
```

## Optional Useful Lemmas

If straightforward, add:

```lean
def trivialMinorClassificationData
```

with `Sblock MA := MA.Sm`, `Sextra MA := empty`, or vice versa, just as a sanity
constructor.  Do not build the final proof on this unless it is useful.

## Do Not

- Do not prove the block-minor analytic bound.
- Do not prove the extra-minor analytic bound.
- Do not choose numeric budgets.
- Do not touch expensive upstream files.
- Do not run repeated builds.  One build of `RequestProject.R2MinorSupportPipeline`
  at the end is enough.

## Expected Output

Report:

- file created;
- theorem names;
- build result;
- any warnings/errors;
- whether there are `sorry`s.
