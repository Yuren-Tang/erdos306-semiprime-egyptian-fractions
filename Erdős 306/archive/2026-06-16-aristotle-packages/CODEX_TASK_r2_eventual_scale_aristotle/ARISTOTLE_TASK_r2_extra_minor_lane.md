# Aristotle Task: R2 Extra Minor Lane

## Context

Read:

```lean
RequestProject/R2MinorEstimateInterface.lean
RequestProject/ExtraMinorDamping.lean
RequestProject/R2MinorCover.lean
RequestProject/R2MinorSupportBudget.lean
RequestProject/R2MassBatchWeights.lean
```

The project is now past the mass-batch/weight stage.  The remaining R2 minor
task is to build `R2MinorSupportBudgetData`.  This task focuses only on the
extra-minor side.

Do not work on global-control/G7 or block-minor estimates.  Do not create broad
new axioms.  If a theorem needs a mathematical hypothesis, expose it explicitly.

## Goal

Create:

```lean
RequestProject/R2ExtraMinorLane.lean
```

The file should provide a clean theorem that turns per-frequency gadget sibling
witnesses into an extra-minor norm-sum budget.

## Required Shape

The theorem should be as close as possible to:

```lean
theorem r2_extra_minor_budget_from_gadget_witnesses
    {T : Finset Nat} {b : Nat}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : Int)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset Nat)
    (Bextra Dmp : Real)
    (rfun sfun : Nat -> Nat)
    (mfun : Nat -> Int)
    -- each extra frequency has a valid gadget witness
    (hr : forall h in extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (rfun h))
    (hs : forall h in extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (sfun h))
    (hrs : forall h in extraMinorPart MA.Sm Sblock Sextra, rfun h <> sfun h)
    (hθlb : forall h in extraMinorPart MA.Sm Sblock Sextra, 1 / 3 <= W.theta (rfun h * sfun h))
    (hθub : forall h in extraMinorPart MA.Sm Sblock Sextra, W.theta (rfun h * sfun h) <= 2 / 3)
    (hm_s : forall h in extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (sfun h)) = (mfun h : ZMod (sfun h)))
    (hm_r : forall h in extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (rfun h)) <> (mfun h : ZMod (rfun h)))
    (hm_small : forall h in extraMinorPart MA.Sm Sblock Sextra,
      2 * |mfun h| < (sfun h : Int))
    (hDmp : forall h in extraMinorPart MA.Sm Sblock Sextra,
      Real.sqrt (1 - (8 / 9) / (rfun h : Real) ^ 2) <= Dmp)
    -- bridge from the full Fourier summand to the chosen gadget factor
    (hfactor : forall h in extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h
        <= ‖bernoulliCharFun (W.theta (rfun h * sfun h))
            ((h : Real) / ((rfun h : Real) * (sfun h : Real)))‖)
    -- cardinal/budget conversion
    (hbudget : ((extraMinorPart MA.Sm Sblock Sextra).card : Real) * Dmp <= Bextra) :
    sum h in extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h <= Bextra
```

You may adjust notation to Lean syntax.  If the exact `hθlb/hθub` using
`W.theta (rfun h * sfun h)` is awkward, introduce

```lean
θextra : Nat -> Real
```

and prove the theorem in that abstract form first:

```lean
fourierNormWeight ... h <=
  ‖bernoulliCharFun (θextra h) ((h : Real) / ((rfun h : Real) * (sfun h : Real)))‖
```

This abstract theorem is acceptable and probably preferable if it compiles
cleanly.  It should directly reuse:

```lean
CircleMethod.extra_part_bound
CircleMethod.gadget_charFun_damp
```

## Secondary Goal

If the main theorem is done, add a packaged structure:

```lean
structure R2ExtraMinorWitnessData ... where
  rfun : Nat -> Nat
  sfun : Nat -> Nat
  thetaExtra : Nat -> Real
  mfun : Nat -> Int
  ... all hypotheses above ...
```

and a short theorem:

```lean
theorem r2_extra_minor_budget_of_witnessData :
  ... -> sum ... fourierNormWeight ... <= Bextra
```

## Do Not

- Do not attempt the block-minor/G7 estimate.
- Do not attempt to select `Sblock` or `Sextra`.
- Do not change existing files unless absolutely needed.
- Do not introduce axioms.
- Do not leave `sorry` in the new file unless you explicitly report why and
  isolate it to a mathematically meaningful missing statement.

## Expected Output

Report:

- created file(s);
- theorem names;
- whether `lake build RequestProject.R2ExtraMinorLane` succeeds;
- whether there are any `sorry`s.
