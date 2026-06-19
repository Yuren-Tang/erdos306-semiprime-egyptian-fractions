# Aristotle Task: R2 Forbidden Pool Budget Bookkeeping

Please work in the Lean project and add a new thin file:

```lean
RequestProject/R2ForbiddenPoolBudget.lean
```

Import:

```lean
import RequestProject.R2MassBatchCandidatePool
```

Do not edit thick upstream files.

## Context

The current mass-batch endpoint is:

```lean
CircleMethod.exists_massBatchSupply_of_pairPool_separate_bounds
```

It needs a bound of the form:

```lean
R2ConcreteData.recipLoad
  (blockSupportPairPool D.BS ∩ residualForbidden D) ≤ F
```

where

```lean
residualForbidden D = T ∪ (ctrlEdges D.BS ∪ gadgetEdges D.R D.S)
```

Your task is the finite-set bookkeeping that decomposes this forbidden load into
three separately estimable pieces.

## Mandatory Goal 1: Nonnegative Monotonicity

Prove a reusable lemma for reciprocal load:

```lean
namespace CircleMethod

lemma recipLoad_mono {A B : Finset ℕ}
    (hAB : A ⊆ B) :
    R2ConcreteData.recipLoad A ≤ R2ConcreteData.recipLoad B := by
  ...

end CircleMethod
```

Hint: use `Finset.sum_le_sum_of_subset_of_nonneg`; the summand is nonnegative.

## Mandatory Goal 2: Union Upper Bound

Prove a two-set and/or three-set union bound.  One acceptable endpoint is:

```lean
lemma recipLoad_inter_union_le
    (A B C : Finset ℕ) :
    R2ConcreteData.recipLoad (A ∩ (B ∪ C))
      ≤ R2ConcreteData.recipLoad (A ∩ B)
        + R2ConcreteData.recipLoad (A ∩ C) := by
  ...
```

It is fine if you prove a more general finite-union statement instead.

## Mandatory Goal 3: Forbidden Budget Decomposition

Prove the paper-facing theorem:

```lean
theorem residualForbidden_recipLoad_le_components
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) :
    R2ConcreteData.recipLoad
        (blockSupportPairPool D.BS ∩ residualForbidden D)
      ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS ∩ T)
        + R2ConcreteData.recipLoad
            (blockSupportPairPool D.BS ∩ ctrlEdges D.BS)
        + R2ConcreteData.recipLoad
            (blockSupportPairPool D.BS ∩ gadgetEdges D.R D.S) := by
  ...
```

Use `residualForbidden` and the union bound.  This theorem should be robust
under definitional unfolding of `residualForbidden`.

## Optional Goal 4: Budget Record

If the mandatory goals are easy, add:

```lean
structure R2ForbiddenBudget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) where
  FT Fctrl Fgadget : ℝ
  hT :
    R2ConcreteData.recipLoad (blockSupportPairPool D.BS ∩ T) ≤ FT
  hctrl :
    R2ConcreteData.recipLoad
      (blockSupportPairPool D.BS ∩ ctrlEdges D.BS) ≤ Fctrl
  hgadget :
    R2ConcreteData.recipLoad
      (blockSupportPairPool D.BS ∩ gadgetEdges D.R D.S) ≤ Fgadget

theorem residualForbidden_recipLoad_le_budget
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b}
    (B : R2ForbiddenBudget D) :
    R2ConcreteData.recipLoad
        (blockSupportPairPool D.BS ∩ residualForbidden D)
      ≤ B.FT + B.Fctrl + B.Fgadget := by
  ...
```

## Verification

Run:

```text
lake build RequestProject.R2ForbiddenPoolBudget
```

The new file should contain no `sorry`, `admit`, or new `axiom`.

