# Codex Task: R2 Eventual Scale Bounds

## Goal

Create a new Lean file:

```lean
RequestProject/R2EventualScale.lean
```

This task is independent finite/numeric bookkeeping.  Import:

```lean
import RequestProject.R2ForbiddenBaseBudget
```

Build target:

```bash
lake build RequestProject.R2EventualScale
```

No `sorry`, `admit`, or new axioms.

## Main Mathematical Content

For fixed finite obstruction set `T` and fixed denominator `b`, choose `k0`
large enough that the bottom pair scale

```lean
2 ^ k0 * 2 ^ k0
```

dominates both all elements of `T` and `2*b/3`.

This supplies two hypotheses consumed by
`exists_massBatchSupply_of_basePieces_forbiddenBudget`:

```lean
hlarge  : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0)
hTsmall : ∀ e ∈ T, e < 2 ^ D.BS.k0 * 2 ^ D.BS.k0
```

## Desired Endpoints

Please prove endpoints with a flexible threshold form.  Exact names may vary,
but try to provide these:

```lean
lemma exists_k0_square_gt_nat (n : ℕ) :
    ∃ k0 : ℕ, n < 2 ^ k0 * 2 ^ k0 := by
  ...
```

```lean
lemma eventually_T_lt_k0_square (T : Finset ℕ) :
    ∃ k0min : ℕ, ∀ k0 : ℕ, k0min ≤ k0 →
      ∀ e ∈ T, e < 2 ^ k0 * 2 ^ k0 := by
  ...
```

```lean
lemma eventually_two_mul_b_lt_three_k0_square (b : ℕ) :
    ∃ k0min : ℕ, ∀ k0 : ℕ, k0min ≤ k0 →
      2 * b < 3 * (2 ^ k0 * 2 ^ k0) := by
  ...
```

Combined endpoint:

```lean
theorem exists_k0_scale_for_T_and_b (T : Finset ℕ) (b : ℕ) :
    ∃ k0min : ℕ, ∀ k0 : ℕ, k0min ≤ k0 →
      (∀ e ∈ T, e < 2 ^ k0 * 2 ^ k0) ∧
      2 * b < 3 * (2 ^ k0 * 2 ^ k0) := by
  ...
```

## Proof Hints

Use any existing Mathlib theorem for powers tending to infinity if available,
for example search for variants of:

```lean
Nat.exists_pow_gt
exists_lt_pow
```

If API search is painful, a direct construction is fine:

1. It is enough to find `k0` with `n < 2 ^ k0`, since then
   `n < 2 ^ k0 * 2 ^ k0` for `k0 ≥ 1`.
2. For finite `T`, use `T.max'` if `T.Nonempty`; otherwise the statement is
   vacuous.
3. Monotonicity: if `k0min ≤ k0`, then
   `2 ^ k0min ≤ 2 ^ k0`, hence
   `2 ^ k0min * 2 ^ k0min ≤ 2 ^ k0 * 2 ^ k0`.

It is fine to prove a slightly stronger theorem with `max` thresholds if that is
easier to use downstream.

## Why This Matters

`RequestProject/R2ForbiddenBaseBudget.lean` reduced the mass-batch construction
to natural large-scale assumptions.  This file should discharge the two
assumptions that depend only on the finiteness of `T` and fixedness of `b`.

