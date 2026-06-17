# Codex Task: R2 Full Pair-Pool Load Lower Bound

Work in the Lean project.  Do not edit thick upstream files unless truly
necessary.  Prefer a new thin file:

```lean
RequestProject/R2PairPoolFullLower.lean
```

Import:

```lean
import RequestProject.R2MassBatchCandidatePool
import RequestProject.BlockSystemConstruction
```

## Context

The current mass-batch endpoint is:

```lean
CircleMethod.exists_massBatchSupply_of_pairPool_separate_bounds
```

It reduces the residual mass-batch construction to separate bounds:

```lean
M ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS)
R2ConcreteData.recipLoad (blockSupportPairPool D.BS ∩ residualForbidden D) ≤ F
(3 / (2 * (b : ℝ)) - D.baseLoad) + F ≤ M
```

Your task is to prove reusable lower bounds for

```lean
R2ConcreteData.recipLoad (blockSupportPairPool BS)
```

from the existing `BlockMassPool.lean` machinery.

## Desired Theorems

First prove an abstract bridge for a dyadic block system whose support is the
same as `blockPrimes k0`:

```lean
namespace CircleMethod

theorem blockSupportPairPool_load_ge_of_blockPrimes_subset
    (BS : BlockSystem) (k0 : ℕ)
    (hsub : blockPrimes k0 ⊆ blockSupport BS)
    (hload :
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) :
    (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool BS) := by
  ...

end CircleMethod
```

Notes:

- You will probably need the product map injectivity already proved as
  `blockPrimes_pair_prod_injOn`.
- Use `Finset.sum_image` to rewrite the pair-product sum as a reciprocal load
  over the image.
- Then use subset monotonicity of nonnegative sums to pass from the image of
  `blockPrimes k0` pairs to `blockSupportPairPool BS`.
- Keep this theorem general if convenient; the exact statement can be adjusted
  as long as it gives a clean lower bound for `blockSupportPairPool BS`.

Then prove a convenient existential/large-scale corollary using the existing:

```lean
blockPrimes_product_load_ge :
  ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 → ...
```

For example:

```lean
theorem blockSupportPairPool_load_ge_half_of_contains_large_blockPrimes
    (BS : BlockSystem) (k1 : ℕ)
    (hlarge : k1 ≤ BS.k0)
    (hsub : blockPrimes BS.k0 ⊆ blockSupport BS)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) :
    (1 : ℝ) / 2 ≤ R2ConcreteData.recipLoad (blockSupportPairPool BS) := by
  ...
```

## Optional But Valuable

If it is easy, specialize to the concrete dyadic block system from
`GlobalControl.exists_blockSystem`/`BlockSystemConstruction.lean`, or add a
lemma showing that for the canonical dyadic system with `K = 3*k0` and
`P = dyadicBlock`,

```lean
blockPrimes k0 = blockSupport BS
```

or at least `blockPrimes k0 ⊆ blockSupport BS`.

## Verification

Run:

```text
lake build RequestProject.R2PairPoolFullLower
```

Do not run a full project build unless needed.  The new file should contain no
`sorry`, `admit`, or new `axiom`.

