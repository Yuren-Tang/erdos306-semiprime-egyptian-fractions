# Task: R2 Minor-Cover Interface

Work in the current Lean package.  Create a new file:

```lean
RequestProject/R2MinorCover.lean
```

Import:

```lean
import RequestProject.R2MinorEstimateInterface
import RequestProject.R2AssemblyFields
```

Goal: isolate the frequency-cover interface needed for the final R2 minor arc.
Do **not** attempt the final `exists_arcConstruction`.  Do **not** change the
statements in existing files unless absolutely necessary.

## Background

We already have:

```lean
blockMinorPart
extraMinorPart
r2_hminor_bound_from_block_and_extra
block_part_bound
extra_part_bound
```

The final construction needs a clean way to say:

```lean
Sm ⊆ Sblock ∪ Sextra
```

and then combine block/extra estimates into:

```lean
‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm
```

The exact analytic estimates can remain hypotheses.  This task is finite
bookkeeping plus a stable theorem shape.

## Required Definitions

Define a structure:

```lean
structure R2MinorCoverData (Sm : Finset ℕ) where
  Sblock : Finset ℕ
  Sextra : Finset ℕ
  hcover : Sm ⊆ Sblock ∪ Sextra
```

Define an abstract per-frequency norm:

```lean
def fourierNormWeight (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (h : ℕ) : ℝ :=
  ‖fourierTerm E theta b L h‖
```

## Required Theorem

Prove a theorem of this shape:

```lean
theorem hminor_of_block_extra_norm_bounds
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (Sm : Finset ℕ) (C : R2MinorCoverData Sm)
    (Bblock Bextra Bm : ℝ)
    (hblock :
      ∑ h ∈ blockMinorPart Sm C.Sblock,
        fourierNormWeight E theta b L h ≤ Bblock)
    (hextra :
      ∑ h ∈ extraMinorPart Sm C.Sblock C.Sextra,
        fourierNormWeight E theta b L h ≤ Bextra)
    (hbudget : Bblock + Bextra ≤ Bm) :
    ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm
```

Expected proof:

1. Use `norm_sum_le` to bound the norm by the sum of norms over `Sm`.
2. Use `r2_hminor_bound_from_block_and_extra` with `F := fourierNormWeight ...`.
3. Finish with `hbudget`.

## Optional Useful Theorem

If the proof is easy, also provide a strict-budget version suitable for
`hbeat`:

```lean
theorem hminor_and_hbeat_of_block_extra
    ...
```

but do not get stuck here.

## Build

Verify only:

```bash
lake build RequestProject.R2MinorCover
```

No axiom trace needed.

