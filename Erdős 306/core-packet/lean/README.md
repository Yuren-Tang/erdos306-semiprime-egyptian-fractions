# Core Lean Workbench

Back to [[../00 README]].

This is the curated Lean-side workbench for the core packet.

It is **not** a dump of the whole Aristotle project. It contains only:

1. the theorem boundary around the last `sorry`;
2. the active rational-collision / split-star shell;
3. the transitive Lean interfaces needed by those files.

The full Aristotle packages remain archived in `../../Aristotle/`.

## Build command

If `lake` is available:

```bash
lake build
```

Codex could not run this locally because the shell did not have a `lake`
command. Aristotle reported that the source package builds.

## The boundary file

```text
RequestProject/FourierPositivity.lean
```

contains the remaining theorem-level `sorry`:

```lean
fourier_positivity_unconditional
```

This is the Fourier-positive extraction theorem. It is not a small Lean API
gap.

## Main theorem shell

- `RequestProject/Erdos306Unconditional.lean`
- `RequestProject/MainTheorem.lean`
- `RequestProject/SBEE.lean`
- `RequestProject/FourierPositivity.lean`

## Active rational-collision shell

- `RequestProject/SplitStarCorrelation.lean`
- `RequestProject/ResidualPrimeShellCRT.lean`
- `RequestProject/PrimitiveProjectiveNormalization.lean`
- `RequestProject/AnchoredDeterminantRank.lean`
- `RequestProject/AnchoredCRTLattice.lean`
- `RequestProject/ValidCRTLattice.lean`
- `RequestProject/ReciprocalCRTProduct.lean`

## Finite selection interfaces kept here

- `RequestProject/AnchoredSelectionPipeline.lean`
- `RequestProject/AdaptiveClusterSelection.lean`
- `RequestProject/ClusterCoverBookkeeping.lean`
- `RequestProject/ClusterLineIncidence.lean`

## Fourier and semiprime support kept here

- `RequestProject/BernoulliFourier.lean`
- `RequestProject/LatticeSpan.lean`
- `RequestProject/CrossLabelEnergy.lean`
- `RequestProject/SemiprimeInfinity.lean`
- `RequestProject/Defs.lean`

(`SemiprimeReciprocals.lean` was removed in cleanup: it was an orphaned duplicate
of `SemiprimeInfinity.lean`, imported by nothing. See `../20 Lean Core Audit`.)

## What is intentionally not here

The bucket/FIE exploratory infrastructure and older broad formalization files
remain in archive. Bring one back only if the active theorem in
[[../02 Active Rational-Collision Problem]] needs it.
