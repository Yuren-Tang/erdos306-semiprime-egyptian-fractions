# Aristotle delivery — current task

**CURRENT TASK = `ACTIVE_PROMPT.md`: R2-mass — the block-aligned mass batch
(T1 S₂ tail, T2 product-load ≥ 1/2, T3 greedy window) extending
`RequestProject/BlockMassPool.lean`.** (Note 49's extra-energy minor arc was
already integrated; do not redo it.)

Work in this folder as the Lake project root.  The Lean package is already in
the expected layout:

- `RequestProject/` contains the Lean sources.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are at the root.
- `.lake/build/lib/lean/RequestProject/` already contains compiled
  `RequestProject` oleans for this exact source state.
- `prebuilt-oleans.tar.gz` is a backup copy of the same project cache; extract
  it into `.lake/build/lib/lean/` only if the `.lake` directory was not preserved
  by upload.
- This cache is not a full Mathlib cache.  Before `lake build`, run
  `lake exe cache get` to fetch Mathlib's binary cache when the environment
  supports it.

## Binding rules

Do not weaken theorem statements or move constants behind the objects they must
control uniformly.  If a proof step is wrong, say so explicitly.  If a step
resists, isolate it as a precisely named `sorry` with a short reason and keep
the build green.

## Verified state

The current R2 foundation includes:

- `RequestProject.FiberCount`, with `mainArc_fiber_card_le`;
- `RequestProject.ArcConstructionExtra`, with support split definitions,
  `edgePrimeSupport_ctrlEdges_subset_blockSupport`, period divisibility helpers,
  and `blockSupport_frequency_fiber_card_le`;
- `lake build RequestProject.ArcConstructionExtra` green in the warm build
  project;
- key new endpoints depending only on standard axioms
  `[propext, Classical.choice, Quot.sound]`.

## Immediate target: note 49

Use `ACTIVE_PROMPT.md` as the direct instruction.  Create
`RequestProject/ExtraEnergyMinorArc.lean` and prove:

1. `minor_energy_sum_le_fiber_tail`;
2. if possible, `minor_arc_bound_fiber_tail`.

Do not attempt `CircleMethod.exists_arcConstruction` directly in this round.
Keep the file sorry-free if possible; if Target 2 is too slow, return Target 1
green with a precise explanation.
