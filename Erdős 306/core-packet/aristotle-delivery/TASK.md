# Aristotle delivery — current task

**CURRENT TASK = `ACTIVE_PROMPT.md`: create the R2 assembly skeleton from note 52
in a new leaf `RequestProject/R2AssemblySkeleton.lean`.** The R2-mass batch and
note-49 extra-energy minor-arc interface are already integrated; do not redo
them.

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
- `RequestProject.BlockMassPool`, with `exists_blockAligned_mass_batch`;
- `RequestProject.ExtraEnergyMinorArc`, with `minor_arc_bound_fiber_tail`;
- `RequestProject.ExtraMinorDamping`, with `gadget_charFun_damp`;
- `lake build RequestProject.ArcConstructionExtra` green in the warm build
  project;
- key new endpoints depending only on standard axioms
  `[propext, Classical.choice, Quot.sound]`.

## Immediate target: note 52

Use `ACTIVE_PROMPT.md` as the direct instruction.  Create
`RequestProject/R2AssemblySkeleton.lean` and prove the first assembly
bookkeeping layer:

1. gadget edge definitions and support/semiprime/divisibility lemmas;
2. union edge-set bookkeeping for `ctrlEdges ∪ Q ∪ gadgetEdges`;
3. if possible, a block-minor wrapper around `minor_arc_bound_fiber_tail`.

Do not attempt `CircleMethod.exists_arcConstruction` directly in this round.
Keep the file sorry-free if possible; if the block-minor wrapper is too large,
return the gadget/union bookkeeping green with a precise explanation.
