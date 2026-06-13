# Aristotle delivery — current task

**CURRENT TASK = `ACTIVE_PROMPT.md`: prove `g6_localization` in a new leaf
`RequestProject/GlobalControlG6.lean` (see note 43). Earlier hrhs/G5 task is
superseded — that is now driven separately.**

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

The single-block SBEE package is sorry-free:

- `SBEEDispersion`
- `SBEEFingerprint`
- `SBEEForcing`
- `SBEEAssembly.single_block_counting`

The global-control foundation already verified includes:

- faithful finite `GlobalAssignment` interface;
- G2 `crossblock_dispersion`;
- G3 `mismatch_penalty` and `mismatch_penalty_with_exceptions`;
- `GlobalPeierlsBookkeeping.lean`;
- note-40 support through `hot_factor`;
- energy-budget lemmas `sum_blockEnergy_le`, `sum_shellVec_le`,
  `shellVec_le_floorR`, `sum_Rw_hot_le`, `sum_bipartite_le`;
- cold/boundary machinery `excSet`, `cold_exceptions_small`,
  `cold_label_size64`, `cold_block_facts`, `boundary_penalty_per_k`.

The three headline chain sorries remain:

- `GlobalControl.global_levelset` (G5);
- `GlobalControl.global_control_partition` (G7);
- `CircleMethod.exists_positive_weighted_construction` (Phase C).

## Immediate target: finish G5

Use note `40 G5 Endgame - Remaining Holes Quartered.md` as the active
instruction, and use `ACTIVE_PROMPT.md` as the direct translation prompt.  The
remaining G5 work is now localized to:

1. The §3 data Finsets and four-level covering argument:
   - shell-data Finset carrying the hot-consistency filter;
   - 6a / 6b / 6d covering and injection/cardinality lemmas;
   - respect the correction that the initial segment label ranges over the
     `sqrt R`-window `L0`, not the old `labelRange`.
2. The §4 label-product numerics:
   - 10a, 10b, 10c.
3. The §5 final assembly:
   - hole 12, proving `global_levelset` with the faithful uniform factor
     `Real.exp (A * (numBlocks BS : ℝ))`.

Do not redo the support layer listed above.  State small helper lemmas first,
close them one by one, and keep `lake build` green after each coherent group.

## After G5

Then close:

1. G7 `global_control_partition`, using note 38 §7 and the now-proved G5.
2. Phase C `CircleMethod.exists_positive_weighted_construction`, using notes
   35 and 37 §6.
3. Final wiring: run `#print axioms erdos_306`, report the sorry inventory and
   axiom trace.
