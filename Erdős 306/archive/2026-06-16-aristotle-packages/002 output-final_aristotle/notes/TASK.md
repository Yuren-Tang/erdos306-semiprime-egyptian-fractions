# Aristotle delivery — current task

**CURRENT TASK = `ACTIVE_PROMPT.md`: prove the R2 control/gadget disjointness
bookkeeping in a new leaf `RequestProject/R2ComponentDisjoint.lean`.**

This is a clean Aristotle lane for the next parallel round: finite-set
prime-factor bookkeeping only, downstream of the mass-batch budget interface,
and not coupled to analytic estimates.

Work in this folder as the Lake project root.  The Lean package is already in
the expected layout:

- `RequestProject/` contains the Lean sources.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are at the root.
- `.lake/build/lib/lean/RequestProject/` contains compiled `RequestProject`
  oleans for an older source state.
- `prebuilt-oleans.tar.gz` is a backup copy of that cache; extract it into
  `.lake/build/lib/lean/` only if the `.lake` directory was not preserved by
  upload.
- This cache may not include the newest R2 leaf files.  Build only the requested
  target; if Mathlib cache is missing, run `lake exe cache get` first when the
  environment supports it.

## Binding rules

Do not weaken theorem statements.  If a proof step is wrong, say so explicitly.
If a step resists, isolate it as a precisely named `sorry` with a short reason
and keep the build green.

## Verified current local state before this task

The local Codex build has verified:

```text
lake build RequestProject.R2ForbiddenBaseBudget
```

This confirms the chain through:

- `RequestProject.R2MassBatchFinalBudget`;
- `RequestProject.R2DyadicBlockSupport`;
- `RequestProject.R2ForbiddenBaseBudget`.

The exact downstream socket to support is:

```lean
CircleMethod.exists_massBatchSupply_of_basePieces_forbiddenBudget
```

## Immediate target

Use `ACTIVE_PROMPT.md` and `ARISTOTLE_TASK_r2_component_disjoint.md` as the
direct instructions.  Create `RequestProject/R2ComponentDisjoint.lean` and
prove `ctrlEdges`/`gadgetEdges` disjointness from `R` being outside block
support.

Do not attempt the final `CircleMethod.exists_arcConstruction` directly in this
round.
