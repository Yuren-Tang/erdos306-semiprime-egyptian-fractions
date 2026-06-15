# Aristotle delivery — current task

**CURRENT TASK = `ACTIVE_PROMPT.md`: prove the R2 forbidden-pool budget
bookkeeping in a new leaf `RequestProject/R2ForbiddenPoolBudget.lean`.**

This is a clean Aristotle lane for the next parallel round: finite-set
bookkeeping only, downstream of the mass-batch candidate-pool interface, and not
coupled to analytic estimates.

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
lake build RequestProject.R2MassBatchCandidatePool
```

This confirms the chain through:

- `RequestProject.R2ComponentNumeric`;
- `RequestProject.R2ComponentNumericAssembly`;
- `RequestProject.R2MinorSupportBudget`;
- `RequestProject.R2MassBatchSupply`;
- `RequestProject.R2ComponentSupply`;
- `RequestProject.R2MassBatchPoolSupply`;
- `RequestProject.R2MassBatchCandidatePool`.

The exact downstream socket to support is:

```lean
CircleMethod.exists_massBatchSupply_of_pairPool_separate_bounds
```

## Immediate target

Use `ACTIVE_PROMPT.md` and `ARISTOTLE_TASK_r2_forbidden_pool_budget.md` as the
direct instructions.  Create `RequestProject/R2ForbiddenPoolBudget.lean` and
prove the finite-set reciprocal-load decomposition for `residualForbidden`.

Do not attempt the final `CircleMethod.exists_arcConstruction` directly in this
round.

