# Aristotle delivery — current task

**CURRENT TASK = `ACTIVE_PROMPT.md`: prove the R2 numeric/main-arc field helpers
in a new leaf `RequestProject/R2NumericFields.lean`.**

This is the clean Aristotle lane for the next parallel round: short, independent,
and not coupled to the final `exists_arcConstruction` assembly.

Work in this folder as the Lake project root.  The Lean package is already in
the expected layout:

- `RequestProject/` contains the Lean sources.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` are at the root.
- `.lake/build/lib/lean/RequestProject/` contains compiled `RequestProject`
  oleans for this source state.
- `prebuilt-oleans.tar.gz` is a backup copy of the same project cache; extract
  it into `.lake/build/lib/lean/` only if the `.lake` directory was not
  preserved by upload.
- This cache is not a full Mathlib cache.  Before `lake build`, run
  `lake exe cache get` to fetch Mathlib's binary cache when the environment
  supports it.

## Binding rules

Do not weaken theorem statements or move constants behind the objects they must
control uniformly.  If a proof step is wrong, say so explicitly.  If a step
resists, isolate it as a precisely named `sorry` with a short reason and keep
the build green.

## Verified current state

The current R2 foundation includes:

- `RequestProject.R2ConcreteData`;
- `RequestProject.R2MinorEstimateInterface`;
- `RequestProject.R2AssemblyFields`, including:
  - `period_div_sum_lt_of_recip_sum_lt`;
  - `r2Concrete_hbound_of_recipLoad_lt_one`;
  - `recipLoad_lt_one_of_lt_three_div`;
  - `r2Concrete_hbound_of_recipLoad_window`;
  - `sigmaE_sqrt_pos_of_weights`;
  - `hbeat_of_sigma_le_sigmaCtrl`;
  - `hbeat_of_block_extra_sigmaCtrl`;
  - `MainArcFields`;
  - `exists_mainArcFields`.

## Immediate target

Use `ACTIVE_PROMPT.md` and `CODEX_TASK_r2_numeric_fields.md` as the direct
instructions.  Create `RequestProject/R2NumericFields.lean` and prove the
numeric/main-arc helpers for:

1. deriving `0 ≤ N` from the main-arc scale hypothesis;
2. deriving `htw` from a uniform edge lower bound;
3. deriving `hsmall` from a uniform ratio/cubic-load bound;
4. packaging these in `MainArcNumericFields`.

Do not attempt the final `CircleMethod.exists_arcConstruction` directly in this
round.

