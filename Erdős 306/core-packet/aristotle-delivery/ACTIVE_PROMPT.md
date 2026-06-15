# Aristotle Task: R2 Numeric/Main-Arc Field Helpers

Create a new Lean file:

```lean
RequestProject/R2NumericFields.lean
```

Import:

```lean
import RequestProject.R2AssemblyFields
```

This is an intentionally independent, time-controlled task.  Do **not** attempt
`exists_arcConstruction`; do **not** touch the minor arc; do **not** modify large
existing files unless Lean absolutely forces a tiny import-level correction.

The goal is to prove abstract helper lemmas for the large-window fields
`hN`, `htw`, and `hsmall` in `ArcConstruction`.

Use `CODEX_TASK_r2_numeric_fields.md` as the detailed specification.

## Required output

1. `RequestProject/R2NumericFields.lean`;
2. no `sorry` if possible;
3. build command:

```bash
lake build RequestProject.R2NumericFields
```

4. brief summary of theorem names and any deviations from the requested
statements.

No axiom trace is required unless a theorem unexpectedly depends on nonstandard
assumptions.

