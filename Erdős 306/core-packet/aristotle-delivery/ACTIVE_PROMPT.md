# Aristotle Task: R2 Component Numeric Bounds

Use `ARISTOTLE_TASK_r2_component_numeric.md` as the detailed specification.

Create a new thin Lean file:

```lean
RequestProject/R2ComponentNumeric.lean
```

Import:

```lean
import RequestProject.R2ComponentBounds
```

This is a bounded downstream task.  Do **not** attempt the full
`exists_arcConstruction`; do **not** edit thick upstream files.  The goal is to
prove reusable numeric/cardinality helpers feeding

```lean
CircleMethod.exists_arcConstruction_of_component_numeric_minor_sets
```

Preferred final check:

```bash
lake build RequestProject.R2ComponentNumeric
```

Report theorem names, build status, and any remaining gaps.
