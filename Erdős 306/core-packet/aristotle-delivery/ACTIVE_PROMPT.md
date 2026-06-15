# Aristotle Task: R2 Control/Gadget Disjointness

Use `ARISTOTLE_TASK_r2_component_disjoint.md` as the detailed specification.

Create a new thin Lean file:

```lean
RequestProject/R2ComponentDisjoint.lean
```

Import:

```lean
import RequestProject.R2ForbiddenBaseBudget
```

This is a bounded downstream task.  Do **not** attempt the full
`exists_arcConstruction`; do **not** edit thick upstream files.  The goal is to
prove the prime-factor bookkeeping that shows

```lean
Disjoint (ctrlEdges BS) (gadgetEdges R S)
```

from the natural hypothesis that every denominator-side gadget prime `r ∈ R` is
outside `blockSupport BS`.

Preferred final check:

```bash
lake build RequestProject.R2ComponentDisjoint
```

Report theorem names, build status, and any remaining gaps.
