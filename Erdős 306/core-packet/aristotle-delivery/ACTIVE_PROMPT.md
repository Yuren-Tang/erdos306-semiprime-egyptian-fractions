# Aristotle Task: R2 Forbidden Pool Budget

Use `ARISTOTLE_TASK_r2_forbidden_pool_budget.md` as the detailed specification.

Create a new thin Lean file:

```lean
RequestProject/R2ForbiddenPoolBudget.lean
```

Import:

```lean
import RequestProject.R2MassBatchCandidatePool
```

This is a bounded downstream task.  Do **not** attempt the full
`exists_arcConstruction`; do **not** edit thick upstream files.  The goal is to
prove the finite-set reciprocal-load bookkeeping that decomposes

```lean
R2ConcreteData.recipLoad
  (blockSupportPairPool D.BS ∩ residualForbidden D)
```

into obstruction/control/gadget pieces.

Preferred final check:

```bash
lake build RequestProject.R2ForbiddenPoolBudget
```

Report theorem names, build status, and any remaining gaps.

