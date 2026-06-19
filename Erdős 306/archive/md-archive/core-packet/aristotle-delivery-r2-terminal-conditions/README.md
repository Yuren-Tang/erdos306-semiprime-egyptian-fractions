# R2 terminal conditions handoff

This handoff splits the remaining terminal conditions behind the R2 extra-minor
multi-gadget argument into two independent Lean tasks.

Current green core:

- `RequestProject/R2ExtraMultiGadget.lean`
- Important theorem:
  `CircleMethod.fourierNormWeight_le_multi_gadget_damp`

Mathematical status:

The terminal proof is no longer a deep analytic-number-theory gap at this point.
The remaining work is finite CRT bookkeeping plus finite reservoir/budget
bookkeeping.  The two tasks below can be solved independently.

Task A:

- File prompt: `TASK_A_CRT_COVERAGE_COUNTING.md`
- Goal: make explicit the missing condition that `D.R` covers every prime
  divisor of `b`, prove the CRT sibling lemma, and prove the finite counting
  bound for extra siblings.

Task B:

- File prompt: `TASK_B_RESERVOIR_BUDGET_BRIDGE.md`
- Goal: package a finite multi-gadget reservoir and turn it into
  `R2ExtraMinorMultiGadgetBoundData`, using the already proved multi-gadget
  damping theorem.

Recommended workflow:

1. Create new files only.  Do not edit the large assembly files.
2. Build only the new target file, not the whole project.
3. If a theorem is too hard in its most concrete form, prove the clean abstract
   version and state clearly which hypothesis is being abstracted.

