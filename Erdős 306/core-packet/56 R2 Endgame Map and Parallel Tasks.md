# R2 Endgame Map and Parallel Tasks

Back to [[55 R2 Parallel Returns Integrated]].

## Current Shape

The remaining `exists_arcConstruction` work is no longer one opaque analytic
problem.  It is a final record assembly with four layers:

1. **Concrete data**: choose `R2ConcreteData T b` and weights
   `R2ConcreteData.Weights D`.  Most structural fields are now available from
   `R2ConcreteData.lean`.
2. **Main-arc finite data**: choose `N`, then obtain `SM`, `Sm`, and `lbl`.
   `R2AssemblyFields.exists_mainArcFields` packages
   `hpart`, `hdisj`, `hmaps`, `hinj`, `hsurj`, and `hterm`.
3. **Main-arc scale inequalities**: prove `hN`, `htw`, and `hsmall`.
   This is mostly large-parameter/numeric bookkeeping.
4. **Minor-arc beat**: prove `hminor` through the block/extra split and then
   `hbeat` using `sigmaE <= sigmaCtrl`.

The real coupling is now concentrated in layer 4: the final `Sm` cover by
block-minor and extra-minor regimes, and the budget comparison.  The main-arc
and `hbound` fields are separable.

## Fields Already Reduced

The following are now essentially field plumbing:

```lean
hsemi     -- R2ConcreteData.semiprime
havoid    -- R2ConcreteData.avoid
hne       -- R2ConcreteData.nonempty_of_massBatch_nonempty / control version
hL        -- R2ConcreteData.period_pos
hbL       -- R2ConcreteData.base_dvd_period
heL       -- R2ConcreteData.dvd_period
he0       -- R2ConcreteData.edges_pos
hlb/hub/hmass -- R2ConcreteData.Weights
hbound    -- R2AssemblyFields.r2Concrete_hbound_of_recipLoad_window
hpart/hdisj/hmaps/hinj/hsurj/hterm -- R2AssemblyFields.exists_mainArcFields
hbeat shape -- R2AssemblyFields.hbeat_of_block_extra_sigmaCtrl
```

## Remaining Human-Core Work

The final local assembly should introduce a theorem, probably in a new file:

```lean
RequestProject/R2FinalAssembly.lean
```

It should first state a deliberately hypothesis-heavy theorem:

```lean
theorem exists_arcConstruction_of_R2FinalData
    ...
    : Nonempty (ArcConstruction T b)
```

This theorem should not yet try to prove all number-theoretic supply facts.
Instead it should consume:

- a concrete `D : R2ConcreteData T b`;
- weights `W : R2ConcreteData.Weights D`;
- structural supply hypotheses for semiprimality, avoidance, period divisibility;
- reciprocal-load upper window;
- `N` and the large-window hypotheses;
- a minor cover and block/extra minor estimates.

Once this theorem compiles, the remaining task is to discharge those hypotheses
from the existing construction lemmas.

## Parallel Task A

See [[CODEX_TASK_r2_numeric_fields]].

Completed and integrated as:

```lean
RequestProject/R2NumericFields.lean
MainArcNumericFields
mainArcNumericFields_of
```

This now packages `hN`, `hNnonneg`, `htw`, and `hsmall` for the final assembly.

## Parallel Task B

See [[CODEX_TASK_r2_minor_cover]].

Completed and integrated as:

```lean
RequestProject/R2MinorCover.lean
R2MinorCoverData
fourierNormWeight
hminor_of_block_extra_norm_bounds
```

This now turns a cover of `Sm` plus block/extra norm-sum bounds into the final
minor norm estimate.

## Local Next Step

The local spine is now:

```lean
RequestProject/R2FinalAssembly.lean
```

It defines:

```lean
R2FinalSupply
R2FinalSupply.toArcConstruction
exists_arcConstruction_of_R2FinalSupply
exists_R2FinalSupply_of_mainArcParams
exists_arcConstruction_of_mainArcParams
exists_arcConstruction_of_blockExtraBudget
exists_arcConstruction_of_componentData
exists_arcConstruction_of_componentData_light
exists_arcConstruction_of_componentData_light_window
exists_arcConstruction_of_componentData_numeric_minor_window
```

The strongest current local endpoint is
`exists_arcConstruction_of_componentData_numeric_minor_window`: it no longer
asks for structural edge fields, numeric main-window fields one by one,
`hminor`, `sigmaE <= sigmaCtrl`, `sigmaCtrl > 0`, the reciprocal-load upper
window for `D.E`, or the final `hbeat` directly.  Instead it consumes:

- component-level semiprime/avoid/divisibility hypotheses for `Q`, `R`, `S`;
- `MainArcNumericFields D.E W.theta N`;
- `2*N+1 <= L` to build the main-arc fields internally;
- residual load-window data
  `D.baseLoad + recipLoad D.Q ∈ [3/(2b), 3/b)`;
- a minor cover for each generated `MainArcFields`, plus block/extra norm-sum
  bounds;
- `admissibleGlobalRange D.BS`;
- the explicit light-extra inverse-square estimate;
- the strict budget `Bblock+Bextra < c3 / sigmaCtrl`.

This is the right socket for the final sprint.

## Build Discipline

The last R2 integration proved that even a target build with only a few dozen
jobs can cost close to an hour if it replays thick dependencies.  Going forward:

- Do not use a big build after every small edit.  Build only at real integration
  nodes, or when a local proof cannot be checked by reading.
- Before touching a thick file, inspect the previous build warnings for that
  file and its direct downstream users.  If the file is already being edited,
  clean mechanical warnings such as `ring`→`ring_nf`, unused simp arguments, and
  unused variables when this is low risk.
- Prefer thin leaf files for high-churn endpoints.  If a thick module must be
  changed repeatedly, first split out the active lemma/interface layer so cache
  invalidation stays local.
- Parallel task packets should also prefer split helper files and stable
  interfaces, not one monolithic file.  This makes Aristotle/Codex work more
  independent and makes local cache behavior better.
- Do not rewrite cached old modules merely to silence warnings.  Clean warnings
  opportunistically when those modules are already on the critical path.
