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

This is cleanly independent.  It should create abstract helper lemmas for
`hN`, `htw`, and `hsmall`, from simple lower-bound/cardinality hypotheses.
It should not touch the minor arc.

## Parallel Task B

See [[CODEX_TASK_r2_minor_cover]].

This is the coupled-but-isolatable minor side: define the concrete block-minor
and extra-minor frequency supports used by the R2 construction, prove
`Sm ⊆ Sblock ∪ Sextra`, and expose the hypotheses needed by
`r2_hminor_bound_from_block_and_extra`.

## Local Next Step

The best local step is to write the hypothesis-heavy
`exists_arcConstruction_of_R2FinalData` theorem.  This will expose exactly which
construction facts remain, without forcing every supply theorem to be solved in
the same edit.  It is the right "spine" for the final sprint.

