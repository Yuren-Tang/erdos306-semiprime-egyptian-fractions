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

A thin downstream wrapper has also been added:

```lean
RequestProject/R2FinalAssemblyRaw.lean
exists_arcConstruction_of_componentData_raw_numeric_minor_window
RequestProject/R2ComponentBounds.lean
exists_arcConstruction_of_component_numeric_minor_sets
RequestProject/R2ComponentNumeric.lean
RequestProject/R2ComponentNumericAssembly.lean
exists_arcConstruction_of_component_rho_numeric_minor_sets
RequestProject/R2MinorSupportBudget.lean
R2MinorSupportBudgetData
exists_arcConstruction_of_component_rho_numeric_minor_budget
RequestProject/R2MassBatchSupply.lean
R2MassBatchSupply
exists_arcConstruction_of_massBatchSupply
RequestProject/R2ComponentSupply.lean
R2ControlSupply
R2GadgetSupply
exists_arcConstruction_of_componentSupplies
RequestProject/R2MassBatchPoolSupply.lean
R2ConcreteData.withQ
exists_massBatchSupply_of_pool
RequestProject/R2MassBatchCandidatePool.lean
blockSupportPairPool
residualPairPool
residualPairPool_small_of_k0_square
residualPairPool_load_lower_of_forbidden_budget
exists_massBatchSupply_of_residualPairPool
exists_massBatchSupply_of_pairPool_forbidden_budget
exists_massBatchSupply_of_pairPool_separate_bounds
RequestProject/R2PairPoolFullLower.lean
blockSupportPairPool_load_ge_of_blockPrimes_subset
blockSupportPairPool_load_ge_half_of_contains_large_blockPrimes
exists_k1_blockSupportPairPool_load_ge_half
```

This wrapper leaves the green `R2FinalAssembly` spine untouched and expands
`MainArcNumericFields` into raw numeric hypotheses:

- scale: `1 / sqrt(sigmaE2 D.E W.theta) <= N`;
- edge lower bound: `10*N <= e` for every `e ∈ D.E`;
- ratio bound by a parameter `ρ`;
- cubic cardinality bound `|E| * 100000 * ρ^3 <= 1/10`.

This is the preferred next socket for parameter-selection work, because it is a
small leaf file downstream of the expensive assembly spine.

`R2ComponentBounds.lean` adds one more layer: instead of proving numeric bounds
for every `e ∈ D.E`, it accepts separate bounds on the three components
`ctrlEdges D.BS`, `D.Q`, and `gadgetEdges D.R D.S`.  This is the preferred
socket for split work, because the three edge families can be treated
independently.

`R2ComponentNumeric.lean` is the Aristotle-returned numeric/cardinality layer:
it proves ratio bounds from `N <= rho * e`, component cardinality control, and
the cubic-card transfer
`(D.E.card : ℝ) * 100000 * rho^3 <= 1/10`.

`R2ComponentNumericAssembly.lean` is the current local downstream socket.  Its
endpoint `exists_arcConstruction_of_component_rho_numeric_minor_sets` replaces
the separate `10*N <= e`, ratio, and `D.E.card` hypotheses by:

- `0 <= rho` and `rho <= 1/10`;
- component-wise positivity and scale bounds `N <= rho * e`;
- component-cardinality bound
  `(ctrl.card + Q.card + gadget.card : ℝ) <= K`;
- cubic budget `K * 100000 * rho^3 <= 1/10`.

This is currently the cleanest numeric interface for the final sprint.

`R2MinorSupportBudget.lean` packages the minor support lane into
`R2MinorSupportBudgetData`, with fields `Sblock`, `Sextra`, `hcover`, `hblock`,
and `hextra`.  The endpoint
`exists_arcConstruction_of_component_rho_numeric_minor_budget` is now the best
record-level socket: the remaining minor task is to construct this record and
prove the strict combined budget.

`R2MassBatchSupply.lean` packages the residual mass-batch lane.  If every
`e ∈ D.Q` is a product `p*q` of two ordered primes in `blockSupport D.BS`, then
the file derives `Qsemi`, `Qpos`, and `Qdvd` automatically.  The endpoint
`exists_arcConstruction_of_massBatchSupply` now consumes one `QB :
R2MassBatchSupply D` instead of the scattered Q structural and load-window
hypotheses.

`R2ComponentSupply.lean` packages the remaining control and gadget lanes:
`R2ControlSupply` stores the control scale/avoidance conditions, and
`R2GadgetSupply` stores the gadget prime/order/period/scale/avoidance
conditions.  The endpoint `exists_arcConstruction_of_componentSupplies` is now
the cleanest record-level assembly theorem.

`R2MassBatchPoolSupply.lean` adds the selection bridge before
`R2MassBatchSupply`: from a finite candidate pool `P` whose elements are
block-support prime products, avoid the obstruction set, are disjoint from the
fixed control/gadget edges, are individually small, and have enough residual
reciprocal load, it chooses a subset `Q` and produces
`R2MassBatchSupply (D.withQ Q)`.  This turns the mass-batch lane into a clean
candidate-pool construction problem rather than a preselected-`Q` problem.

`R2MassBatchCandidatePool.lean` names the canonical pool
`residualPairPool D`: all products `p*q` of ordered distinct block-support
primes, after removing `T` and the fixed control/gadget edges.  Its endpoint
`exists_massBatchSupply_of_residualPairPool` shows that this canonical pool
supplies `Q` once two numerical facts are proved:

- each surviving edge has reciprocal `< 3/(2b)`;
- its total reciprocal load is at least `3/(2b) - D.baseLoad`.

The first bullet is now reduced by `residualPairPool_small_of_k0_square`: it is
enough to impose the bottom-scale inequality
`2*b < 3*(2^D.BS.k0 * 2^D.BS.k0)`.  Thus the genuinely remaining mass-batch
estimate is the trimmed-pool load lower bound.

That lower bound has also been normalized by
`residualPairPool_load_lower_of_forbidden_budget` and
`exists_massBatchSupply_of_pairPool_forbidden_budget`: it is enough to show

```lean
(3 / (2 * (b : ℝ)) - D.baseLoad)
  + R2ConcreteData.recipLoad (blockSupportPairPool D.BS ∩ residualForbidden D)
  ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS)
```

plus the bottom-scale inequality above.  This is the current exact mass-batch
target.

`R2PairPoolFullLower.lean` proves the full-pool lower-bound half of this target:
if `blockPrimes k0 ⊆ blockSupport BS`, then the existing `BlockMassPool`
product-load lower bound transfers to
`R2ConcreteData.recipLoad (blockSupportPairPool BS)`.  In particular,
`blockSupportPairPool_load_ge_half_of_contains_large_blockPrimes` gives the
clean lower bound `1/2 ≤ ...` from the large-scale `blockPrimes` estimate.

## Next Split

The next parallel split should be:

1. **Component numeric/cardinality lane**: prove practical hypotheses feeding
   `exists_arcConstruction_of_component_numeric_minor_sets`, especially
   component-wise edge lower bounds, ratio bounds, and an upper bound strong
   enough for `(D.E.card : ℝ) * 100000 * ρ^3 <= 1/10`.
2. **Minor support/budget lane**: define the actual `Sblock` and `Sextra`
   families for each `MainArcFields`, prove `Sm ⊆ Sblock ∪ Sextra`, and expose
   block/extra norm-sum bounds in the exact form consumed by
   `exists_arcConstruction_of_component_numeric_minor_sets`.
3. **Local mainline lane**: keep connecting concrete construction data,
   residual `Q` selection, and weight/mass construction into the component
   socket.  This should stay in thin downstream files unless a thick module is
   already on the critical path.

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
