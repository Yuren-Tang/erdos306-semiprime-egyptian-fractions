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
RequestProject/R2ForbiddenPoolBudget.lean
residualForbidden_recipLoad_le_components
R2ForbiddenBudget
residualForbidden_recipLoad_le_budget
RequestProject/R2MassBatchFinalBudget.lean
exists_massBatchSupply_of_half_fullPool_forbiddenBudget
exists_massBatchSupply_of_blockPrimes_forbiddenBudget
exists_massBatchSupply_of_eventual_blockPrimes_forbiddenBudget
RequestProject/R2DyadicBlockSupport.lean
exists_blockSystem_with_blockPrimes_subset
RequestProject/R2ForbiddenBaseBudget.lean
blockSupportPairPool_inter_T_eq_empty_of_lt_k0_square
baseLoad_eq_ctrl_add_gadget_of_disjoint
R2ForbiddenBudget.of_basePieces
exists_massBatchSupply_of_basePieces_forbiddenBudget
RequestProject/R2ComponentDisjoint.lean
mem_ctrlEdges_support_pair
ctrlEdges_disjoint_gadgetEdges_of_R_outside_blockSupport
r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport
RequestProject/R2EventualScale.lean
exists_k0_square_gt_nat
eventually_T_lt_k0_square
eventually_two_mul_b_lt_three_k0_square
exists_k0_scale_for_T_and_b
RequestProject/R2MassBatchReady.lean
exists_massBatchSupply_of_basePieces_eventual
RequestProject/R2BaseLoadUpper.lean
R2BaseLoadBudget
baseLoad_eq_ctrl_add_gadget_of_R_outside
baseLoad_lt_of_budget
dyadic_control_recipLoad_eventually_small
RequestProject/R2MassBatchBaseLoadBudget.lean
exists_massBatchSupply_of_baseLoadBudget_eventual
RequestProject/R2ComponentScaleCard.lean
ctrlEdges_ge_k0_square
ctrlEdges_scale_of_k0_square
gadgetEdges_ge_mul
gadgetEdges_scale_of_mul
ctrlEdges_card_le_ctrlPairs_card
gadgetEdges_card_le_product
ctrlPairs_card_le_support_square
r2ControlSupply_of_k0_square
r2GadgetSupply_of_mul_scale
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

`R2ComponentScaleCard.lean` supplies the finite lower-scale and cardinality
wrappers for the control and gadget components, including constructors for
`R2ControlSupply` and `R2GadgetSupply`.

`R2ComponentSupplyReady.lean` is the current component-lane socket.  It packages
the scale, avoidance, prime/order/divisibility, and combined cardinality
hypotheses into one record
`R2ComponentScaleCardSupply`, and its endpoint
`exists_arcConstruction_of_componentScaleCardSupply` feeds this record directly
into `exists_arcConstruction_of_componentSupplies`.

`R2MassBatchScale.lean` proves that the residual mass batch `Q` inherits the
same bottom block-support scale bound from `R2MassBatchSupply.hQpair`.  Its
endpoint is `massBatchEdges_scale_of_k0_square`.

`R2ComponentMassReady.lean` is now the cleanest downstream R2 socket before
minor-budget and base-load closure.  Its endpoint
`exists_arcConstruction_of_componentScaleCardMassSupply` consumes just
`R2ComponentScaleCardSupply`, `R2MassBatchSupply`, and the minor-budget data;
the separate `hQedge` hypothesis is discharged internally.

`R2ComponentCoreSupply.lean` separates the stable control/gadget component data
from the selected residual batch `Q`.  Its `R2ComponentScaleCoreSupply` can be
transported across `D.withQ Q`, then converted back into
`R2ComponentScaleCardSupply` once the final `Q.card` budget is known.  This is
the intended interface after the mass-batch selector chooses `Q`.

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

`R2ForbiddenPoolBudget.lean` proves the complementary upper-bound bookkeeping:
the forbidden part of the residual pair pool is bounded by separate reciprocal
load budgets for overlap with `T`, `ctrlEdges D.BS`, and `gadgetEdges D.R D.S`.
Thus the mass-batch construction is now reduced to a final arithmetic bridge:
compare the half-mass full pool with `3/(2b) - D.baseLoad` plus those three
forbidden budgets.

`R2MassBatchFinalBudget.lean` closes that bridge.  Its endpoint
`exists_massBatchSupply_of_eventual_blockPrimes_forbiddenBudget` says: once
`blockPrimes D.BS.k0 ⊆ blockSupport D.BS`, the bottom-scale edge-smallness
inequality holds, and the three forbidden budgets satisfy
`(3/(2b) - D.baseLoad) + FT + Fctrl + Fgadget ≤ 1/2`, the residual `Q` batch
exists after choosing `D.BS.k0` beyond the existing `blockPrimes` load threshold.

`R2DyadicBlockSupport.lean` exposes the corresponding support fact for the
concrete dyadic block systems used by the construction:
`blockPrimes BS.k0 ⊆ blockSupport BS`.

`R2ForbiddenBaseBudget.lean` removes most of the forbidden-budget mystery.  If
all old obstruction edges in `T` lie below the bottom pair scale
`2^k0 * 2^k0`, and the fixed control/gadget edge families are disjoint, then
the `T` overlap is zero while the control/gadget forbidden pieces are absorbed
by `D.baseLoad`.  The final mass-batch budget then follows from `b ≥ 3`.

`R2ComponentDisjoint.lean` closes the disjointness input used by
`R2ForbiddenBaseBudget`: if every `r ∈ D.R` is prime and lies outside
`blockSupport D.BS`, then `ctrlEdges D.BS` and `gadgetEdges D.R D.S` are
disjoint.  The proof is pure prime-factor bookkeeping: a common edge would make
some `r ∈ D.R` divide a product `p*q` of block-support primes, hence force
`r = p` or `r = q`.

The still-open finite scale inputs for this branch are now only:

- `2*b < 3*(2^D.BS.k0 * 2^D.BS.k0)`;
- `∀ e ∈ T, e < 2^D.BS.k0 * 2^D.BS.k0`.

These are independent large-`k0` natural-number facts and are now proved in the
thin `R2EventualScale.lean` leaf.

The remaining nontrivial mass-batch input is therefore split into
`R2BaseLoadBudget D`: a control reciprocal-load budget and a gadget
reciprocal-load budget whose sum is `< 3/(2b)`.  The control part requires a
one-reciprocal upper estimate for dyadic prime blocks: heuristically
`∑_{p∈P_k} 1/p = O(1/k)`, so the internal/bipartite control reciprocal load is
`O(∑_{k=k0}^{3k0} 1/k^2) = O(1/k0)`.  The existing `dyadic_prime_density` and
`dyadic_mertens_cumulative` inputs are lower-bound inputs; by themselves they do
not give this upper estimate.  A crude interval-cardinality upper bound is too
weak.

`R2BaseLoadUpper.lean` now names this exact analytic socket as
`dyadic_control_recipLoad_eventually_small`, while keeping the gadget budget
separate.  `R2MassBatchBaseLoadBudget.lean` feeds `R2BaseLoadBudget` directly
into the mass-batch existence theorem.

`R2BaseBudgetAssembly.lean` is the Codex-returned base-budget layer.  It proves
the finite gadget reciprocal-load estimate
`gadget_recipLoad_le_card_div`, packages arbitrary control/gadget bounds into
`R2BaseLoadBudget`, and exposes
`baseLoadBudget_of_control_epsilon_and_gadget_scale`.  Thus the base-load lane
is now reduced to choosing an epsilon from
`dyadic_control_recipLoad_eventually_small` and checking the explicit finite
inequality
`epsilon + |R|*|S|/(r0*s0) < 3/(2b)`.

## Next Split

The next parallel split should be:

1. **Base-load upper lane**: use the named control analytic input plus a
   concrete gadget load budget to produce `R2BaseLoadBudget D`.
2. **Component numeric/cardinality lane**: prove practical hypotheses feeding
   `exists_arcConstruction_of_component_numeric_minor_sets`, especially
   component-wise edge lower bounds, ratio bounds, and an upper bound strong
   enough for `(D.E.card : ℝ) * 100000 * ρ^3 <= 1/10`.
3. **Minor support/budget lane**: define the actual `Sblock` and `Sextra`
   families for each `MainArcFields`, prove `Sm ⊆ Sblock ∪ Sextra`, and expose
   block/extra norm-sum bounds in the exact form consumed by
   `exists_arcConstruction_of_component_numeric_minor_sets`.
4. **Local mainline lane**: keep connecting concrete construction data,
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
- Keep `/Users/david/erdos-lean-build` synchronized with the live source packet
  before assigning external Codex tasks.  If task files mention new R2 leaves
  such as `R2ComponentDisjoint`, `R2EventualScale`, or `R2MassBatchReady`, those
  files must already exist in that worktree.
