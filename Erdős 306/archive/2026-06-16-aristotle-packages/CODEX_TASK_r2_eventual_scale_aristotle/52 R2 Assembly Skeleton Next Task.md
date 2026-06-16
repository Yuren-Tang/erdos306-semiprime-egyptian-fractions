# R2 Assembly Skeleton Next Task

Back to [[50 R2 Construction Resolved - Gadget Cancellation and the b≥3 Reduction]]
and [[51 R2 Mass Batch Completed]].

## Current State

The arithmetic cores are now banked:

- block system with `K = 3*k0`;
- block-aligned mass batch:
  `CircleMethod.exists_blockAligned_mass_batch`;
- block-minor interface:
  `CircleMethod.minor_arc_bound_fiber_tail`;
- support and period bookkeeping:
  `ArcConstructionExtra.lean`;
- sigma comparison:
  `ArcConstructionSigma.lean`;
- extra-minor gadget arithmetic:
  `CircleMethod.gadget_nndist1_lower` and
  `CircleMethod.gadget_charFun_damp`;
- `b = 2` reduction has been added in `CircleMethodAssembly.lean`;
- the consumer is still:
  `CircleMethod.exists_arcConstruction`.

## The Remaining Shape

The remaining R2 work is no longer a missing arithmetic estimate.  It is the
monolithic assembly:

1. instantiate a block system at sufficiently large scale;
2. choose a block-aligned mass batch `Q`;
3. choose gadget edges `r*s` for each prime `r ∣ b` and enough block primes `s`;
4. define the final edge set

   ```lean
   E = ctrlEdges BS ∪ Q ∪ gadgetEdges
   ```

5. set the period

   ```lean
   L = b * ∏ p ∈ blockSupport BS, p
   ```

6. choose weights `theta` satisfying `[1/3,2/3]` and exact mass;
7. define the main frequencies `SM` and labels using `exists_mainArc_bijection`;
8. split `Sm = range L \ SM` into block-minor and extra-minor parts internally;
9. prove `hminor` as block-minor bound plus extra-minor sibling damping;
10. fill all fields of `ArcConstruction`.

## Recommended Next Lean Task

Do not attempt the whole `exists_arcConstruction` in one jump.  First create a
new leaf file:

```text
RequestProject/R2AssemblySkeleton.lean
```

with imports:

```lean
import RequestProject.BlockMassPool
import RequestProject.ExtraEnergyMinorArc
import RequestProject.ExtraMinorDamping
import RequestProject.ArcConstructionSigma
```

### Target A: gadget edge definitions

Define a finite gadget edge set abstractly from a finite set of denominator
primes `R` and support primes `S`:

```lean
def gadgetEdges (R S : Finset ℕ) : Finset ℕ :=
  (R ×ˢ S).image (fun rs => rs.1 * rs.2)
```

Prove support and semiprime lemmas under prime/distinct hypotheses:

```lean
lemma gadgetEdges_semiprime
lemma gadgetEdges_dvd_period
lemma gadgetEdges_avoid_of_large_support
```

Use statement forms that are easy to feed into `ArcConstruction`.

### Target B: union edge-set bookkeeping

For

```lean
E := ctrlEdges BS ∪ Q ∪ gadgetEdges R S
```

prove named lemmas:

```lean
lemma r2_edges_semiprime
lemma r2_edges_avoid
lemma r2_edges_dvd_period
lemma ctrlEdges_subset_r2_edges
```

All hypotheses should be explicit; do not hide construction choices.

### Target C: block-minor ready lemma

Prove a wrapper that packages the hypotheses needed to invoke
`minor_arc_bound_fiber_tail` on the block-minor set.  It is acceptable for the
wrapper to take the actual fiber-tail bound as a hypothesis:

```lean
theorem r2_block_minor_bound
  ...
```

The goal is to isolate the exact hypothesis list that the final assembly must
supply.

## Deliverable

Return:

1. files changed;
2. theorem names proved;
3. `lake build RequestProject.R2AssemblySkeleton`;
4. axiom traces for the nontrivial endpoint lemmas.

If Target C is too large, complete Targets A and B first.  They are immediately
useful and should be sorry-free.
