# R2 Extra Support Bookkeeping Completed

Back to [[46 R2 Construction Design - Multiplicity Is Not Enough]] and
[[47 R2 Extra Support Bookkeeping Task]].

## Result

The bounded note-47 task has been completed locally in Lean:

```text
lake build RequestProject.ArcConstructionExtra
```

finished successfully in the warm build directory on 2026-06-14.

The file extended is:

```text
lean/RequestProject/ArcConstructionExtra.lean
```

The same source has been copied into the warm build project
`~/erdos-lean-build/RequestProject/ArcConstructionExtra.lean`.

## New Lean Names

Basic support lemmas:

```lean
CircleMethod.mem_extraPrimeSupport
CircleMethod.edgePrimeSupport_mono
CircleMethod.edgePrimeSupport_union
CircleMethod.edgePrimeSupport_insert
```

Edge divisibility and support-period helpers:

```lean
CircleMethod.all_edges_dvd_edgePrimeSupport_prod
CircleMethod.primeSupportPeriod
CircleMethod.edge_dvd_primeSupportPeriod_of_mem_support
CircleMethod.semiprime_edge_dvd_primeSupportPeriod
```

Control skeleton support:

```lean
CircleMethod.edgePrimeSupport_ctrlEdges_subset_blockSupport
```

Fiber-count alias:

```lean
CircleMethod.blockSupport_frequency_fiber_card_le
```

## Axiom Trace

For the nontrivial new endpoints:

```text
'CircleMethod.edgePrimeSupport_ctrlEdges_subset_blockSupport' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'CircleMethod.blockSupport_frequency_fiber_card_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'CircleMethod.semiprime_edge_dvd_primeSupportPeriod' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

## Mathematical Meaning

The control skeleton is now known to introduce no primes outside the block
support:

```lean
edgePrimeSupport (ctrlEdges BS) ⊆ blockSupport BS
```

For arbitrary semiprime edge sets, every edge divides the period formed from the
edge-prime support:

```lean
e ∈ E, IsSemiprime e
  ==> e ∣ primeSupportPeriod b (edgePrimeSupport E)
```

Thus the next R2 step can cleanly distinguish:

- control primes, already handled by `blockSupport BS`;
- extra mass/gadget primes, collected by `extraPrimeSupport BS E`;
- periods formed by multiplying the denominator `b` with the relevant prime
  support.

This removes a bookkeeping ambiguity from note 46.  The remaining difficulty is
not finite support management; it is the stronger minor-arc estimate that retains
extra-edge energy rather than replacing extra coordinates by a raw multiplicity
factor.

## Next Frontier

The old note-47 outsource task should no longer be sent as new work.  If it has
already been sent, the returned result can be used as an independent check.

The next honest task is to formulate and prove the extra-energy minor-arc
interface replacing the crude use of `minor_arc_bound_mult` in the construction
of `CircleMethod.exists_arcConstruction`.
