# R2 Assembly Skeleton Bookkeeping Completed

Back to [[52 R2 Assembly Skeleton Next Task]].

## What Was Added

`RequestProject/R2AssemblySkeleton.lean` now builds sorry-free.

It formalizes the finite edge-set layer needed before the final
`exists_arcConstruction` assembly:

- `gadgetEdges R S = image (fun (r,s) => r*s) (R × S)`;
- membership expansion for gadget edges;
- gadget semiprimality under explicit prime and order hypotheses;
- gadget divisibility into
  `primeSupportPeriod b (blockSupport BS)`;
- gadget avoidance from pairwise avoidance;
- provisional R2 edge set

  ```lean
  r2Edges BS Q R S = ctrlEdges BS ∪ Q ∪ gadgetEdges R S
  ```

- subset inclusions for the three components;
- semiprimality, avoidance, and period-divisibility wrappers for the union.

## Theorem Names

The new useful endpoints are:

```lean
CircleMethod.gadgetEdges_semiprime
CircleMethod.gadgetEdges_dvd_period
CircleMethod.gadgetEdges_avoid_of_pair_avoid
CircleMethod.r2_edges_semiprime
CircleMethod.r2_edges_avoid
CircleMethod.r2_edges_dvd_period
```

The build command was:

```bash
lake build RequestProject.R2AssemblySkeleton
```

and it completed successfully.

Axiom traces for all six endpoint lemmas are standard only:

```text
[propext, Classical.choice, Quot.sound]
```

## Interpretation

This closes Targets A and B of note 52.  It does **not** close the final R2
construction.  The real remaining assembly is now narrower:

1. choose the concrete `R` of denominator primes and enough block-support
   primes `S`;
2. choose the block-aligned mass batch `Q`;
3. use the new union lemmas to populate the easy `ArcConstruction` fields;
4. prove the `hminor` field by splitting frequencies into:
   - block-minor frequencies handled by `minor_arc_bound_fiber_tail`;
   - extra-minor frequencies handled by the sibling gadget damping from
     `ExtraMinorDamping.lean`;
5. feed the exact-mass construction into `theta`.

The work is therefore not blocked by semiprime/period bookkeeping anymore.  It
is concentrated in the monolithic construction of the final edge set and the
minor-arc split.

## Local Follow-Up

`RequestProject/R2MinorAssembly.lean` has also been started locally.  It proves
the pure finite-sum partition needed for the final `hminor` split:

```lean
CircleMethod.blockMinorPart
CircleMethod.extraMinorPart
CircleMethod.minorParts_union_eq_of_cover
CircleMethod.sum_le_of_minor_split_bounds
CircleMethod.r2_minor_bound_split
```

This is deliberately only the finite bookkeeping layer.  It does not yet invoke
`minor_arc_bound_fiber_tail` or `gadget_charFun_damp`; it provides the wrapper
shape into which those two estimates should feed.

## Suggested Next Prompt

Ask for a new file or extension, still avoiding the whole theorem in one jump:

```text
Extend RequestProject/R2AssemblySkeleton.lean or create
RequestProject/R2MinorAssembly.lean.

Goal:
prove a wrapper theorem `r2_minor_bound_split` whose hypotheses are exactly:

1. a block-minor hypothesis supplied in the form needed by
   `minor_arc_bound_fiber_tail`;
2. an extra-minor sibling assignment hypothesis supplied in the form needed by
   `gadget_charFun_damp`;
3. a partition of `range L \ SM` into block-minor and extra-minor frequencies.

The theorem should conclude the `hminor`-shaped bound needed by
`ArcConstruction`.

Do not choose final numeric constants yet.  The aim is to expose the exact
interface between block-minor and extra-minor, not to solve mass selection or
the full `exists_arcConstruction` in one theorem.
```
