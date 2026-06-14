# R2 Minor-Split Assembly Interface

Read `53 R2 Assembly Skeleton Bookkeeping Completed.md` first.

The file `RequestProject/R2AssemblySkeleton.lean` is already present and builds
sorry-free.  Do **not** redo gadget-edge or union-edge bookkeeping.  The next
task is to isolate the `hminor` interface for the final R2 construction.

## Context

The final R2 edge set has the shape

```lean
r2Edges BS Q R S = ctrlEdges BS ∪ Q ∪ gadgetEdges R S
```

The easy fields for `ArcConstruction` now have wrappers:

```lean
CircleMethod.r2_edges_semiprime
CircleMethod.r2_edges_avoid
CircleMethod.r2_edges_dvd_period
```

The remaining difficult field is the minor-arc bound.  It should be proved by
splitting minor frequencies into:

1. block-minor frequencies, handled by
   `CircleMethod.minor_arc_bound_fiber_tail`;
2. extra-minor frequencies, handled by the gadget sibling damping theorem
   `CircleMethod.gadget_charFun_damp`.

## Task

Create a new leaf file:

```text
RequestProject/R2MinorAssembly.lean
```

with imports:

```lean
import RequestProject.R2AssemblySkeleton
import RequestProject.ExtraEnergyMinorArc
import RequestProject.ExtraMinorDamping
```

Prove a wrapper theorem with a name like:

```lean
theorem r2_minor_bound_split
  ...
```

The theorem should **not** choose final numeric constants.  Instead it should
make the exact interface explicit.

The intended proof shape is:

1. Let `Sm` be the full minor-frequency Finset.
2. Let `Sblock` and `Sextra` be two Finsets with
   `Sm ⊆ Sblock ∪ Sextra`.
3. Assume a block-minor sum bound on `Sblock`, in the exact form produced by
   `minor_arc_bound_fiber_tail` or a direct corollary of it.
4. Assume an extra-minor sum bound on `Sextra`, in a form whose hypotheses are
   close to `gadget_charFun_damp`.
5. Conclude a combined minor bound over `Sm` by monotonicity and finite-sum
   splitting.

It is acceptable, and likely best, to first prove a pure finite-sum lemma:

```lean
lemma sum_le_of_subset_union_bounds
  {α : Type*} [DecidableEq α]
  (Sm Sblock Sextra : Finset α) (F : α → ℝ)
  (hFnonneg : ∀ x ∈ Sm, 0 ≤ F x)
  (hcover : Sm ⊆ Sblock ∪ Sextra)
  (hblock : ∑ x ∈ Sm.filter (fun x => x ∈ Sblock), F x ≤ A)
  (hextra : ∑ x ∈ Sm.filter (fun x => x ∈ Sextra), F x ≤ B) :
  ∑ x ∈ Sm, F x ≤ A + B
```

If this exact statement is awkward because of duplicate overlap, use the
disjointized version:

```lean
SblockPart = Sm.filter (fun x => x ∈ Sblock)
SextraPart = Sm.filter (fun x => x ∉ Sblock ∧ x ∈ Sextra)
```

and prove the corresponding partition identity/bound.  This is probably easier.

## Deliverable

Return:

1. files changed;
2. theorem names proved;
3. `lake build RequestProject.R2MinorAssembly`;
4. axiom traces for the endpoint lemmas;
5. a short explanation of the exact remaining hypotheses that final
   `exists_arcConstruction` must supply.

Keep the new theorem sorry-free if possible.  If a statement requires a larger
refactor, isolate the smallest precise `sorry` and explain why.
