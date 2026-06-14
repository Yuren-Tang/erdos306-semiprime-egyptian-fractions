# R2 Minor Estimates Into Split Wrapper

`RequestProject/R2MinorAssembly.lean` is now present.  It proves the pure
finite-sum splitter:

```lean
CircleMethod.blockMinorPart
CircleMethod.extraMinorPart
CircleMethod.minorParts_union_eq_of_cover
CircleMethod.sum_le_of_minor_split_bounds
CircleMethod.r2_minor_bound_split
```

Do **not** redo this finite-sum lemma.  The next task is to connect the two real
minor estimates to this wrapper.

## Task

Create or extend:

```text
RequestProject/R2MinorEstimateInterface.lean
```

with imports:

```lean
import RequestProject.R2MinorAssembly
import RequestProject.ExtraEnergyMinorArc
import RequestProject.ExtraMinorDamping
```

Prove two wrapper lemmas, with theorem statements as concrete as possible:

1. a `block_part_bound` wrapper that rewrites the hypotheses of
   `CircleMethod.minor_arc_bound_fiber_tail` into a bound over
   `blockMinorPart Sm Sblock`;
2. an `extra_part_bound` wrapper that rewrites the hypotheses of
   `CircleMethod.gadget_charFun_damp` into a bound over
   `extraMinorPart Sm Sblock Sextra`.

Then prove a combined theorem, for example:

```lean
theorem r2_hminor_bound_from_block_and_extra
  ...
```

whose proof is:

```lean
exact CircleMethod.r2_minor_bound_split ... hcover hblock hextra
```

## Important

The goal is interface discovery, not final constants.  It is acceptable for the
combined theorem to take explicit numeric/analytic bounds as hypotheses, as long
as the statement shows exactly what final `exists_arcConstruction` still has to
supply.

Return:

1. file(s) changed;
2. theorem names;
3. build result for `lake build RequestProject.R2MinorEstimateInterface`;
4. axiom traces for endpoint lemmas;
5. the final remaining hypothesis list.
