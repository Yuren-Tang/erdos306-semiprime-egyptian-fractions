# R2 Mass Batch Completed

Back to [[50 R2 Construction Resolved - Gadget Cancellation and the b≥3 Reduction]].

## Result

Aristotle's R2-mass package has been integrated into the core Lean source and
validated locally.

The main file is:

```text
lean/RequestProject/BlockMassPool.lean
```

Two lightweight dyadic files were also integrated:

```text
lean/RequestProject/DyadicBlockDef.lean
lean/RequestProject/DyadicPrimes.lean
```

`BlockSystemConstruction.lean` now imports `DyadicPrimes` rather than defining
the dyadic block and the two analytic inputs inline.

## Build

In the warm build project:

```text
lake build RequestProject.BlockMassPool
```

completed successfully.  The only warning is the intentional unused interface
hypothesis `hbsf : Squarefree b` in `exists_blockAligned_mass_batch`.

## New Lean Endpoints

The mass-pool file now contains:

```lean
CircleMethod.blockPrimes
CircleMethod.blockPrimes_prime
CircleMethod.blockPrimes_ge
CircleMethod.blockPrimes_lt
CircleMethod.blockPrimes_subset_Ico

CircleMethod.blockPrimes_sub_sq_tail
CircleMethod.blockPrimes_pair_prod_injOn
CircleMethod.blockPrimes_product_load_ge_of
CircleMethod.exists_subset_recip_window
CircleMethod.exists_blockAligned_mass_batch_of

CircleMethod.blockPrimes_product_load_ge
CircleMethod.exists_blockAligned_mass_batch
```

The already-banked algebraic identity remains:

```lean
CircleMethod.sq_sum_eq_sum_sq_add_two_sum_lt
```

## Axiom Trace

```text
'CircleMethod.blockPrimes_sub_sq_tail' depends on axioms:
  [propext, Classical.choice, Quot.sound]

'CircleMethod.blockPrimes_product_load_ge' depends on axioms:
  [propext, Classical.choice, GlobalControl.dyadic_mertens_cumulative, Quot.sound]

'CircleMethod.exists_blockAligned_mass_batch' depends on axioms:
  [propext, Classical.choice, GlobalControl.dyadic_mertens_cumulative, Quot.sound]
```

Thus the only non-standard dependency of the R2-mass batch is the named Mertens
input already introduced in note 50.

## Mathematical Meaning

For every finite obstruction set `T` and squarefree `b ≥ 3`, there are arbitrarily
late block primes from which one can select a finite batch `Q` of distinct
squarefree semiprime denominators, all made from block primes and avoiding `T`,
such that

```text
3/(2b) ≤ ∑_{e∈Q} 1/e ≤ 3/b.
```

This closes the mass-load part of the R2 construction after the separate
`b = 2` reduction.  The remaining R2 work is now assembly:

1. define the concrete edge set with the mass batch plus gadget siblings;
2. set common weights, probably `theta e = 1/2` on the selected batch/gadgets or
   a uniform value in `[1/3,2/3]` adjusted to exact mass;
3. use the extra-minor damping lemmas from `ExtraMinorDamping.lean`;
4. use block-minor control from `ExtraEnergyMinorArc.lean`;
5. populate `ArcConstruction` and close `exists_arcConstruction`.
