# R2 Construction Design - Multipity Is Not Enough

Back to [[00 README]]. This note updates the R2 construction frontier after
reading `HANDOFF_erdos306.md`, the latest state file, note [[35 Circle Method -
Detailed Spec (Translation-Ready)]], and the current Lean files in
`~/erdos-lean-build`.

## 0. Current Machine State

The circle-method analytic capstone is now verified once an
`ArcConstruction T b` is supplied. The remaining R2 theorem is:

```lean
CircleMethod.exists_arcConstruction
  (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
  Nonempty (ArcConstruction T b)
```

Banked infrastructure includes:

- `exists_blockSystem`, with Rosser--Schoenfeld dyadic prime density as the
  single named classical input;
- `ctrlEdges`, `ctrlEdges_semiprime`, `ctrlPairs_prod_injOn`;
- `QE_ge_Qctrl`;
- `minor_arc_bound_mult`, allowing a bounded multiplicity factor;
- `fourierTerm_eq_term_label_of_cong` / `_of_modL`;
- `exists_mainArc_bijection`;
- `MassBatch.exists_largePrimeProduct_batch_recip_between`;
- candidate `FiberCount.mainArc_fiber_card_le`, proving multiplicity `≤ b` when
  `L = b * ∏ p ∈ blockSupport BS, p`.

The last item is useful only if the final period has no mass primes outside
`blockSupport`.

## 1. The Fork

R2 has two incompatible-looking requirements:

1. Minor-arc control wants frequencies to be summarized by their residues on
   `blockSupport BS`, because `G7` controls exactly `Qctrl BS`.
2. Mass tuning wants many semiprime denominators with total reciprocal mass
   around `1/b`, and the easiest verified source is `MassBatch`, whose products
   may live far above the block range.

If all edge primes lie in `blockSupport`, then the frequency map on
`Finset.range L` has multiplicity `b` after adjoining the squarefree denominator
`b`, and `FiberCount.mainArc_fiber_card_le` is the right lemma.

If mass primes lie outside `blockSupport`, then the multiplicity is not `b`.
It is roughly the product of the extra primes appearing in the period. This may
be enormous.

## 2. Why Naive Multiplicity Is Not The Right Fix

`minor_arc_bound_mult` gives

```text
minor ≤ M * (η + Ctail * exp(-C^2 * 8/9)) / sigmaCtrl BS
```

where `M` is a fiber bound for

```lean
h ↦ (fun p : {p // p ∈ blockSupport BS} => (h : ZMod p.1)).
```

If the mass batch uses extra primes outside the blocks, then
`M = L / ∏ blockSupport` includes those extra primes. Since the mass batch is
chosen precisely by taking many large prime products, this `M` can be huge and
depends on the batch.

One cannot simply say "choose `η` tiny" after seeing `M`: in the construction,
`η` feeds into `global_control_partition_final`, hence into the required lower
bound on `BS.k0`; the mass batch and its period are then chosen after `BS`.
This creates a parameter cycle. It may be breakable with a carefully quantified
fixed-point argument, but it is no longer the clean R2 route and should not be
treated as bookkeeping.

## 3. Why Pure Block-Aligned Mass Is Also Suspect

`admissibleGlobalRange BS` is currently:

```lean
2 * BS.k0 ≤ BS.K ∧ BS.K ≤ 3 * BS.k0
```

Thus a purely block-aligned mass batch can only use primes in dyadic blocks
`k0, ..., 3k0`. Heuristically,

```text
∑_{p in blocks} 1/p ≈ ∑_{k=k0}^{3k0} 1/k ≈ log 3,
```

and the reciprocal mass available from unordered prime products is about

```text
(log 3)^2 / 2 ≈ 0.60.
```

The common-weight mass trick needs a batch reciprocal load in
`[3/(2b), 3/b]`. For `b = 2`, this lower endpoint is `0.75`.

This is not a proof of impossibility, but it is strong evidence that insisting
on all mass primes inside the current block range is the wrong design. It also
matches the paper construction's use of high-scale mass/gadget edges.

## 4. Corrected R2 Target

The right next target is not to close `exists_arcConstruction` directly and not
to lean harder on `minor_arc_bound_mult`. Instead, prove a strengthened minor
arc lemma that uses the damping from extra mass/gadget edges instead of throwing
it away as a multiplicity factor.

The desired structure is:

1. Let `Pctrl = blockSupport BS`.
2. Let `Pextra` be the extra primes appearing in `E` but not in `Pctrl`.
3. Let `L = b * ∏ p ∈ Pctrl, p * ∏ p ∈ Pextra, p`, with pairwise coprime
   squarefree support.
4. Split the minor frequencies into:
   - block-minor frequencies, where the projection to `Pctrl` is outside
     `mainArc BS C`;
   - extra-minor frequencies, where the block projection is on the diagonal
     main arc but at least one extra coordinate is not compatible with the same
     label.

For the block-minor part, do **not** use the raw multiplicity bound unless
`Pextra` is tiny. Instead prove a fiberwise energy bound of the form:

```lean
∑ h in fiber_over_block_assignment a,
  Real.exp (-(16/9) * QE E h)
≤ C_extra * Real.exp (-(16/9) * Qctrl BS a)
```

where `C_extra` is harmless because the extra-edge energy is retained. The
current `minor_energy_sum_le_mult` is the special case `C_extra = M`, obtained
by discarding all extra energy; that is too crude for mass batches.

For the extra-minor part, prove a direct CRT/product estimate: if the block
coordinates are diagonal with label `m` but an extra coordinate is not, then at
least one extra edge has nonzero phase distance, and the product bound gives
enough damping after summing over the extra residue coordinates.

## 5. Concrete Lean Lemma To Aim For

Introduce a new construction-side support split, probably in a new file
`RequestProject/ArcConstructionExtra.lean`:

```lean
def edgePrimeSupport (E : Finset ℕ) : Finset ℕ := ...
def extraPrimeSupport (BS : BlockSystem) (E : Finset ℕ) : Finset ℕ :=
  edgePrimeSupport E \ blockSupport BS
```

Then replace the final use of `minor_arc_bound_mult` in R2 by a stronger lemma:

```lean
theorem minor_arc_bound_with_extra_energy
    (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail Cextra : ℝ), 0 < Ctail ∧ 0 < Cextra ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (Sm : Finset ℕ),
      -- usual theta/L/positivity hypotheses
      -- E contains ctrlEdges BS
      -- exact support decomposition hypotheses
      -- extra-edge damping hypotheses
      ‖∑ h ∈ Sm, fourierTerm E theta b L h‖
        ≤ (η + Ctail * Real.exp (-C^2 * (16/9) / 2)) / sigmaCtrl BS
          + Cextra * (extraMinorTail E theta C)
```

The statement above is schematic; the key is that the extra part must be a
tail, not a raw product of extra primes. Once such a lemma exists, mass primes
may live outside `blockSupport`, and `MassBatch` becomes usable without
exploding the minor arc.

## 6. Immediate Decision

Do **not** try to finish `exists_arcConstruction` using only the current
`minor_arc_bound_mult` unless the construction is changed to keep all mass
primes inside `blockSupport`. The latter appears numerically inadequate for
`b = 2` under `K ≤ 3k0`.

The next honest mathematical task is therefore:

> Build the extra-prime minor-arc estimate retaining `QE` on the extra
> coordinates, or prove a quantified fixed-point version showing the huge
> multiplicity can still be absorbed.

The first route is cleaner and closer to the actual Fourier mechanism.
