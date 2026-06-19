# ⚠️ FINISH your own ~95%-complete proof (R2TopAssembly.lean)

Your previous run built the entire construction + all the `have`s of
`exists_arcConstruction_final` but **ran out of time before the closing step**. The file
currently does NOT compile. Finish it — this is the last `sorry`/error blocking `erdos_306`.

Iterate fast: `lake env lean RequestProject/R2TopAssembly.lean` (single file, deps cached;
single-threaded). Goal: that command returns with **no error and no `sorry`** in this file.

## Exactly what's left (from `lake env lean`)

1. **The goal at `exists_arcConstruction_final` (line ~654) is never closed.** The proof
   ends at `h2N1sigma` with a chain of `have`s but no final `exact`. Write the closing
   assembly:
   - You already proved `r2_buildFreqLanes` (sorry-free): it gives
     `Nonempty (R2MinorEndgameFrequencyLanes D W N Bblock Bextra η Ctail (N:ℝ) Dmp
     (mainArcClassificationData D W N C))` with `Bblock = b·(η+Ctail·e^{−C²·8/9})/σ`,
     `Bextra = b·(2N+1)·Dmp`. Apply it with your `D W N C η Ctail Dmp G` and the `have`s.
   - Feed the lanes to `exists_r2_minorReady_from_frequency_lanes` (your `hMR` at line ~662)
     to get `R2MinorReadyData D W N`.
   - Feed that + the component supply (`R2ComponentScaleCoreSupply` — build its 14 fields from
     your structural/scale `have`s, `r0=2`, `s0=2^k0`) + `QB` to the arc endpoint
     `exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_minorReady`
     (`R2MinorReadyArc`), supplying the socket inequalities from your `have`s
     (`hNsigma`, `h2N1sigma`, `hsigmaE_ub/lb`, the component-card and beat bounds).

2. **Fix line ~755** (`hgadgetAvoid`, `nlinarith` hit max recursion). Use a direct argument:
   `s ≤ r*s` (since `r ≥ 2 > 0`), `2^{2k0} ≤ s` (`hSge`), and `r*s < 2^{2k0}` (`hTlt`), then
   `omega`.

3. **Fix lines ~765–766** (the `r2_extra_inv_sq_le` application — syntax / `omega` / `rewrite`
   failures). The `|R| = b.primeFactors.card ≤ b` bound is `Finset.card_le_card` into `Icc 1 b`;
   restructure the term so it parses and the side goals close.

4. **Delete the 3 unused dead lemmas** `r2_pow_dom`, `r2_edge_lower`, `r2_period_lower`
   (lines ~621–643) — they are NOT referenced anywhere; remove them (don't leave their sorries).

## Constraints
- Do NOT convert `dyadic_prime_density`, `dyadic_mertens_cumulative`,
  `dyadic_control_recipLoad_eventually_small` from `axiom` to `theorem := by sorry` — keep them
  as **named axioms** (they are cited classical inputs; `DyadicPrimes.lean` / `R2BaseLoadUpper.lean`
  in this package already have them as axioms — leave them).
- Edit ONLY `RequestProject/R2TopAssembly.lean`. No other file's sorry is on the path.
- Report whether the file ends with zero `sorry`/error. That closes `erdos_306` to its 3 cited axioms.
