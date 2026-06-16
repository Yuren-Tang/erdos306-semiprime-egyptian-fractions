This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Erdős Problem 306 — Lean 4 formalization (squarefree-denominator case)

A Lean 4 / Mathlib formalization of the circle-method approach to **Erdős
Problem 306** (<https://www.erdosproblems.com/306>), restricted to the
squarefree-denominator case:

> **Theorem (`erdos_306`).** Let `b` be a squarefree positive integer. For every
> positive integer `a` there is a finite set of *distinct squarefree semiprimes*
> `n₁, …, n_k` (each `nᵢ = pᵢ qᵢ`, a product of two distinct primes) with
> `a / b = ∑ᵢ 1 / nᵢ`.

The squarefree hypothesis is necessary (`necessity_squarefree_denom`,
`RequestProject/Defs.lean`).

> ⚠️ **Honest status.** This is a *substantial, partially verified* formalization,
> **not** a complete proof. The theorem statement is faithful and the entire
> circle-method analytic core is machine-verified, but the proof currently rests
> on **one isolated, documented `sorry`** — the block-aligned construction
> `CircleMethod.exists_arcConstruction`. Accordingly `#print axioms erdos_306`
> reports `sorryAx`. See **[Verification status](#verification-status)** below.

## Entry point

Open **`RequestProject/Erdos306Unconditional.lean`**. Its module header is the
authoritative, self-contained description of the statement, the proof
architecture, the verification status, and the cited classical inputs. The file
ends with `#print axioms erdos_306` so the dependency trace is visible on build.

## Building / verifying

* Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (see `lean-toolchain`,
  `lakefile.toml`, `lake-manifest.json`).
* Prebuilt object files for this package are shipped in
  `prebuilt-oleans.tar.gz` (extract at the repository root to restore
  `.lake/build/lib/lean/RequestProject/…`). Mathlib itself is fetched/built by
  `lake`.

```sh
tar xzf prebuilt-oleans.tar.gz      # optional: restore this package's .olean files
lake build                          # builds RequestProject (Mathlib from cache)
```

A successful build prints
`'erdos_306' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`.

## Verification status

| Component | Where | Status |
|---|---|---|
| Statement `erdos_306` (faithful) | `Erdos306Unconditional.lean` | ✓ stated |
| Reduction `a/b ⇝ 1/b` (denominator-avoiding) | `MainTheorem.lean` | ✓ verified |
| Circle-method analytic core: *construction ⇒ positivity ⇒ representation* | `CircleMethodAssembly.exists_pos_weighted_of_construction` | ✓ verified, sorry-free |
| `b = 1`, `b = 2` reductions (`1 = 1/2+1/3+1/6`, `1/2 = 1/3+1/6`) | `CircleMethodAssembly.lean` | ✓ verified |
| Concrete `1/b` instances (b = 2,3,5,7,11) + triple-prime identity | `Erdos306Unconditional.lean` | ✓ verified |
| **The block-aligned construction** `exists_arcConstruction` | `CircleMethodAssembly.lean` | ✗ **open `sorry`** (the only gap reachable from `erdos_306`) |
| `R2*` reduction of the construction to supply estimates | `RequestProject/R2*.lean` | ✓ sorry-free, but not yet grounded in a concrete block system |
| Phase-G global control / SBEE minor-arc analysis | `GlobalControl*.lean`, `BlockCRTEnergy.lean`, `SBEE*.lean` | partial; named `sorry`s for the unfinished analytic content (not reachable from `erdos_306`) |

The verified core `exists_pos_weighted_of_construction` is checked to be
sorry-free (`#print axioms` shows only `propext, Classical.choice, Quot.sound`),
which confirms that the *only* gap reachable from `erdos_306` is
`exists_arcConstruction`.

## Cited classical inputs (isolated named axioms)

The `R2*` reduction of the construction gap relies on standard, peer-reviewed
prime-distribution facts, isolated as named, individually documented axioms:

* `GlobalControl.dyadic_prime_density` — Rosser & Schoenfeld, *Approximate
  formulas for some functions of prime numbers*, Illinois J. Math. **6** (1962),
  Corollary 3. (`RequestProject/DyadicPrimes.lean`)
* `GlobalControl.dyadic_mertens_cumulative` — Mertens' theorem, cumulative dyadic
  form. (`RequestProject/DyadicPrimes.lean`)
* `CircleMethod.dyadic_control_recipLoad_eventually_small` — the matching
  Mertens-level reciprocal upper estimate. (`RequestProject/R2BaseLoadUpper.lean`)

They are recorded as axioms only because the corresponding quantitative
estimates are not yet available at the required strength in Mathlib (cf. the
`PrimeNumberTheoremAnd` project). They do not currently appear in the axiom
trace of `erdos_306` (the `R2*` reduction is not yet wired into
`exists_arcConstruction`); they are documented here so a verifier can recognise
them as cited results rather than proof failures.

## Project layout

* `RequestProject/Erdos306Unconditional.lean` — **entry point** (statement, proof,
  status, citations).
* `RequestProject/Defs.lean`, `MainTheorem.lean`, `SemiprimeInfinity.lean` —
  basic definitions, the numerator reduction, semiprime supply.
* `RequestProject/CircleMethod*.lean`, `BernoulliFourier.lean`, `LatticeSpan.lean`,
  `FourierPositivity.lean` — the circle-method analytic core.
* `RequestProject/GlobalControl*.lean`, `BlockCRTEnergy.lean`, `SBEE*.lean`,
  `CrossLabelEnergy.lean` — Phase-G global control / SBEE minor-arc development
  (carries the remaining named analytic `sorry`s).
* `RequestProject/R2*.lean`, `BlockMassPool.lean`, `DyadicBlockDef.lean`,
  `DyadicPrimes.lean`, `ArcConstruction*.lean`, … — the (sorry-free) reduction of
  the construction gap to concrete supply estimates.
* `notes/` — archived development notes, plans, logs, and task files (reference
  only; many are outdated or superseded). See `notes/README.md`.

## Caveat on completeness

Because of the open `sorry` in `exists_arcConstruction`, this repository should be
cited as a *formalization of the squarefree case modulo the explicit
block-aligned construction lemma*, not as a complete machine-checked proof of
Erdős 306.
