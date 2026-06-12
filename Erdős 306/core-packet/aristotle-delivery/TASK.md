# Aristotle delivery — FINAL PHASE: complete the Erdős 306 formalization

**Upload this whole folder** (`lake build`). This is the final task package: it
takes the machine-verified SBEE single-block theorem all the way to a sorry-free
`erdos_306`. **The mathematics is fully written out for translation** in the
included notes `34` (global control) and `35` (circle method); notes `29`/`30`/`32`
document the verified single-block layer. **Translate, don't rediscover.** Where a
step resists, isolate it as a precisely-named `sorry` with a one-line reason and
move on; if a written step is WRONG, say so explicitly — that is the most
valuable report. Keep ALL hypotheses faithful (window/density/primality/size
bounds — past statements broke from omitted hypotheses).

State: sorry-free & verified — `SBEEDispersion.lean` (dispersion engine),
`SBEEFingerprint.lean` (Theorem C), `SBEEForcing.lean` (Theorems A, B, Lemma E),
`SBEEAssembly.lean` (`single_block_counting : SBEEPartitionBound c`). The one
intended open sorry: `fourier_positivity_unconditional` (`FourierPositivity.lean`)
— **this package closes it**.

This will take multiple sessions; phases are ordered. Complete and report each
phase; partial progress is fine — the build must stay green at every step.

## Phase G — global control (note 34; new file `GlobalControl.lean`)

* **G0**: `BlockSystem` (blocks $P_k\subseteq$ primes∩$[2^k,2^{k+1})$, density
  $|P_k|\ge2^k/(2\log2^k)$, $k_0\le k\le K$), control pairs (internal + consecutive
  full bipartite), `Qctrl`, `sigmaCtrl`. Each block is `IrvingGood` (bridge lemma).
* **G1 extractions** (small lemmas from the proved single-block package): L2 cold
  ⟹ unique dominant label; L3 label range; L4 exception bound ($\le R_k/E_1$, cold
  ⟹ $\le e_0$ absolute); L5 dominant count given label. (The proofs of
  `theorem_A_dominant_count` / `theorem_B_nondominant_forcing` contain these;
  restate standalone.)
* **G2 cross-block dispersion** (full proof in note 34): reuse the `lemmaD`
  pattern; fiber $\le1$ here (interval length $\le$ modulus/2).
* **G3 mismatch penalty** $\Pi_k$ (full proof in note 34).
* **G4 hot absorption** (numeric).
* **G5 Theorem G** (global level-set; the encoding — six recorded data items,
  decoder injective; full proof in note 34).
* **G6 main-arc localization** + **G7 Prop 8.1** (partition form; Laplace step =
  the verified `partfun_series_bound` pattern).

## Phase C — circle method (note 35; new file `CircleMethod.lean`)

* **C0**: Construction structure; the weighted count `W`; the finite Fourier
  identity (orthogonality on `ZMod L` — pure algebra).
* **C1**: edge construction exists (CP 03 §9 translation; note 35). External
  input: Chebyshev block density $\pi(2x)-\pi(x)\ge x/(2\log x)$ — use Mathlib if
  available, else isolate as the named hypothesis `chebyshev_block_density`
  (do NOT silently weaken).
* **C2**: pointwise bound $|\widehat\mu(h)|\le e^{-\frac{16}9Q_E(a(h))}$
  (computation in note 35; extend `product_charFun_bound`).
* **C3**: main arc $\ge c_3(C)/\sigma_E$ (explicit Taylor; note 35).
* **C4**: minor arc via G7 + CRT bijection + $Q_E\ge Q_{\rm ctrl}$.
* **C5**: positivity ⟹ subset extraction ⟹ **close
  `fourier_positivity_unconditional`**.

## Phase W — wiring & cleanup

1. `#print axioms erdos_306` — confirm sorry-free end-to-end (standard axioms only).
2. Deprecate/derive the superseded placeholders (old `SBEE.lean` chain,
   `SingleBlockCounting.lean` abstract target, `BlockCRTEnergy.lean` `*_uniform`).
3. Final report: full sorry inventory of the package (should be empty or
   precisely-named residuals), axiom trace, build log.

## Honest expectations

G5/G7 and C1/C3 are the labor-heavy parts; all are elementary with written
proofs. If `chebyshev_block_density` is the only residual named input, that is an
acceptable terminal state (documented elementary provable input); everything else
should close. Report per-phase.
