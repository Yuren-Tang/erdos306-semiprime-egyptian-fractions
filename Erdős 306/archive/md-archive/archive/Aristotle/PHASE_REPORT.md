# Erdős 306 — Phase Report (current session)

This session continued the final-phase task of `TASK.md`: taking the verified
single-block package toward a sorry-free `erdos_306` by translating notes `34`
(global control) and `35` (circle method).

## Build status

`lake build` is **green** end-to-end. (The project layout was first repaired:
the `.lean` sources were flattened into the repo root but the lakefile/imports
expect them under `RequestProject/`; they were moved there.)

## What was completed

### Circle method extraction layer (note 35 C0/C5) — `CircleMethod.lean` (NEW)

* `Wcount` — the deterministic weighted count over subsets `S ⊆ E` (note 35 C0).
* `exists_subset_of_Wcount_pos`, `Wcount_pos_imp_repr` — **PROVED.** The
  "`W > 0 ⟹ subset extraction ⟹ representation`" step (note 35 C5): a positive
  weighted count yields a subset of squarefree-semiprime edges avoiding `T` whose
  reciprocals sum to `1/b`, i.e. `HasEgyptianSemiprimeReprAvoiding T (1/b)`.
* `fourier_orthogonality` — **PROVED.** Finite additive-character orthogonality
  on `ZMod L` (note 35 C0, "pure finite algebra"): the underlying inversion
  identity.
* `circle_method_positivity` — assembles the analytic positivity with the
  extraction layer to produce the representation.

### Closing the `FourierPositivity` sorry — `FourierPositivity.lean`

`fourier_positivity_unconditional` is **no longer a `sorry`**; it is now proved
by `CircleMethod.circle_method_positivity`. Consequently the *entire downstream
wiring* of `erdos_306` is sorry-free, and the whole problem is reduced to a
single precisely-named analytic residual (see below).

### Phase-G global control skeleton (note 34) — `GlobalControl.lean` (NEW)

* `BlockSystem` (G0) — blocks `Pₖ ⊆ primes ∩ [2ᵏ,2ᵏ⁺¹)` with density
  `|Pₖ| ≥ 2ᵏ/(2 log 2ᵏ)`, `k₀ ≤ k ≤ K`.
* `BlockSystem.irvingGood` — **PROVED.** Bridge lemma: each block is
  `SBEEAssembly.IrvingGood`, connecting the global layer to the verified
  single-block package.
* `Hglob`, `internalPairs`, `bipartitePairs`, `ctrlPairs`, `Qctrl`, `sigmaCtrl`,
  `mainArc` — the global control energy/data of G0/G6 (definitions).
* `Qctrl_nonneg`, `sigmaCtrl_nonneg` — **PROVED.**
* Headline results stated with precisely-named `sorry`s (each with a one-line
  reason): `crossblock_dispersion` (G2), `mismatch_penalty` (G3),
  `global_levelset` (G5), `global_control_partition` (G7, = Prop 8.1).

## Axiom trace

`#print axioms erdos_306` →
`[propext, sorryAx, Classical.choice, Quot.sound]`.

The only non-standard axiom is `sorryAx`, which enters **solely** through
`CircleMethod.exists_positive_weighted_construction`.

## Sorry inventory

**On the `erdos_306` dependency path (1 residual):**

* `CircleMethod.exists_positive_weighted_construction` — the analytic heart of
  the circle method (note 35 C1–C4): the edge construction (C1, needs the block
  density input `π(2x)−π(x) ≥ x/(2 log x)`), the pointwise Fourier bound (C2),
  the main-arc lower bound (C3), and the minor-arc upper bound via Phase-G global
  control (C4). Bundled as one existence statement so no false intermediate
  general lemma is asserted.

**Phase-G skeleton, off the `erdos_306` path (4 residuals, note 34):**

* `GlobalControl.crossblock_dispersion` (G2) — deterministic; `lemmaD` pattern,
  fiber ≤ 1. (A subagent attempt reproduced the full proof skeleton — residue
  counting + nearest-integer bound — but timed out; genuinely multi-step.)
* `GlobalControl.mismatch_penalty` (G3).
* `GlobalControl.global_levelset` (G5) — the segment encoding ("Peierls"
  content).
* `GlobalControl.global_control_partition` (G7) — Laplace step on G5.

**Superseded placeholders, off the `erdos_306` path (annotated DEPRECATED):**

* `SBEE.lean` — old SBEE lemma chain (5 `sorry`s).
* `SingleBlockCounting.lean` — abstract target (1 `sorry`).
* `BlockCRTEnergy.lean` — `*_uniform` stubs (4 `sorry`s). The CRT-energy
  *definitions* in this file remain in active use (incl. by `GlobalControl.lean`).

## Per-phase status vs. `TASK.md`

* **Phase G** — file created; G0 data + `IrvingGood` bridge proved; G2/G3/G5/G7
  stated as precisely-named residuals.
* **Phase C** — file created; C0 extraction layer + orthogonality identity
  proved; C5 assembled; C1–C4 isolated as the single analytic residual.
* **Phase W** — layout repaired; build green; superseded placeholders annotated
  DEPRECATED; axiom trace + sorry inventory above.

## Honest expectation

Per `TASK.md`'s own honest expectations, the residual analytic content
(G2/G3/G5/G7 and C1–C4) is the "labor-heavy" part and is multi-session work.
This session delivered the faithful structural translation, proved the
self-contained pieces (extraction, orthogonality, IrvingGood bridge), and
reduced `erdos_306` to a single precisely-named analytic residual while keeping
the build green throughout.
