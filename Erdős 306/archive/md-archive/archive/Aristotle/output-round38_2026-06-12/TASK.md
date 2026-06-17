# Aristotle delivery — MASTER PLAN to a sorry-free `erdos_306`

**Upload this whole folder** (`lake build`). This single document is the
complete, ordered task list from the current state to the end. Work the steps
IN ORDER; keep the build green after every step; partial completion is fine —
whatever closes, closes. **Translate, don't rediscover**: every remaining
mathematical step has a written proof in the included notes (38 is the main
one for Phase G; 35 + 37 §6 for Phase C).

## Ground rules (unchanged, binding)

* Do NOT weaken any statement; keep every hypothesis. Constants quantified
  uniformly (never after the block system / object being counted).
* If a step resists, isolate it as a precisely-named `sorry` with a one-line
  reason and MOVE ON to the next step that doesn't depend on it.
* If a written step is WRONG, say so explicitly — that is the most valuable
  possible report.
* Only allowed named external input: `chebyshev_block_density` (Phase C), and
  only if Mathlib lacks it.

## Current state (verified — do NOT redo)

* Sorry-free: the whole SBEE single-block package (`SBEEDispersion`,
  `SBEEFingerprint`, `SBEEForcing`, `SBEEAssembly.single_block_counting`),
  `GlobalControl` G2 (`crossblock_dispersion`), G3 (`mismatch_penalty`,
  `mismatch_penalty_with_exceptions`), the finite `GlobalAssignment`
  interface, and `GlobalPeierlsBookkeeping.lean` (4 abstract lemmas).
* `erdos_306` is wired end-to-end with ONE named sorry
  (`CircleMethod.exists_positive_weighted_construction`); `GlobalControl` has
  two more (`global_levelset` G5, `global_control_partition` G7).
* **Note `38` is new and authoritative for Phase G.** It contains complete
  proofs for everything below, including three corrections (note 38 §0) —
  read §0 first.

## Phase G — close G5 and G7 (note 38; this is the bulk)

**G-0 (statement correction, note 38 §0 C-a).** Strengthen
`admissibleGlobalRange` to `2*BS.k0 ≤ BS.K ∧ BS.K ≤ 3*BS.k0`. (Needed to
absorb the `k0` factor of the sigma comparison; the construction takes
`K ≈ 3k0`, so this is faithful.)

**G-1 (new abstract lemma, `GlobalPeierlsBookkeeping.lean`).**
`shell_sum_bound` — note 38 §1, full proof given (geometric discount over
shell vectors). NOTE: the existing `prod_local_count_le` is NOT sufficient for
the encoding; this lemma is what the assembly actually uses.

**G-2 (block decomposition, `GlobalControl.lean`).** D1 windows disjoint,
`restrict` def, D2 joint injectivity, D3 energy splits, D4 product count —
note 38 §2, proofs given.

**G-3 (extraction lemmas, in/next to `SBEEForcing.lean`).** Note 38 §3,
proofs given:
* `dominant_label_unique` (L2u) — **use the two-prime proof of note 38; the
  earlier note-37 §4 single-prime sketch is WRONG.**
* `fixed_label_count` (L5) — verbatim extraction of the `hfibcard` block
  inside the proved `theorem_A_dominant_count` (no `htriv` split needed).
* `cold_exception_bound` (L4c) — corollary of `exception_count_bound`.
* `L3c` cold-label size chain.
(L1 = `unified_levelset`, L2 = contrapositive of
`theorem_B_nondominant_forcing`, L3 = `theoremA_label_range` are used as-is;
fix `ρ := 1/4`.)

**G-4 (sigma lemmas, `GlobalControl.lean`).** S1 `σ_{k0} ≤ σctrl`,
S2 `σctrl ≤ 4·2^{−k0} ≤ 1`, S3 `σctrl ≤ c_σ·k0·σ_{k0}` — note 38 §4, proofs
given.

**G-5 (THE assembly: `global_levelset`).** Note 38 §5 — full proof: trivial
regime split (step 0), hot/cold/labels/boundaries (steps 1–3), the covering
fibration (step 4, mirrors the proved `hcover`/`hfibcard` pattern of
`theorem_A_dominant_count` two levels up), per-factor table with the ε-budget
(step 5, total 6ε ≤ 8ε). Do it concretely in `GlobalControl.lean` (no further
abstract layer); private helper defs welcome; bundle all `k0 ≥ k0min` numeric
comparisons into one threshold lemma.

**G-6 (localization lemma).** Note 38 §6, proof given (uses
`exception_single_energy`, `crtRepr_eq_label`, G3).

**G-7 (`global_control_partition`).** Note 38 §7 — full proof:
`partfun_series_bound` with G5 at `ε = c/32` (step 1), sector I via the
`F0(BS)` floor + `admissibleGlobalRange` numeric (step 2 — this is where
`k0min(η,c)` is chosen), sector II via the standalone `gaussian_int_sum_le`
(statement + elementary proof in note 38 §7).

## Phase C — circle method (notes 35 + 37 §6)

Split `CircleMethod.exists_positive_weighted_construction` into named lemmas
C1a (Construction structure), C1b (edge construction; may use the named input
`chebyshev_block_density`), C2 (pointwise `|μ̂(h)| ≤ e^{−(16/9)Q_E}`,
extend `product_charFun_bound`), C3 (main arc `≥ c₃(C)/σ_E`; exact mass
cancellation), C4 (minor arc = G7 + CRT bijection + `Q_E ≥ Q_ctrl`), C5
(positivity ⟹ close it). Computations are in note 35; file split in note 37
§6. If a specific C-step stalls, name it precisely — a note-38-grade
elaboration of that step will be supplied next round.

## Phase W — wiring & final report

1. `#print axioms erdos_306` — confirm standard axioms only (or precisely
   `chebyshev_block_density` as the sole extra named input).
2. Deprecate superseded placeholders (old `SBEE.lean` chain,
   `SingleBlockCounting.lean` abstract target, `BlockCRTEnergy.lean`
   `*_uniform`).
3. Final report: sorry inventory (empty or precisely-named), axiom trace,
   build log.

## Honest expectations

G-5 is the labor-heavy step but now has a complete written proof with the
encoding bookkeeping spelled out (including the shell-sum fix and the trivial
regime split that earlier notes glossed). G-1 through G-4 are short and
independent — close them first in one pass even if G-5 then takes longer.
Acceptable terminal state for a session: any prefix of the ordered list
closed, the rest as named sorries.
