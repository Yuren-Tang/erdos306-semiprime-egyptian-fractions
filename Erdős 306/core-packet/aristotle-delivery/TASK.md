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
  interface, and `GlobalPeierlsBookkeeping.lean` (5 abstract lemmas incl.
  `shell_sum_bound`).
* **The note-38 support layer is CLOSED (last round): G-0 through G-4 and
  three of the four G-3 extraction lemmas are proved** —
  `admissibleGlobalRange` strengthened, `shell_sum_bound`, `restrict` /
  `blocks_disjoint` / `restrict_injective` / `restrict_filter_card_le` /
  `energy_splits`, `sigmaP_block_le` / `sigmaCtrl_le_one` /
  `sigmaCtrl_le_sigmaP_k0`, `dominant_label_unique`, `fixed_label_count`,
  `cold_exception_bound`. Only **L3c** (cold-label size chain, note 38 §3)
  remains from the support layer.
* Exactly three sorries on the `erdos_306` chain: `global_levelset` (G5),
  `global_control_partition` (G7),
  `CircleMethod.exists_positive_weighted_construction` (Phase C).
* **Note `38` is authoritative for Phase G** — complete proofs, three
  corrections in §0 (already applied to statements).

## Goal of this session: go as far as you can — ideally all the way

**The note-39 G5 skeleton is INSTANTIATED and most holes are CLOSED** (last
round): all setup definitions (`blockEnergy`/`Rw`/`isHot`/`hotSet`/`coldLabel`/
`boundarySet`/`shellVec`/`segStarts`/`segStart`/`Pifloor`/`labelRange`/
`classCount`/`fiber`) plus holes 1 (`coldLabel_spec`, `coldLabel_eq`),
2 (`cold_isDominant`), 4 (`segStart_le/ge/run`), 5 (`coldLabel_eq_segStart`),
7 (`fiber_card_le`), 9 (`cold_factor`), 11 (`trivial_regime`), and the
hole-8 numeric core `hot_threshold` + `inv_sigmaP_bound` — all sorry-free.
**Do not redo any of these.**

Remaining: the hole-8 glue (`hot_factor`), holes 3, 6, 10, 12 (= G5), then
G7, Phase C, Phase W. **Note `40` is now binding**: it quarters exactly these
into sub-lemmas of ≤ 30–60 lines each, every one with a complete proof, in
closing order. **If the steps keep closing, do NOT stop at a phase boundary —
the intended terminal state is a sorry-free `erdos_306`.**

## Working rules for the remaining holes (note 40)

1. **Read note 40's three structural notes (N-a/N-b/N-c) first** — they
   correct/simplify the assembly: no trivial-regime split is needed; the
   shell-data Finset must carry the hot-consistency filter; the INITIAL
   segment label ranges over the `√R`-window `L0`, NOT `labelRange`.
2. Work sub-lemma by sub-lemma in note-40 order (§1 hot_factor glue; §2 =
   3a, 3b, 3c, 3d-i…iv; §3 = 6c, 6a, 6b, 6d + the data-Finset defs; §4 =
   10a, 10b, 10c; §5 = hole 12 assembly). State ALL of them with `sorry`
   first, get the file compiling, THEN close them one at a time. Every
   closed sub-lemma is durable; never attempt a multi-sub-lemma jump.
3. The proofs in note 40 are complete — translate; if a constant chase
   misses, widen the constant/threshold rather than redesigning (statement
   shapes are binding, constants are lavish by design).

Then G7 (note 38 §7 / note 40 §6; `gaussian_int_sum_le` is already proved),
then Phase C, then Phase W, as below.

## Phase G — close G5 and G7 (note 38; this is the bulk)

**G-0 … G-4: DONE last round (see "Current state"). Do not redo.**

**L3c (the one remaining support lemma).** Cold-label size chain — note 38 §3,
proof given (`theoremA_label_range` + `sigmaP_lower` + the cold threshold).
Both conclusions (`|m| ≤ N·X/16` for L5/L4c, and the `hm`-type bounds of
`mismatch_penalty_with_exceptions`) follow from
`|m| ≤ 168√c2·X^{3/2}/√(log X) ≤ X²/(64 log X)` for `X ≥ X0(c2)`.

(For the assembly: L1 = `unified_levelset`, L2 = contrapositive of
`theorem_B_nondominant_forcing`, L3 = `theoremA_label_range`, L2u/L5/L4c =
last round's extractions; fix `ρ := 1/4`.)

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
