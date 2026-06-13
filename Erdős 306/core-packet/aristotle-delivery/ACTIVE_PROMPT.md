# ACTIVE TASK: close G5 — prove `global_levelset_final` (hrhs N5 assembly)

## DONE already — do NOT redo
`g6_localization` (now in `RequestProject/GlobalControlG6.lean`) is COMPLETE and
integrated. `GlobalControlSectorI.lean` is complete. The hrhs sub-lemmas N1–N4 in
`RequestProject/GlobalControlG5Assembly.lean` (`pow_beats_poly_log`,
`labelBound_charge_hot`, `label_product_le`, `fiber_card_exp_bound`, plus the
frozen cover layer in `GlobalControlG5Data.lean`: `cover_card_le`, the 5
admissibility facts, `hrhs_inner`, `global_levelset_route`) are PROVED. The ONLY
remaining Phase-G sorry is `global_levelset` (G5).

## Startup — DO NOT rebuild the verified core (follow ORDER)
1. `lake exe cache get`  (Mathlib only)
2. if sources were flattened to repo root, move them back under `RequestProject/` FIRST
3. `tar xzf prebuilt-oleans.tar.gz -C .lake/build/lib/lean/`  (refreshes olean mtimes
   so lake replays instead of rebuilding the ~40-min core)
4. `lake build RequestProject.GlobalControlG5Assembly`  (should elaborate only your work)

## Work ONLY in the leaf `RequestProject/GlobalControlG5Assembly.lean`
Do NOT edit `GlobalControl.lean`, `GlobalControlG5Data.lean`, `GlobalControlG6.lean`,
`GlobalControlSectorI.lean`, `GlobalControlG7.lean`, `CircleMethod*.lean`.

## Task: prove `global_levelset_final` (= the hrhs N5 assembly)
State and prove, in namespace `GlobalControl`, a lemma with the EXACT signature of
`GlobalControl.global_levelset` (copy it from `GlobalControl.lean` — the
`∃ k0min A, 0 < A ∧ ∀ BS, k0min ≤ k0 → admissibleGlobalRange BS → ∀ R ≥ 1,
ncard{a | Qctrl ≤ R} ≤ exp(A·numBlocks)·exp(8εR)·(1+√R/σ)` statement), named
`global_levelset_final`, sorry-free. (We keep it in the leaf to avoid the cyclic
import; G7 will be repointed to it.)

**Proof = N5 assembly** (note `42 hrhs Completion Spec for Aristotle.md`, the N5
section, + notes 39/40 for the skeleton). Use the verified inputs:
- `global_levelset_route` (GlobalControlG5Data) reduces the target to `hrhs`
  (the ∑∑∑∑ fiber.card bound) + existential facts.
- `hrhs` = the ε-budget assembly: per-block `fiber_card_le` + `hot_factor`/
  `cold_factor` → `fiber_card_exp_bound` (N3, done); `label_product_le` (N4, done);
  `labelBound_charge_hot` (N1, done); `shell_sum_bound`/`weighted_subset_entropy`
  for the H- and B-sums; combine constants → `exp(A·numBlocks)`, budget 6ε ≤ 8ε.
- **The first-segment subtlety (the N5 obstruction you flagged before):** the initial
  segment (`segStart = k0`) label window is `L0 ≈ √R/σ_{k0}`, paid ONCE as the
  `√R/σctrl` factor in the target (NOT block-by-block). Route it via
  `sigmaCtrl_le_sigmaP_k0` (σctrl ≤ c_σ·k0·σ_{k0}, so `L0 = 7√R/σ_{k0} ≤
  7 c_σ k0 · √R/σctrl`); the extra `k0` factor is absorbed into `exp(A·numBlocks)`
  since `numBlocks ≥ k0` (admissible). This is bookkeeping, not new math.

If a sub-step genuinely resists, isolate it as ONE precisely-named `sorry` and close
everything else; report the residual. Axiom-check `global_levelset_final`.
