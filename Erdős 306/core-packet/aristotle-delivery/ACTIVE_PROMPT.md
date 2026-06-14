# ACTIVE TASK: close `hrhs_final` (the last G5 residual) — see note 45

## DONE already — do NOT redo
`global_levelset_final`, `cold_master`, `hadmL_final` are assembled and integrated
(your previous round). The ONLY remaining sorry under `global_levelset_final` is
`hrhs_final` in `RequestProject/GlobalControlG5Assembly.lean`. g6, Sector-I, the
N1–N4 layer, and the cover/route layer are all proved.

## Startup (the upload drops `.lake`; restore it from the tar)
1. `lake exe cache get`  (Mathlib only)
2. if sources were flattened to repo root, move them back under `RequestProject/` FIRST
3. `mkdir -p .lake/build/lib/lean && tar xzf prebuilt-oleans.tar.gz -C .lake/build/lib/lean/`
4. `lake build RequestProject.GlobalControlG5Assembly`

## Work ONLY in `RequestProject/GlobalControlG5Assembly.lean`
(do NOT edit `GlobalControl.lean`, `GlobalControlG5Data.lean`, or the other files.)

## Task: close `hrhs_final` — read note `45 hrhs_final via Theorem-A (G5 last residual).md`
Your own diagnosis was correct: the first-segment large label (`L0 ≈ √R/σ_{k0}`)
breaks `fiber_card_exp_bound`'s `hlabsize`. **The fix is NOT new math** — it routes
the first segment through the ALREADY-VERIFIED `theorem_A_dominant_count` /
`fixed_label_count`:

- **Key fact (note 45): the fixed-label fiber count is label-translation-invariant.**
  For a *fixed* dominant label `m` of block `P_k`, the count of conforming
  block-assignments does NOT depend on `|m|` (the bijection `a_p ↦ a_p + (m'-m)` on
  the `(1-ρ)N_k` conforming primes). So the per-fiber bound `∏_k exp(2ε(v_k+1))`
  holds for ANY `ℓ` — `hlabsize` is unnecessary. This is exactly the content of
  `fixed_label_count` (the `theorem_A_dominant_count` component you already have,
  proved for `|m| ≤ X²/2`).
- **Plan:**
  1. `fiber_card_exp_bound'` — re-prove `fiber_card_exp_bound` WITHOUT the
     `hlabsize` hypothesis (cold blocks via `fixed_label_count` for any label; hot
     blocks via `hot_factor` as before).
  2. `hrhs_final` — re-run your `hrhs_inner` assembly with `fiber_card_exp_bound'`,
     so the first-segment large label is admissible. The `√R/σctrl` slot comes from
     `admLabels_card`'s initial window `L0` via `sigmaCtrl_le_sigmaP_k0`
     (`σctrl ≤ c_σ·k0·σ_{k0}`); the `k0` factor folds into `exp(A·numBlocks)`
     (admissible ⇒ `numBlocks ≥ k0`). NO regime split needed — one route for all `R`.

If a step resists, isolate the SMALLEST precisely-named sorry and close the rest.
Axiom-check `global_levelset_final` (should be sorry-free if `hrhs_final` closes).
Keep it focused — this is the endgame.
