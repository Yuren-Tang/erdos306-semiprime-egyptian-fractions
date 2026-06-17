# Note 45 — closing `hrhs_final` (the G5 residual) via verified Theorem A

**Target.** `GlobalControl.hrhs_final` in `GlobalControlG5Assembly.lean`:
`∑_H ∑_B ∑_v ∑_ℓ fiber.card ≤ exp(A·numBlocks)·exp(8εR)·(1+√R/σctrl)`.
This is the last sorry under `global_levelset_final` (hence under G7's
`global_control_partition_final`).

## Aristotle's correct diagnosis
The note-42 route bounds the inner sum by `|admLabels|·(per-fiber)` where the
per-fiber bound `fiber_card_exp_bound` carries the hypothesis
`hlabsize : |ℓ(segStart k)| ≤ N_k·2^k/16`. For the **initial** segment
(`segStart=k0`) the label window is `L0=⌈7√R/σ_{k0}⌉`, which exceeds
`N_{k0}·2^{k0}/16` once `R ≳ 2^{2k0}/poly` — so `hlabsize` fails there
(middle-R regime, between block-by-block and `trivial_regime`).

## The resolution (NO missing idea — uses verified Theorem A)
**Key fact: the fixed-label fiber count is label-translation-invariant.** For a
*fixed* dominant label `m` of a block `P_k`, the count of block-assignments with
dominant label `m` (and energy shell `v_k`) does NOT depend on `|m|`: the
dominant structure is `(1-ρ)N_k` primes with `a_p ≡ m (mod p)` plus `≤ e0`
exceptions; replacing `m` by `m'` is the bijection `a_p ↦ a_p + (m'-m)` on the
conforming primes, so the count is the same. Hence the per-fiber bound
`fiber.card ≤ ∏_k exp(2ε(v_k+1))` holds for **any** `ℓ`, and `hlabsize` is an
unnecessary hypothesis (it was inherited from `cold_factor`'s small-label range,
but the *count* is translation-invariant). This is exactly the content of
`theorem_A_dominant_count`'s internal `fixed_label_count` (note 38 L5, verified
in `SBEEForcing`), which is proved for `|m| ≤ X²/2` — i.e. all relevant labels.

**Therefore the `√R/σ` factor is simply the number of first-segment labels.**
`|admLabels|` (Aristotle's `admLabels_card`) already supplies the initial window
`L0 ≈ 7√R/σ_{k0}` as a separate factor (`label_product_le` = "initial window ×
hot/boundary products"). With `sigmaCtrl_le_sigmaP_k0` (`σctrl ≤ c_σ·k0·σ_{k0}`)
this `√R/σ_{k0}` becomes `≤ c_σ·k0·√R/σctrl`, and the `k0` factor is absorbed by
`exp(A·numBlocks)` (admissible ⇒ `numBlocks ≥ k0`). The non-initial segment
labels are paid by the Peierls boundary weight (`label_product_le` non-initial
factor `e^{εw}`), unchanged.

## Concrete formalization plan
1. **`fiber_card_exp_bound'`** — re-state `fiber_card_exp_bound` WITHOUT
   `hlabsize` (or with it dropped for `segStart=k0`), proving the per-fiber bound
   `fiber.card ≤ ∏_k exp(2ε(v_k+1))` from `fixed_label_count` (the
   `theorem_A_dominant_count` component) via the translation bijection. The hot
   blocks still use `hot_factor`; cold blocks use `fixed_label_count` (any label).
   *(The only new content: confirm `fixed_label_count`/`theorem_A_dominant_count`
   gives the per-label count uniformly in `|m|` — it does, proved for `|m|≤X²/2`.)*
2. **`hrhs_final`** — repeat Aristotle's `hrhs_inner` assembly but with
   `fiber_card_exp_bound'` (no `hlabsize`), so the first-segment large label is
   admissible. The `√R/σctrl` slot comes from `admLabels_card`'s initial window
   via `sigmaCtrl_le_sigmaP_k0`; the `k0` factor folds into `exp(A·numBlocks)`.
   No regime split needed (one route for all `R`).

## Status note
This corrects the earlier "first-segment routing is bookkeeping" claim: it needs
a real lemma (`fiber_card_exp_bound'`, dropping `hlabsize`), but the mathematical
ingredient (translation-invariant fixed-label count = `theorem_A_dominant_count`)
is already machine-verified. So G5 has **no missing mathematical idea**; closing
`hrhs_final` is reachable formalization using a verified component. Size: a
moderate single new lemma + re-running the assembly — suitable for a focused round
(keep it small per the endgame time budget).
