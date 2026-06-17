# G5 (`global_levelset_final`) — status and the single residual

## What is proved (sorry-free, axiom-clean: `propext`, `Classical.choice`, `Quot.sound`)

In `RequestProject/GlobalControlG5Assembly.lean`:

- `cold_master` — a single constant triple `(c2, e0, X0)` simultaneously
  providing block dominance (`SBEEForcing.IsDominant`) and the boundary penalty
  floor, both for the **same** `c2` (obtained from `boundary_penalty_per_k`,
  whose cold facts already expose the residue agreement that yields dominance
  once `X0` is large enough that block density forces `N_k ≥ 4 e0`).
- `hadmL_final` — the label-range admissibility `hadmL`: for `k0` past a uniform
  threshold, the zero-extended cold labels of any `Qctrl ≤ R` assignment lie in
  `admLabels` (routes `coldLabel_mem_labelFin` through every segment start).
- `global_levelset_final` — the **exact** statement of
  `GlobalControl.global_levelset`, fully assembled from `cold_master`,
  `hadmL_final`, `hrhs_final`, and the verified `global_levelset_route`.
  (Its only non-standard axiom is `sorryAx`, entering solely through
  `hrhs_final`.)

These build on the previously-proved N1–N4 layer (`pow_beats_poly_log`,
`labelBound_charge_hot`, `label_product_le`, `fiber_card_exp_bound`,
`admLabels_card`, `sum_subset_charge_le`) and the frozen cover/route layer.

## The single residual `sorry`: `hrhs_final`

`hrhs_final` (the four-fold fiber-sum bound
`∑_H ∑_B ∑_v ∑_ℓ fiber.card ≤ exp(A·numBlocks)·exp(8εR)·(1+√R/σctrl)`) is a
**true** statement but is left as one precisely-named `sorry`.  This is a genuine
mathematical obstruction, not a translation gap:

- The note-42 "N5" route factors the inner sum as
  `|admLabels| · (per-fiber bound)` via `hrhs_inner`, where the per-fiber bound
  is `fiber.card ≤ ∏_k exp(2ε(v_k+1))` supplied by `fiber_card_exp_bound`.
- That per-fiber bound — and its hypothesis `hlabsize`
  (`|ℓ(segStart k)| ≤ N_k·2^k/16` for every cold `k`) — is **false** for the
  **initial** segment (`segStart = k0`) once `R` is large.  There the label
  window is `L0 = ⌈7√R/σ_{k0}⌉`, which already exceeds the `cold_factor` size
  threshold `N_{k0}·2^{k0}/16` for `R ≳ 2^{2k0}/poly(k0)`.  A single large
  first-segment label can have a fiber count comparable to a small one, so the
  `√R/σctrl` factor in the target **cannot** be produced as a count of label
  choices; it must be charged **collectively** against the first segment's
  energy.
- A two-regime split (block-by-block for small `R`, `trivial_regime` for large
  `R`) does not close the problem: the small-`R` regime reaches only
  `R ≲ 2^{2k0}/poly`, while `trivial_regime` requires
  `R ≥ ε⁻¹·2^{K+2}·(K+1)` (up to `~2^{3k0}` under `admissibleGlobalRange`),
  leaving a nonempty middle regime uncovered.

Closing `hrhs_final` therefore requires a **segment-level joint counting lemma**
(a fixed-label count valid for arbitrarily large labels, charging the whole
first cold segment collectively via the `σctrl`/S3 machinery).  Such a lemma is
not present in the frozen core (`SBEEForcing`/`GlobalControl`), and the project's
own notes flag exactly this as "the remaining obstruction … not a pure
translation of the note-42 plan."  Building it is a substantial new development
beyond the assembly task.
