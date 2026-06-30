/-
# Global Control — translation of note `34` (Phase G)

This file translates note `34` ("Global Control: Detailed Proof"), the
block-to-global chain (CP 03 §§5–8 / Prop 8.1).  The argument mirrors the
verified single-block proof one level up: *blocks* play the role *vertices*
played inside a block, and the deterministic dispersion (`linearCongruence_pair_count` pattern)
suffices because the Peierls penalties exceed the entropies.

## Section map (note 34)

* **G0** — `BlockSystem`, control pairs, the global control energy `Qctrl` and
  deviation `sigmaCtrl`.  The **faithful finite global-assignment
  interface** (note 36 §0) is now in place: `blockSupport`, `GlobalAssignment`
  (a finite dependent product over the block support), and `Qctrl`/`sigmaCtrl`/
  `mainArc`/`global_levelset`/`global_control_partition` are stated over it, so
  the level-set counts are honest cardinalities of a finite type.
* **G2** — cross-block dispersion (`crossblock_dispersion`).  Self-contained
  number theory; **proved** (deterministic, `linearCongruence_pair_count` pattern; fiber ≤ 1), via
  `unitCircleNorm_ratio_ge` and `crossblock_residue_count`.
* **G3** — mismatch penalty `Πₖ` (`mismatch_penalty`).  **Proved (corrected
  statement)** — the original statement is FALSE (label-size hypotheses were
  omitted; see the finding in the G3 section).  Assembled from
  `crossblock_phase_bridge` and `mismatch_per_q`.  The **exceptional corollary**
  `mismatch_penalty_with_exceptions` (note 36 §0, for cold blocks with a bounded
  exception set) is also **proved**.
* **G-2** — block decomposition (note 38 §2).  **Proved:** `blocks_disjoint`
  (D1), `restrict_injective` (D2), `restrict_filter_card_le` (D4),
  `QP_restrict_eq_internal` and `energy_splits` (D3).
* **G-4** — sigma comparison (note 38 §4).  **Proved:** `sigmaP_block_le` (S1),
  `sigmaCtrl_le_one`/`sigmaCtrl_le_geom` (S2), `sigmaCtrl_le_sigmaP_k0` (S3),
  with `block_card_le` and `sigmaP_sq_eq_internal`.
* **G5** — the global level-set route is completed downstream by
  `global_levelset` in `GlobalControl.LevelSetAssembly`.  Its constants are
  quantified *uniformly* over all block systems.  Its supporting layer is
  proved here: G-1
  (`GlobalPeierls.shell_sum_bound`), G-2, G-4, and the single-block extraction
  lemmas `LocalEnergy.dominant_label_unique` (L2u),
  `LocalEnergy.fixed_label_level_set_bound` (L5), `LocalEnergy.cold_exception_count_bound`
  (L4c).
* **G7** — Prop 8.1 is completed by `global_control_partition` in
  `GlobalControl.Partition`, from the level-set theorem, localization, and the
  two Laplace sectors.
  Constants are likewise uniform over block systems.

These results feed the minor-arc bound of the circle method (note 35 C4,
`CircleMethod.exists_positive_weighted_construction`).

## Status

Faithful Phase-G translation.  G0 data, G2/G3, and the
full note-38 §2/§4 support layer (block decomposition G-2 and sigma comparison
G-4) are proved.  The headline G5 and G7 assemblies are completed in
`GlobalControl.LevelSetAssembly` and `GlobalControl.Partition`.  No new analytic input is
required beyond the verified single-block package (`LocalEnergy.LevelSet`),
`GlobalPeierls.shell_sum_bound`, and `linearCongruence_pair_count`.
-/
import RequestProject.GlobalControl.Partition
