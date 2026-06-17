# Summary of changes for run 61e3433b-fab1-407a-8adb-131bff40692a
Completed this round's Phase-G work in `RequestProject/GlobalControl.lean` (with a project-structure fix), keeping the build green throughout.

**Project structure fix.** The `.lean` sources were at the repository top level but the lakefile/`import RequestProject.*` lines expect them under `RequestProject/`. I moved all sources into `RequestProject/` and refreshed the Mathlib dependency, so `lake build` now compiles the whole project successfully.

**G2 — cross-block dispersion (`crossblock_dispersion`): fully proved.** Mirroring the verified single-block dispersion engine (`dispersion_residue_count`/`dispersion_energy_bound`) one level up, with the easier "fiber ≤ 1" geometry. Added and proved two reusable helpers:
- `nndist1_ratio_ge` — phase lower bound `1/q ≤ ‖n/q‖` when `q ∤ n`.
- `crossblock_residue_count` — at most `|P|/4+1` of the primes have small phase.
The main bound splits into a trivial small-`|P|` case (each phase `≥ 1/q`) and the dispersion case.

**G3 — mismatch penalty (`mismatch_penalty`): corrected and fully proved; the original statement was FALSE.** I found and machine-verified a counterexample: with `m = ∏_{p∈P k} p` and `m' = 0` the labels are `≠` yet every control representative is `crtRepr p q 0 0 = 0` (verified), so the bipartite energy is `0` below the positive bound. The original statement omitted the cold-label size hypotheses of note 34 G3. I preserved the false statement (commented out) with a documented finding, and stated a corrected version restoring faithful label-size hypotheses (`hm`, `hm'`) and the block-density regularity used by the dispersion count (`hNk`, `hNk1`). It is proved via new reusable lemmas:
- `nndist1_le_abs`, `nndist1_add_intCast` — basic `nndist1` facts.
- `crossblock_phase_bridge` — the modulus-`q` CRT↔phase identity `‖(m'-m)·p̄/q‖ ≤ |H|/(pq) + |m|/(pq)`.
- `mismatch_per_q` — the per-vertex dispersion bound `|P|³/(2¹³X²)`.
The assembly sums over the `≥ N_{k+1}/2` "good" vertices `q ∤ m'-m` (bad vertices bounded by ≤ 1).

**Remaining residuals (precisely-named, documented sorries).** `global_levelset` (G5, the segment-encoding "Peierls" argument) and `global_control_partition` (G7, the Laplace step on G5). These are the labor-heavy parts and additionally require an extraction layer (L2–L5) from the single-block package that is not yet present; they are left as documented named sorries, an acceptable terminal state per the task.

Notes: the corrected `mismatch_penalty` retains the original block-range hypotheses `hk1`/`hk2` (note 34 G0) for faithfulness even though the finished proof does not use them (this produces only unused-variable warnings). The file header status section was updated to reflect G2/G3 proved and G5/G7 outstanding.