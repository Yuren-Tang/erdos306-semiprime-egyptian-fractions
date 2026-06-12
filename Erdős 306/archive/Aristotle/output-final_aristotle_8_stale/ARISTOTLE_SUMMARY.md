# Summary of changes for run 6d0d0010-2ea3-4c25-841d-34a825e884f5
I worked on the Phase-G / Phase-C continuation described in note `36`, in `RequestProject/GlobalControl.lean` (and reviewed `RequestProject/CircleMethod.lean`). The whole project builds cleanly. Concretely:

**1. Faithful finite global-assignment interface (note 36 §0) — done.** I added `blockSupport BS` (the finite set of primes appearing in some block), `GlobalAssignment BS` as the finite dependent product `(p : {p // p ∈ blockSupport BS}) → ZMod p.1`, a `NeZero` instance making the type a genuine `Fintype`, the extension map `toPlain`, and the helper `ctrlPairs_mem_blockSupport`. I rewrote `Qctrl`, `mainArc`, `global_levelset`, and `global_control_partition` over this finite type, so the level-set "counts" are now honest cardinalities of a finite type rather than `Set.ncard` of an infinite domain. G2/G3 (already proved) were left intact.

**2. Exceptional G3 corollary — proved.** `mismatch_penalty_with_exceptions` (note 36 §0): the bipartite mismatch penalty for cold blocks carrying a bounded exception set, obtained by rerunning `mismatch_per_q` over the reduced vertex sets `Pₖ\Eₖ` and `Pₖ₊₁\Eₖ₊₁`. It uses only the standard axioms.

**3. Faithfulness correction to the G5/G7 statements.** The previously-stated `global_levelset`/`global_control_partition` quantified their constants *after* `BS`, which makes them vacuously true (one can take the constant to be the finite total number of assignments and bound the level set by the whole space, since every right-hand factor is ≥ 1). The automated prover indeed closed G5 by exactly this artifact — which note 36 explicitly forbids. I therefore restated both theorems with the threshold `k0min` and the constants quantified *uniformly over all block systems* (with hypothesis `k0min ≤ BS.k0`), which is the faithful form, and reverted G5 to a documented `sorry`.

**What remains open (honest status).** Three deep theorems are still `sorry`:
- `global_levelset` (G5) — the segment-encoding "Peierls" injective decoder;
- `global_control_partition` (G7) — the Laplace/dyadic summation + G6 localization, which depends on G5;
- `CircleMethod.exists_positive_weighted_construction` (Phase C / C1–C5) — the full circle-method analytic heart, which depends on G7.

These constitute the genuine research core of the argument: closing G5 in its faithful (non-vacuous) form requires the full segment-encoding decoder with the L1–L5 single-block inputs and the five cardinality/injectivity bounds; G7 and Phase C build on top of it (Construction structure, `sigmaE`, CRT bijection, main-arc Taylor with exact mass cancellation, minor-arc via G7). I was not able to formalize these in this session, and I did not take the only available shortcut because it is precisely the vacuity artifact the task rules out. The single-block foundation they would build on (`SBEEAssembly.unified_levelset`, `single_block_counting`, and the new `mismatch_penalty_with_exceptions`) is verified sorry-free, so the scaffolding for a future completion is in place and faithfully stated.

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