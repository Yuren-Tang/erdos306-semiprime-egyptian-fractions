# Summary of changes for run a53d640a-96d2-4849-b1a6-b58a6f0582e9
I followed `TASK.md` (the note-38 master plan toward a sorry-free `erdos_306`) and made concrete, verified progress, keeping the build green throughout.

**Project-layout fix.** The `.lean` sources were sitting at the repository root, but the lakefile expects them under `RequestProject/` (module names `RequestProject.*`). I moved them back, so the whole project compiles again (`lake build`, 8057 jobs, green).

**New proved lemmas (sorry-free, standard axioms only).**
- `SBEEForcing.cold_label_size` — **Lemma L3c** (cold-label size chain, note 38 §3), the one remaining support lemma the task flagged as outstanding. For a cold block (`R ≤ c₂·X/log³X`) with dominant label `m`, it gives `|m| ≤ N·X/16` for `X ≥ X0(c₂)`. With L3c proved, the note-38 support layer is now complete.
- `SBEEForcing.exists_X0_const_logbnd` — a parametrized log-vs-linear threshold (`∀ K, eventually K·log X ≤ X`), generalizing the existing `exists_X0_logbnd`; used by L3c.
- `GlobalControl.gaussian_int_sum_le` — the standalone elementary Gaussian integer-sum bound `∑_{m∈ℤ} exp(-A·m²) ≤ 1 + 6/√A` for `0 < A ≤ 1` (note 38 §7), the analytic input for the G7 Gaussian-tail sector.

**Remaining work (the deep research core).** Three named sorries remain, exactly the ordered list's tail after L3c:
- `GlobalControl.global_levelset` (G5) — the segment-encoding "Peierls" decoder (note 38 §5). This is a several-hundred-line covering/encoding assembly: the per-block √R/σ factors must be charged only per cold *segment* (via `segment_label_constant`), not per block, or the product bound blows up. A direct high-effort proof attempt timed out, matching the experience of prior runs. All of its inputs are now in scope and proved (L1–L5, the new L3c, G3-with-exceptions, S1–S3, D1–D4, the shell/subset-entropy lemmas, and segment constancy).
- `GlobalControl.global_control_partition` (G7) — depends on G5; its Gaussian-tail input is now available (`gaussian_int_sum_le`).
- `CircleMethod.exists_positive_weighted_construction` (Phase C) — depends on G7.

This matches the task's accepted terminal state: the L3c prefix of the ordered list is now closed (together with a G7 analytic input), and the remaining deep steps are left as precisely-named sorries with one-line reasons in their docstrings. The progress is recorded at the top of `ARISTOTLE_SUMMARY.md`. (Note: a `sorry` at line 777 of `RequestProject/GlobalControl.lean` is inside a commented-out FALSE-statement block, not live code.)

# Summary of changes for current run (note-38 Phase-G support layer)

Followed `TASK.md` (note-38 master plan).  First fixed the project layout: the
`.lean` sources were at the repository root, but the lakefile expects them under
`RequestProject/` (module names `RequestProject.*`); I moved them back, so the
whole project builds green again (`lake build`, 8057 jobs).

**New proved lemmas (sorry-free, standard axioms).**
* `GlobalControl.gaussian_int_sum_le` — the standalone elementary Gaussian
  integer-sum bound `∑_{m∈ℤ} exp(-A·m²) ≤ 1 + 6/√A` for `0 < A ≤ 1` (note 38
  §7, step II), the analytic input for the G7 Gaussian-tail sector.
* `SBEEForcing.exists_X0_const_logbnd` — parametrized log-vs-linear threshold
  (`∀ K, eventually K·log X ≤ X`), generalizing `exists_X0_logbnd`.
* `SBEEForcing.cold_label_size` — **Lemma L3c** (cold-label size chain, note 38
  §3), the one remaining support lemma the task flagged: for a cold block
  (`R ≤ c₂·X/log³X`) with dominant label `m`, `|m| ≤ N·X/16` for `X ≥ X0(c₂)`.
  Proved by combining `theoremA_label_range`, `theoremA_label_le` and the cold
  range via the new threshold.  This feeds `fixed_label_count`,
  `cold_exception_bound`, and the `mismatch_penalty_with_exceptions` size
  hypotheses.  **With L3c the note-38 support layer is complete.**

**Remaining named sorries (the deep research core, unchanged in count).**
* `GlobalControl.global_levelset` (G5) — the segment-encoding Peierls decoder
  (note 38 §5).  A direct high-effort attempt timed out; this is a
  several-hundred-line covering/encoding assembly (the per-block √R/σ factors
  must be paid only per cold *segment*, via `segment_label_constant`, not per
  block, or the product bound blows up).  All of its inputs are now in scope and
  proved (L1–L5, L3c, G3-with-exceptions, S1–S3, D1–D4, SH, shell/subset
  entropy, segment constancy).
* `GlobalControl.global_control_partition` (G7) — depends on G5; its Gaussian
  tail input `gaussian_int_sum_le` is now available.
* `CircleMethod.exists_positive_weighted_construction` (Phase C) — depends on G7.

Build is green; the only `sorry`s are these three (line 777 of `GlobalControl`
is inside a commented-out FALSE-statement block, not live code).

# Summary of changes for run 55bcd808-5453-4add-8c1f-b9f75e7f72ab
Worked the note-37 ("Faithful G5/G7/C Formalization Blueprint") continuation of the Erdős 306 package. The whole project now builds green (`lake build`, 8057 jobs).

**Project-structure fix.** The `.lean` sources had been flattened to the repository root, but the lakefile (`globs = ["RequestProject.+"]`) and every `import RequestProject.*` expect them under `RequestProject/`. I moved all sources back into `RequestProject/`, so the project compiles again.

**New verified foundation — `RequestProject/GlobalPeierlsBookkeeping.lean` (sorry-free, standard axioms only).** Note 37 §3 explicitly asks to prove the *pure finite combinatorics* layer of the global level-set theorem (G5) before instantiating it with CRT/SBEE data. I created this file and proved:
- `weighted_subset_entropy` — entropy bound: costs `≤ exp(ε·w/4)` ⟹ total over subsets of weight `≤ R` is `≤ exp(εR/2)·exp(∑ exp(-ε·w/4))`. Used twice in G5.
- `subset_count_entropy` — the `cost ≡ 1` specialization.
- `prod_local_count_le` — energy-shell product: `∏ c i ≤ exp(εR)` when `c i ≤ exp(ε·R i)`, `∑ R i ≤ R`.
- `segment_label_constant` — labels are constant along any connected run of non-boundary edges (G5 step 4).

All four depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Honest status.** Three named sorries remain: `GlobalControl.global_levelset` (G5), `GlobalControl.global_control_partition` (G7), `CircleMethod.exists_positive_weighted_construction` (Phase C). The reusable combinatorial pieces for G5 are now in `GlobalPeierlsBookkeeping.lean`.

# Codex consolidation note (2026-06-12)

This bundle has been consolidated after the recovery run below.  The latest
active instruction is note `37 Faithful G5 G7 C Formalization Blueprint.md`.
Relative to the recovery output, `GlobalControl.lean` has one further statement
correction: G5 now uses the faithful paper factor
`exp(A * numBlocks BS)` under `admissibleGlobalRange BS`, and G7 is stated in
the final useful `eta + Gaussian tail` form.  This avoids both bad extremes:
choosing constants after `BS` (vacuous) and demanding one absolute `Cglob`
independent of the number of blocks (stronger than the paper statement).

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
