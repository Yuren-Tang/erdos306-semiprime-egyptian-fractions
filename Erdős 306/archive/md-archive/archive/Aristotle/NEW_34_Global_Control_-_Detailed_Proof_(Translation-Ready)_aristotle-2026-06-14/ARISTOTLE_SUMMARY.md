# Summary of changes for run 21281329-6f30-4210-a109-dc87221a458f
Completed the active task (`ACTIVE_PROMPT.md` / note 43): proved the **G6 localization dichotomy** in a new leaf file `RequestProject/GlobalControlG6.lean` that only `import`s `RequestProject.GlobalControl`. I did not edit `GlobalControl.lean`, `GlobalControlG7.lean`, `GlobalControlG5Assembly.lean`, or `CircleMethod.lean`.

Startup fix: the uploaded `.lean` sources were flattened to the repository root, but the lakefile expects them under `RequestProject/`; I moved all 35 sources back there so the project compiles. (`.lake` had no prebuilt RequestProject oleans, so the verified core was rebuilt from the Mathlib cache.)

The target theorem `GlobalControl.g6_localization` is proved with the exact required signature, and the `globalControlFloor` / `diagSector` definitions are byte-identical to those in `GlobalControlG7.lean`. The whole project builds green and the result is axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`); the file contains no `sorry`.

Decomposition (following note 43, all proved):
- L1 `Rw_mono` (with the supplied verified `Rw_mono_step`) — monotonicity of the forcing floor `Rw`.
- L2 `Pifloor_ge_Rw` / `Rw_le_Pifloor` — the forcing floor at `k0` is below the boundary-penalty floor at later blocks, via the new `exists_pow_ge_affine` (exponential beats affine) and the block density bounds.
- L5 core `crtRepr_eq_label_of_small` and `diagonal_Qctrl` — the centered-CRT identity and the exact quadratic energy identity `Qctrl a = m²·σ²`; plus the control-pair size facts `ctrlPairs_ne` and `ctrlPairs_prod_lower`.
- Energy bookkeeping `blockEnergy_le_Qctrl`, `Xen_le_Qctrl`, and `segStart_empty`.
- L3 — the substantive `cold_no_exceptions` step was **fully closed** (not left as a sorry). The note flagged this as the one genuinely-hard new lemma and permitted isolating it; instead I proved it. The key was that Theorem-B's constant `c2 = min(ρ²√(cEρ)/10⁶, ρ²/4718592)` with `ρ=1/4` is ≈ 1.3·10⁻⁸, comfortably below the `1/2²¹` threshold needed. I introduced `cold_no_exceptions_core` (with an explicitly small `c2 ≤ 1/2²¹`) that applies `SBEEForcing.exception_count_bound`: an exceptional prime in a cold block would force block energy that contradicts `¬ isHot`, so the exception count is `< 1`, hence `0`. The bundle `cold_no_exceptions` then takes `c2 := min(c2_boundary, 1/2²¹)` and re-derives the cold-block facts and boundary penalty from `boundary_penalty_per_k` by monotonicity in `c2` (`Rw_le_of_c2_le`, `not_isHot_mono`).
- The assembly `g6_localization` performs the hot / boundary / no-structure trichotomy: Case H and Case B land in the energy-floor disjunct; Case D (no hot, no boundary) collapses to a globally diagonal label `m = coldLabel k0` with large label (off main arc) and exact energy.

Honest status of the broader program (outside this task's scope, unchanged): the other headline results remain `sorry` in their own files as before — `GlobalControl.global_control_partition`, the separately-driven `GlobalControlG7.g6_localization`, and the Phase-C circle-method theorem.

# Summary of changes for run e69b533e-b227-43d8-b123-952f9690ba31
Continued the Erdős-306 (note-40) Phase-G program in `RequestProject/GlobalControl.lean`, picking up from the prebuilt state. The whole project builds green (`lake build`, 8057 jobs) and every new result is axiom-clean (only `propext`, `Classical.choice`, `Quot.sound`).

**Closed the hole-8 glue (previously open).**
- `hot_factor` — the per-hot-block level-set count `≤ exp(2ε(n+1))`, absorbing the `unified_levelset` polynomial factor into the energy floor. Supported by two new reusable helpers I added and proved: `log_le_eps_mul` (monotone `log t ≤ ε·t` for `t ≥ 1/ε`) and `Rw_large` (`Rw c2 k → ∞`).

**Completed the note-40 §2 energy-budget layer (all proved):**
`sum_blockEnergy_le`, `sum_shellVec_le`, `shellVec_le_floorR`, `sum_Rw_hot_le`, `sum_bipartite_le` — the per-block internal energies, shell vectors, hot floors and bipartite cross-energies each sum to `≤ R`.

**Built the exception-set machinery and the cold/boundary layer (note-40 §3d, all proved):**
- `excSet` (deviating primes of a cold block) with `excSet_subset`, `restrict_eq_toPlain`, `excSet_card_eq`, `conform_card_eq` (bridges to the `attach`/`classCount` forms used by the single-block package).
- `cold_exceptions_small` (§3d-ii) — cold blocks have a small exception set.
- `cold_label_size64` — a factor-4 sharper cold-label bound `|m| ≤ N·X/64` (needed by the boundary penalty).
- `cold_block_facts` — bundles, for every cold block, the small-exception bound, the sharp label bound, and the conform property, producing the global cold constants `c2,e0`.
- `boundary_penalty_per_k` (§3d-iii/3d-iv master lemma) — the "heart": every mismatch-boundary block contributes bipartite control energy `≥ Pifloor`, assembled from `mismatch_penalty_with_exceptions`, `cold_block_facts`, and density thresholds.

**Honest remaining status.** The three headline chain results remain precisely-named `sorry`s, stated faithfully (uniform constants): `global_levelset` (G5), `global_control_partition` (G7), and `CircleMethod.exists_positive_weighted_construction` (Phase C). The note-40 §2 and §3d support layers underneath G5 are now essentially complete; what remains for G5 is the §3 data Finsets, the four-level covering argument (6a/6b/6d), the label-product numerics (10a–c), and the final assembly (hole 12), then G7 and Phase C.

No user-provided content was deleted; the previously-documented FALSE original `mismatch_penalty` statement remains commented out with its finding. `ARISTOTLE_SUMMARY.md` was left unedited as requested.

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
