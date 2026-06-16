# Cleanup Tasks for Aristotle

Back to [[00 README]]. Companion to [[20 Lean Core Audit and Dependency Map]].

> ✅ **STATUS: ALL DONE (2026-06-09).** Aristotle completed C1, C2, C3 and verified
> `lake build`. The cleaned package is now integrated as `core-packet/lean/`
> (raw output archived at `archive/Aristotle/output-cleanup_2026-06-09/`). Result:
> SBEE de-vacuized (4 launderers → honest `sorry`d statements; `IrvingKloostermanBound'`
> now states the real bound; `irving_good_pruning` honestly `sorry`d with phase
> dispersion); `CRTLatticeCore.lean` factored out the shared CRT machinery (Valid/
> Anchored/Reciprocal now import it, public API preserved); all 11 collision-infra
> files + core labelled "route-exploration, off critical path." Build: only
> `fourier_positivity_unconditional` + 5 honest SBEE sorries; no admit/unsound axioms.

The **safe, comment-only / orphan-deletion** cleanup is already applied locally
(see §0). The remaining items change Lean semantics and therefore **must be
rebuilt** (`lake build`) — out of scope for the local shell, in scope for
Aristotle. Each task below is a self-contained prompt: the package builds against
`leanprover/lean4:v4.28.0` + Mathlib, and the success criterion is **no new
errors and no new `sorry`/`admit`** beyond the single intended
`fourier_positivity_unconditional`.

## 0. Already applied locally (no rebuild needed — comments + deletion)

* Corrected the false "SBEE is proved" header in `Erdos306Unconditional.lean` to
  the honest status (erdos_306 ⟸ the one sorry, SBEE not discharged).
* Added an honesty banner + per-declaration `⚠️` markers in `SBEE.lean` on the
  four laundered theorems, the `IrvingKloostermanBound'` stub, and the trivial
  `irving_good_pruning`.
* Deleted the orphaned duplicate `SemiprimeReciprocals.lean` and updated
  `lean/README.md`.

## Task C1 — De-vacuize `SBEE.lean` (rebuild)

In `RequestProject/SBEE.lean`:

1. Replace the four hypothesis-laundering theorems
   (`cross_block_label_mismatch`, `peierls_collapse`, `ordinary_diagonal_counting`,
   `global_control_partition`) — each currently `:= hbound`/`:= hlb` — by **honest
   statements of their real conclusions proved with `sorry`** (so they become
   genuine, non-vacuous targets), OR delete them entirely (they are imported by
   nothing; only `single_block_counting`/`fourier_positivity` and the assumed
   `ConditionSBEE` are downstream). Confirm by grep that removal breaks no import.
2. Restate `IrvingKloostermanBound'.bound` with its **real** conclusion instead of
   `True`: a bound on `S_q(a;x)=∑_{p∼x,(p,q)=1} e(a·p⁻¹/q)`, e.g.
   `|S_q(a;x)| ≤ C·(x^{15/16}+q^{1/4}x^{2/3})·q^ε` in `x^{3/4}≤q≤x^{4/3}`
   (Irving, Acta Arith. 150 (2011); cf. [[11 Irving Toolbox and the Finish Roadmap]]).
   Keep it as an external cited `axiom`/`structure` (do not prove it).
3. Re-`sorry` or honestly restate `irving_good_pruning` (its current proof
   `P_star := P.primes` is vacuous).

**Goal:** `SBEE.lean` should contain only genuine proofs, honest `sorry`d targets,
and clearly-marked external axioms — no theorems that return their own hypotheses.

## Task C2 — Factor duplicated CRT-lattice machinery (rebuild)

`ValidCRTLattice`, `AnchoredCRTLattice`, `ReciprocalCRTProduct` repeat the same
pattern (`base_diff`, `local_residue`, `_smul`, `dvd_of_*Hit`, `xi_eq_div`).
Extract a single generic `CRTLatticeCore.lean` parametrized over the seed data,
and have the three files instantiate it. Preserve all currently-exported lemma
names (add `export`/aliases if needed) so dependents (`ResidualPrimeShellCRT`,
`SplitStarCorrelation`, `AnchoredDeterminantRank`, `AnchoredSelectionPipeline`)
still compile unchanged.

**Goal:** remove ~hundreds of duplicated lines with zero change to the public API.

## Task C3 — Connect Component C, or mark it off-path (rebuild)

Per [[20 Lean Core Audit and Dependency Map]], the rational-collision files
(Component C) are real but disconnected: their top result
`ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound` **assumes** the
shell bound (`:= hbound …`), and nothing links C to `ConditionSBEE` (B) or
`erdos_306` (A).

Choose one:

* **(C3a, wiring)** Formalize the markdown chain "residual-prime shell bound ⟹
  `ConditionSBEE.partition_bound`" as a Lean theorem (with the genuinely-open
  analytic steps isolated as named `sorry`s), so Component C stops being an
  island and the conditional theorem `erdos_306_conditional` gains a stated
  (if still `sorry`-gated) route from the collision infrastructure.
* **(C3b, honest labeling)** If the wiring is premature, add a module-level note
  to each Component-C file stating it is *route-exploration not on the critical
  path of `erdos_306`*, and that its top bound is assumed.

**Goal:** no false impression that Component C contributes to a `sorry`-free
`erdos_306`.

## Priority

C1 (honesty, small) > C3b (labeling, small) > C2 (refactor, medium) >
C3a (wiring, large — overlaps with real mathematics, do only when the
shell-bound ⟹ SBEE argument is settled on paper). None of these touch the single
genuine open problem, `fourier_positivity_unconditional`.
