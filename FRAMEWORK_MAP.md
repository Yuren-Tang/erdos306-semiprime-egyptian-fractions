# Erdős 306 — Framework Map (mathematical reverse-engineering)

> Generated 2026-06-17 on branch `clear-up` by static analysis (no build).
> Reliable inputs: parsed `imports` edges + read proof bodies + grep for genuine `sorry`.
> **Unreliable, do not trust:** the `status` field and `decl_ref` edges in the dependency JSON
> (false edges from identifier name-matching; `placeholder` keys on the word "sorry" in doc-comments).

---

## 0. The one-line shape

```
erdos_306 (a/b, squarefree b, all a)
  └─[induction on a, denominator-avoiding]  reduction_to_unit_numerator_avoiding
       └─ fourier_positivity_unconditional T b           (the 1/b case, avoiding any obstruction set T)
            └─ CircleMethod.circle_method_positivity T b  ← THE ENGINE
                 ├─ b=1, b=2 : explicit finite constructions
                 └─ b≥3 : exists_pos_weighted_of_construction      [ANALYTIC CORE]
                      │      ArcConstruction T b  ⟹  0 < Wcount E θ b
                      ├─ MAIN ARC ≥  +  MINOR ARC ≤   (boards A+B+C, COMPLETE via *_final)
                      └─ Nonempty (ArcConstruction T b) = exists_arcConstruction   ← ★ THE ONLY LIVE GAP ★
                                                            (board D = R2 island; incomplete + unwired)
```

Everything reduces to one analytic engine `circle_method_positivity`. It needs two things, supplied by two
disjoint mechanisms:

1. **An `ArcConstruction`** — an explicit edge set `E` (squarefree semiprimes avoiding `T`), weights `θ∈[1/3,2/3]`
   with `∑ θ_e/e = 1/b`, a main/minor frequency split `range L = SM ⊔ Sm`, and a *consumed* minor-arc bound
   `‖∑_{h∈Sm} fourierTerm‖ ≤ Bm < 0.8·e^{-π²/2}/2 / √σ_E²` (`hminor`/`hbeat`).
2. **The analytic core** `exists_pos_weighted_of_construction` that turns such a structure into `Wcount > 0`
   (positivity ⟹ an actual Egyptian semiprime representation).

The minor-arc bound is where the deep number theory lives. It is established **twice over** in the repo, and
this is the central structural tangle (see §6).

---

## 1. Boards (module clusters)

| Board | Files | Role | Status |
|---|---|---|---|
| **A — Circle method** | 11 (`CircleMethod*`, `Bernoulli/FourierPositivity`, `ArcConstruction`) | Fourier/circle-method analytic core: main term ≥, minor arc ≤, positivity ⟹ representation | **closed** (live path) |
| **B — SBEE** | 11 (`SBEE*`, `BlockCRTEnergy`, `SingleBlockCounting`, `Block*`, `CrossLabelEnergy`, `FiberCount`) | Single-block energy/entropy + Irving–Kloosterman dispersion ⟹ per-block partition bound | **closed** via `SBEEAssembly` (`*_final`) |
| **C — Global control** | 8 (`GlobalControl*`, `GlobalPeierls*`, `DyadicBlockDef`) | Global level-set / Peierls floor / Gaussian sector ⟹ off-main-arc Laplace sum bound | **closed** via `global_control_partition_final` |
| **D — R2 construction** | 62 (`R2*`) | The explicit block-aligned construction discharging `exists_arcConstruction` for `b≥3` | **OPEN island** (not imported by top; incomplete) |
| **E — Kloosterman/CRT** | 13 (`Anchored*`, `Cluster*`, `*CRT*`, `Split*`, `Reciprocal*`, `Residual*`) | CRT lattice / anchored-determinant / cluster-selection machinery feeding D (and historically B) | **island** (only reached via D) |
| **Z — Top** | 4 (`Erdos306Unconditional`, `MainTheorem`, `Defs`, `SemiprimeInfinity`) | Statement, a/b→1/b induction, conditional vs unconditional | live |

**Reliable import facts.** `Erdos306Unconditional` transitively imports exactly boards **A+B+C (25 files)**.
Board **D (R2) imports all of A+B+C** and adds the construction — so R2 is a *layer on top*, not a duplicate of
B/C. But nothing in A+B+C imports D, so the construction is currently dangling.

---

## 2. Board A — the circle-method engine (`CircleMethod*`)

- `circle_method_positivity` → `egyptian_rep_ge2` → `egyptian_rep_ge3` → `exists_pos_weighted_ge3`.
- `exists_pos_weighted_ge3` = `exists_arcConstruction` (the ★ gap) **+** `exists_pos_weighted_of_construction`.
- `exists_pos_weighted_of_construction` is the **self-contained analytic core**: its only cross-board references
  are to `CircleMethodMainTerm` (Fourier main term). It consumes the minor bound as a *hypothesis*; it does **not**
  itself invoke SBEE/GlobalControl.
- Main-arc positivity: `CircleMethodMainArc` (Bernoulli/Taylor log expansion) → `CircleMethodMainTerm`
  (`main_sum_re_lower`, `main_sum_im_zero`: the main term is real and bounded below).
- Minor-arc bound: `CircleMethodArcs.minor_arc_bound` / `minor_arc_norm_le`, which **calls the COMPLETE
  `global_control_partition_final`** (board C) — this is the live wiring of A↔C.

## 3. Board C — global control (`GlobalControl*`)

The off-main-arc sum `∑_{a ∉ mainArc} e^{-c·Qctrl(a)} ≤ (η + Ctail·e^{-C²c/2})/σ_ctrl`, proved as
`GlobalControlG7.global_control_partition_final` by splitting into:
- **G5 level-set** `global_levelset_final` (`GlobalControlG5Assembly/Data`): cold/wrapped count bounds, Peierls floor charge.
- **G6 localization** `g6_localization`: off-main-arc ⟹ either above the control floor or in the diagonal sector.
- **Sector I** `sectorI_absorption'` (`GlobalControlSectorI`): η-absorption above the floor (superlinear floor growth).
- **Sector II** `sectorII_gaussian` (`GlobalControlG7`): the one-dimensional Gaussian tail.

`Qctrl`/`sigmaCtrl` are sums over `ctrlPairs BS` = internal (same-block) ∪ bipartite (**adjacent** blocks) — this
adjacency restriction is the source of the R2 `3σ²` subtlety (§6, board D).

## 4. Board B — SBEE single-block engine (`SBEE*`, `BlockCRTEnergy`)

Per prime block `P`, the partition function `blockPartFun P c ≤ C/σ_P` (a Gaussian-type saving), assembled as
`SBEEAssembly.single_block_counting` (proves `SBEEPartitionBound`) via a trichotomy on the energy level `R`:
- **Theorem A** `theorem_A_dominant_count` (`SBEEForcing`): dominant-label count.
- **Theorem B** `theorem_B_nondominant_forcing` (`SBEEForcing`): low energy ⟹ dominant (covering dichotomy).
- **Theorem C** fingerprint threshold `fingerprint_count` (`SBEEFingerprint`), entropy/decoding bounds.
- Dispersion input: `SBEEDispersion` (`lemmaD`, `dispersion_residue_count`) — incomplete-Kloosterman residue counts
  (Irving's bound `IrvingKloostermanBound'` is the sole cited external input).

## 5. Boards D+E — the R2 construction (the island)

`R2TopAssembly.exists_arcConstruction_final` is meant to *be* `exists_arcConstruction` for `b≥3`: build a concrete
`R2ConcreteData` (edge set = control edges ⊕ mass-batch `Q` ⊕ gadget edges), choose weights, and feed the
numeric-window endpoint `R2FinalAssembly.exists_arcConstruction_of_componentData_numeric_minor_window`. It reuses
boards A+B+C for the analytic facts and boards E for the CRT/cluster construction of `Q`. **It is not finished**
(see §6). 62+13 files, ~340 declarations — over half the project, none of it reaching the top theorem.

---

## 6. Findings — what to clean up

### 6.1 The dead sorry-stubs — DELETED 2026-06-17 ✓
**Done.** 12 superseded legacy stubs removed (grep-verified zero code references; only doc-comments mentioned them).
`mismatch_per_q` turned out to be COMPLETE (its "sorry" at GlobalControl:778 is inside a `/- … -/` comment), so it
was kept. Removed:
- whole file `SingleBlockCounting.lean` (imported by nothing; only `sbee_nondominant` stub + `trivial_bound`).
- `BlockCRTEnergy.{SBEEUniformSaving, dominant_case_uniform, tiny_case_uniform, sbee_nondominant_uniform,
  single_block_counting_uniform}` (the whole "Faithful UNIFORM saving" section).
- `SBEE.{irving_good_pruning, cross_block_label_mismatch, peierls_collapse, ordinary_diagonal_counting,
  global_control_partition}` (the dead Lemma-5.1–8.1 intermediate chain).
- `GlobalControl.{global_levelset, global_control_partition}` (tail stubs; `mainArc` def kept — live, used by G7).

**Result: the entire project now contains exactly ONE genuine code `sorry` —
`CircleMethodAssembly.exists_arcConstruction` (§6.2).** (Modulo a build to confirm the edited files still parse;
all deletions were reference-safe.) Still-dead-but-harmless leftovers for a later sweep: the primed-label helper
defs in `BlockCRTEnergy` (`BlockLabeling'`, `activeLabels'`, `labelClass'`, `isDominantLabel'`,
`substantialCoverage'`, `isSubstantialClass'` — zero external refs), `SBEE.IrvingKloostermanBound'` +
`fourier_positivity` + `single_block_counting` (complete but off the live path), the commented FALSE
`mismatch_penalty` block (GlobalControl:766–790), and `GlobalControl.mismatch_per_q` (complete but unused).

### 6.2 The ONE real gap: `exists_arcConstruction` (board D)
`R2TopAssembly.exists_arcConstruction_final` has three concrete blockers:
- **(a) closing application** — the body builds all `have`s (≈R2TopAssembly:632–782) then `end`s without ever
  applying the endpoint; the closing `exact … + hN2/hNL` large-`k0` arithmetic is missing (this is the "does not
  compile, but no sorry" state).
- **(b) elaboration debt** — deep `let`/`set` nesting of `D`(=…`Classical.choose Q`)/`W`/`σ`/`N`/`C` causes
  `isDefEq` blow-up → `maxRecDepth`/kernel stack overflow. Fix: abstract the construction body to take **opaque**
  `D W N` parameters. (This is itself a cleanup.)
- **(c) the tight analytic residual** — the endpoint requires
  `hextraLight : ∑_{e∈E∖ctrlEdges} 1/e² ≤ 3·σ_ctrl²`, but the only producer `r2_extra_inv_sq_le` gives loose
  `≤ 1000001·σ²`. **Math problem, isolated for hand-off** (§7).

### 6.3 Coarse-estimate pattern
`r2_extra_inv_sq_le` is the archetype: it bounds `∑_Q 1/e² ≤ (∑_{p∈blockSupport} 1/p²)²` (discarding adjacency
structure) then compares **absolute** magnitudes via two loose constants (`8/(k0·2^{k0})` and the very loose
`σ ≥ 1/(100·k0·2^{k0})`), giving a 640000× slack. The clean replacement is a **relative** sub-sum bound where the
prime-density factor cancels (§7).

### 6.4 Duplicate structures (board D fragmentation — lower priority)
6× `R2Minor*Lanes`, 4× `R2ExtraMinor*Data`, 6× `R2*Supply`, `MainArcFields`/`MainArcNumericFields`,
`R2ExtraFrequencyLabelData`/`…IntFrequencyLabelData` (real/ℤ clones), `BlockLabeling`/`BlockLabeling'`. Candidates
for parameterized consolidation once the bridge is closed.

---

## 7. Isolated math problem (for hand-off)

**Claim (closes blocker 6.2c).** With `blockSupport = ⋃_{k∈[k₀,K]} P_k` (dyadic blocks, `p ∈ P_k ⟹ 2^k ≤ p < 2^{k+1}`),
and `σ² = ∑_{(p,q)∈ctrlPairs} 1/(pq)²` over `ctrlPairs` = {same-block pairs} ∪ {adjacent-block pairs `P_k×P_{k+1}`},
define `NonAdj = ∑_{p<q, |block(p)−block(q)| ≥ 2} 1/(p²q²)`. Then
$$\textstyle \mathrm{NonAdj} \le 2\,\sigma^2.$$
Consequently `∑_{e∈Q} 1/e² ≤ ∑_{p<q ∈ blockSupport} 1/(pq)² = σ² + NonAdj ≤ 3σ²` (the mass-batch `Q` edges are
products of blockSupport prime pairs, `QB.hQpair`).

**Why it should be elementary.** Both sides carry the same prime-density factor (`∑_{p∈P_k} 1/p² ≍ 1/(k·2^k)`),
so it cancels: this is a pure geometric-block-distance decay comparison, **not** an absolute prime-counting lower
bound (which is what the previous attempt got stuck on). Open sub-questions to pin during the proof: whether `Q`'s
image hits all blockSupport pairs or a subset (subset ⇒ easier); whether the diagonal `p=q` occurs (`IsSemiprime`
⇒ distinct primes ⇒ no `∑1/p⁴` term); the exact decay ratio needed to land the constant `2`.
Reusable: `dyadic_block_card_upper`, `ctrlPairs`/`bipartitePairs` (`GlobalControl.lean:128–135`).
