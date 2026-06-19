# Aristotle delivery — Erdős 306 package

> **CURRENT TASK = F1** (see "CURRENT TASK — F1" below): formalize the
> reciprocal-cluster selection lemma. The earlier cleanup tasks C1–C3 were
> COMPLETED (2026-06-09) and are already integrated into this snapshot (one
> intended open sorry `fourier_positivity_unconditional` + five honestly-`sorry`d
> SBEE lemmas); they are retained at the bottom for reference only.

**Upload this whole folder.** It is a self-contained Lean 4 package
(`leanprover/lean4:v4.28.0` + Mathlib, see `lean-toolchain` / `lakefile.toml`).
Build with `lake build`. The package currently builds with **one intended
`sorry`**: `fourier_positivity_unconditional` in
`RequestProject/FourierPositivity.lean`. Do **not** attempt to prove that one —
it is an open analytic theorem, out of scope here.

## Success criterion

After your changes the package must still build with **no new errors** and **no
new `sorry`/`admit`** beyond that single `fourier_positivity_unconditional`.
Preserve every public lemma/def name that other files import (add aliases if you
rename). Report the final `lake build` output.

## Background (what is real vs assumed)

`erdos_306` (the main theorem) reduces, with no hidden dependencies, to the one
`sorry`. A second file `SBEE.lean` states a *parallel, unfinished* route via an
**assumed** `ConditionSBEE` structure; several of its "theorems" currently just
return their own hypotheses (`:= hbound`), and `IrvingKloostermanBound'`
concludes `True`. A large block of files (`*CRT*`, `Anchored*`, `*Cluster*`,
`SplitStarCorrelation`, …) is real, sorry-free algebra/combinatorics but is
**disconnected** from the main theorem. The tasks below make the package honest
and de-duplicated without touching the open problem.

## CURRENT TASK — F1: formalize the reciprocal-cluster selection lemma

**Goal.** Prove, in Lean, that in the large-pool regime a **good seed tuple always
exists** — i.e. turn the trichotomy of `AnchoredSelectionPipeline.anchored_selection_pipeline`
into the single conclusion `hasAnchoredGoodKSubset`. This de-islands the
rational-collision component by giving it a concrete (non-assumed) conclusion.

Work in a NEW file `RequestProject/ClusterSelectionClosure.lean` importing
`AnchoredSelectionPipeline`. Build must stay green (`lake build`), no new
`admit`/unsound axioms; isolate any genuinely missing arithmetic as a clearly
named `sorry` (but try to avoid sorries — the pieces below are elementary).

**Recall the formalized ingredients (already in the package):**
- `anchoredCluster Short F p q0 x0 = F.filter (fun q => ∃ x y, Short x ∧ Short y ∧ q*x - q0*x0 = p*y)`
- `anchoredClusterFamily Short F P X0 q0 = (P ×ˢ X0).image (fun px => anchoredCluster Short F px.1 q0 px.2)`
- `anchored_good_or_allCovered`: `hasAnchoredGoodKSubset … ∨ allKSubsetsCovered …`
- `anchored_incidence_le_clusters_mul_choose`: if every cluster meets `F` in ≤ `L`
  points then `incidence ≤ family.card * Nat.choose L m`
- `incidence_lower_of_all_high_codegree` (use with `R = 1`)

**Steps:**
1. **Covered ⇒ codegree ≥ 1**: `coveredBySomeCluster Clusters S → 1 ≤ clusterCodegree Clusters S`.
2. **All-covered ⇒ incidence ≥ C(|F|,k)**: combine step 1 with
   `incidence_lower_of_all_high_codegree` (R=1) and
   `(F.powerset.filter (·.card = k)).card = Nat.choose F.card k`.
3. **Cluster-size bound** `(F ∩ anchoredCluster Short F p q0 x0).card ≤ L`: prove with
   explicit hypotheses encoding the central regime — e.g. `p.Prime`,
   `∀ q ∈ F, X ≤ q ∧ q ≤ 2*X`, `X ≤ p`, `Short x ↔ (0 < |x| ∧ |x| ≤ Mτ)`, and
   coprimality `IsCoprime (q0*x0) p` as needed. Key arithmetic: for each short `x`,
   `q*x ≡ q0*x0 (mod p)` pins `q` to one residue class mod `p`, and `[X,2X]` meets
   it in ≤ 1 integer when `X ≤ p`; summing over `≪ Mτ` short `x` gives
   `L ≪ Mτ` (a concrete `L`, e.g. `L = 2*Mτ` up to constants — choose what the
   proof gives).
4. **Family-count bound** `(anchoredClusterFamily …).card ≤ P.card * X0.card`
   (`Finset.card_image_le`, `Finset.card_product`).
5. **Arithmetic contradiction / main lemma**: assume `allKSubsetsCovered`; then
   `Nat.choose F.card k ≤ incidence ≤ (P.card*X0.card) * Nat.choose L k`. State a
   hypothesis capturing the regime (e.g. `(P.card*X0.card) * Nat.choose L k < Nat.choose F.card k`)
   and derive `False`, hence `hasAnchoredGoodKSubset` via `anchored_good_or_allCovered`.
   Provide a corollary instantiating the regime hypothesis from the numeric scale
   `F.card ≥ X^(1/2+δ)`, `L ≤ Mτ ≤ X^(1/2)`, `P.card ≤ X`, `X0.card ≤ Mτ`, `k = 4`
   (so `P.card*X0.card*C(L,4) ≪ X*Mτ^5 = X^(7/2)` while `C(F.card,4) ≫ X^(7/2)` once
   `F.card ≫ X^(7/8)`). Keep the corollary's arithmetic side-condition explicit.

**Deliverable:** a theorem `good_kSubset_exists_of_size` concluding
`hasAnchoredGoodKSubset Short F P X0 q0 k` from the size/count/arithmetic
hypotheses, plus the cluster-size lemma (step 3) proved. Report `lake build`.

---

## EARLIER TASKS (C1–C3) — COMPLETED 2026-06-09, retained for reference

### C1 — De-vacuize `SBEE.lean`
- The four theorems `cross_block_label_mismatch`, `peierls_collapse`,
  `ordinary_diagonal_counting`, `global_control_partition` are proved `:= hbound`/
  `:= hlb` (they return their own hypothesis). Either **delete** them (grep
  confirms nothing imports them) or **restate** them with their genuine
  conclusions proved by `sorry` (clearly marked). Do not leave hypothesis-returns.
- Restate `IrvingKloostermanBound'.bound` with its real conclusion instead of
  `True`: a nontrivial bound on `S_q(a;x) = ∑_{p∼x,(p,q)=1} e(a·p⁻¹/q)`, e.g.
  `|S_q(a;x)| ≤ C·(x^(15/16) + q^(1/4)·x^(2/3))·q^ε` for `x^(3/4) ≤ q ≤ x^(4/3)`
  (Irving, *Average Bounds for Kloosterman Sums Over Primes*, Acta Arith. 150
  (2011)). Keep it as an external **axiom/structure** — do **not** prove it.
- `irving_good_pruning` is currently vacuous (`P_star := P.primes` gives `2|P|≥|P|`).
  Restate honestly (its real content is phase dispersion) with `sorry`, or remove
  if unused downstream.

### C2 — Factor duplicated CRT-lattice machinery
`ValidCRTLattice`, `AnchoredCRTLattice`, `ReciprocalCRTProduct` repeat the same
constructions (`base_diff`, `local_residue`, `_smul`, `dvd_of_*Hit`,
`xi_eq_div`). Extract a shared generic core file and have the three instantiate
it, **preserving all exported names** so dependents
(`ResidualPrimeShellCRT`, `SplitStarCorrelation`, `AnchoredDeterminantRank`,
`AnchoredSelectionPipeline`) compile unchanged.

### C3 — Honestly label the disconnected component
Add a module-level comment to each of the rational-collision files
(`*CRT*`, `Anchored*`, `*Cluster*`, `SplitStarCorrelation`,
`PrimitiveProjectiveNormalization`, `ResidualPrimeShellCRT`) stating they are
**route-exploration not on the critical path of `erdos_306`**, and that the top
result `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound` *assumes*
the shell bound as a hypothesis.

(Do C1 and C3 first — they are small and high-value. C2 is a larger refactor.)
