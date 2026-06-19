# Aristotle delivery — Erdős 306 package

> **CURRENT TASK = F2a'''** (see below): the saving predicate `SBEESavingBound`
> was found **vacuous** (constant `C` quantified per-block ⇒ any single block
> satisfies it). Fix it to a **uniform** (block-independent) `C`, then restate the
> dominant/tiny/non-dominant cases against the faithful predicate (as honest
> sorries — they now need the real dispersion content). The `QP`/`sigmaP`/`blockPartFun`
> *definitions* are faithful; only the bound's quantifier was wrong. Done &
> integrated: C1–C3, F1, F1b, F2a', F2a'' (the latter's case proofs were vacuous —
> see note 27 §4c). Builds. See core-packet notes 26, 27.

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

## CURRENT TASK — F2a': FAITHFUL single-block encoding (replaces the trivialized F2a)

⚠️ The prior F2a (`SingleBlockCounting.lean`) took shortcuts: it proved the
dominant/tiny cases with the **trivial** bound `partitionFun ≤ N` (each term ≤ 1)
instead of the real *saving* bound, and `single_block_counting_assembled`
**launders** (assumes `N ≤ C/√variance`, which is false since `N = ∏ p`). These
are vacuous against real SBEE because the abstract `BlockEnergyData.energy` carries
no CRT structure. F2a' fixes the **encoding** so trivial proofs cannot pass.

Create `RequestProject/BlockCRTEnergy.lean` (and revise `SingleBlockCounting.lean`):

1. **Faithful objects** (match CP 02 §1):
   - block `P : Finset ℕ` (primes); assignment `a : ∀ p, ZMod p` (or `Π p ∈ P, ZMod p`).
   - CRT representative `H p q a : ℤ` with `H ≡ a p (mod p)`, `H ≡ a q (mod q)`,
     `|H| ≤ p*q/2`; energy `QP P a = ∑_{p<q ∈ P} ((H p q a : ℝ)/(p*q))^2`;
     `sigmaP P = Real.sqrt (∑_{p<q} 1/((p:ℝ)*q)^2)`.
2. **Real target bound** (the SAVING — this is the point):
   `∑_{a} Real.exp (-c * QP P a) ≤ C / sigmaP P`  (or the level-set form
   `#{a : QP P a ≤ R} ≤ Cε * exp(ε*R) * (1 + Real.sqrt R / sigmaP P)`).
   With assignment space of size `∏ p`, the trivial `≤ #assignments` is **useless**,
   so any proof must exhibit a genuine saving.
3. **Dominant case** — prove the remainder saving via Irving majority correction
   (exception entropy `O(log X)` paid by energy), NOT `≤ ρN`.
4. **Tiny case** — prove that an almost-all-tiny profile forces the short list, hence
   `R`, large enough to pay the crude entropy. (May legitimately need the
   base-list lower bound on `R`.)
5. **`sbee_nondominant`** — restate against `QP`, `sigmaP` so the cluster machinery
   (`good_kSubset_exists_unconditional`) and `cross_label_divisor_energy` actually
   connect. Keep as `sorry` (this is F2b's faithful target).
6. **Replace** the laundering `single_block_counting_assembled`: assemble the three
   real case bounds into the real partition bound; if a case is not yet provable,
   leave a clearly-named `sorry` (do NOT assume the conclusion as a hypothesis).

**Deliverable:** faithful `QP`/`sigmaP`/assignment-space encoding; dominant + tiny
proved against the SAVING bound (or honest named sorries if a genuine sub-lemma is
missing — but no trivial `≤ N` substitutes and no laundering); faithful
`sbee_nondominant`. Report `lake build` and the exact remaining sorries.

## CURRENT TASK — F2a''': fix the saving predicate to UNIFORM C (it was vacuous)

The F2a'' round (correctly!) found that `SBEESavingBound P hP c := ∃ C, 0<C ∧
blockPartFun P hP c ≤ C/sigmaP P` is **vacuous**: `C` is existentially quantified
*per block*, so any single finite block satisfies it (`C = blockPartFun·sigmaP+1`).
The dominant/tiny "proofs" are sound but vacuous. **Fix the predicate so `C` is
uniform (block-independent)**, then restate the three cases against it.

In `BlockCRTEnergy.lean`:

1. **New faithful predicate** (the constant outside the ∀-block):
   ```
   def SBEEUniformSaving (c : ℝ) : Prop :=
     ∃ C : ℝ, 0 < C ∧
       ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p), 2 ≤ P.card →
         blockPartFun P hP c ≤ C / sigmaP P
   ```
   (Computation check: for `P={p,q}`, `∑_a exp(-c(H/pq)²) ≈ pq·√(π/c) = √(π/c)/sigmaP`,
   so the true uniform constant is `C ≈ √(π/c)`, depending only on `c`. For a fixed
   `C`, "for all blocks `P`" is a genuine constraint — NOT vacuous.) Keep the old
   per-block `SBEESavingBound` only if you also mark it clearly as "vacuous, do not
   use as the SBEE target".

2. **Restate the three cases against `SBEEUniformSaving`** (or against the
   per-block bound but with `C` supplied from outside): `dominant_case_uniform`,
   `tiny_case_uniform`, `sbee_nondominant_uniform`. These are now the **real**
   theorems — proving them needs the genuine dispersion/energy content. Leave each
   as a **clearly-named sorry** unless a real proof is available (the 2-prime base
   constant is provable; the uniform bound over all blocks is the deep content).
   **Do NOT** discharge them via the per-block `∃C` trick.

3. **Remove or quarantine** the now-vacuous `dominant_case_saving`,
   `tiny_case_saving`, `single_block_counting_faithful` (or restate against the
   uniform predicate). No vacuous "proofs" should remain presented as the SBEE
   content.

4. **Assembly**: `single_block_counting_uniform : SBEEUniformSaving c` from the
   three uniform cases (with honest sorries), without assuming the conclusion.

Deliverable: faithful `SBEEUniformSaving`; the three cases restated against it as
honest sorries (or genuine proofs); the vacuous versions removed/quarantined.
Report `lake build` and the exact remaining sorries.

## (superseded) F2a'' — dominant + tiny against per-block bound [vacuous, see note 27 §4c]

The faithful encoding (`BlockCRTEnergy.lean`: `QP`, `sigmaP`, `blockPartFun`,
`SBEESavingBound`) is in place; `dominant_case_saving` and `tiny_case_saving` are
honest sorries. Prove them (the standard cases), using `IrvingKloostermanBound'`
(now stating the real bound) where needed. Leave `sbee_nondominant'` as the sole
decisive sorry.

* **Dominant case** (`dominant_case_saving`): one label `m` covers ≥ (1−ρ)·#assignments.
  Show `blockPartFun ≤ C/sigmaP`. Argument (CP 03 §§4–5): the class-`m` partition
  function is a Gaussian-type sum `≤ C/sigmaP` (the dominant Gaussian peak); the
  ≤ρ-fraction of exceptions each carry CRT energy `QP ≫ |P|` (Irving-good
  dispersion, from `IrvingKloostermanBound'`), so their `exp(−c·QP)` contribution
  is exponentially small and their `O(log)` choice/residue entropy is paid by that
  energy. If a genuine sub-lemma is missing (e.g. the Gaussian peak bound), leave a
  precisely-named sorry — but no trivial `≤ #assignments` substitute.
* **Tiny case** (`tiny_case_saving`): all label classes ≤ T (small). Then the short
  list is large, forcing the relevant energy/entropy tradeoff so that the bound
  `≤ C/sigmaP` holds (CP 03 §7 / the base-list lower bound). Again: real saving, or
  a named sorry — not the trivial bound.
* **Assembly** (`single_block_counting_faithful`): combine dominant + tiny +
  `sbee_nondominant'` into `SBEESavingBound`, without assuming the conclusion.

Report `lake build` and the exact remaining sorries. **Do NOT attempt
`sbee_nondominant'` (the FIE core) in this task** — it is reserved for F2b and
needs the entropy-descent argument (being worked out on the math side).

## NEXT TASK — F2b: the non-dominant FIE core (decisive) — against the FAITHFUL `sbee_nondominant'`

Formalize Condition SBEE's `partition_bound` route at the level of the
**single-block counting theorem** (CP 02 §4 / CP 03 §4 in the markdown), splitting
into cases and **proving the two easy cases**, leaving the hard case as a named
lemma. Create `RequestProject/SingleBlockCounting.lean` (import `SBEE`). Keep build
green; the hard case is an explicit, clearly-named `sorry` or hypothesis.

Target shape (adapt types to the existing `PrimeBlock`/`BlockEnergyData` in `SBEE.lean`):
- **Dominant case**: if some label $m$ covers $\ge(1-\rho)N$ vertices, the count is
  $\ll e^{\varepsilon R}(1+\sqrt R/\sigma_P)$ via majority correction (exception
  entropy $O(\log X)$ paid by energy). Prove it (or reduce to a small lemma).
- **Tiny case**: if almost all covered vertices lie in tiny classes, the short list
  is large enough that $R$ pays the crude entropy. Prove it.
- **Non-dominant substantial case**: state as `theorem sbee_nondominant … : … := sorry`
  with the precise hypotheses (no dominant label; substantial classes carry $\ge\rho N$).
  This is the FIE target (F2b).
- **Assemble**: the three cases ⇒ the single-block counting bound ⇒
  `ConditionSBEE.partition_bound` (construct a `ConditionSBEE` term whose
  `partition_bound` field is this theorem; `fourier_positivity_avoiding` stays as
  the circle-method target for F3).

Deliverable: `SingleBlockCounting.lean` with dominant+tiny proved, `sbee_nondominant`
isolated. Report which sorries remain.

## NEXT TASK — F2b: the non-dominant FIE core (decisive)

Prove `sbee_nondominant` from: `good_kSubset_exists_unconditional`
(`ClusterSelectionClosure.lean`, done) + regular-uniqueness (no short kernel ⇒ ≤1
witness per residual prime; FIE draft §21) + singular-tuple sparsity (elementary
count) + the ambient-sensitive entropy descent (two ranges $D\ll N^{1/2}$ /
$D\gg N^{1/2}$, overlapping — see core-packet note 24 §4 and the ambient-FIE
draft §§1–6) + `cross_label_divisor_energy` (done). **Isolate the first-capture
counting tree and any not-yet-rigorous descent step as clearly named sorries.**
The pattern of remaining sorries is the diagnostic (see core-packet note 26 §2).

---

## (superseded) F1b — discharge F1's hypotheses  [DONE 2026-06-09]

F1 (done, `ClusterSelectionClosure.lean`) proved `good_kSubset_exists_of_size'`
**conditional on** (i) a cluster-size bound `hL : ∀C∈family, (F∩C).card ≤ L`, and
(ii) the regime inequality `P.card*X0.card*C(L,k) < C(F.card,k)`. F1b proves both
from explicit arithmetic hypotheses, yielding an UNCONDITIONAL good-tuple theorem.

Add to `ClusterSelectionClosure.lean` (keep build green, no sorries):

**(A) Cluster-size lemma.** With hypotheses
`hF : ∀ q ∈ F, X ≤ q ∧ q ≤ 2*X`, `hp : Nat.Prime p.natAbs` (or `Prime p`),
`hpX : X ≤ p`, and `Short` instantiated as `fun x => 0 < |x| ∧ |x| ≤ Mτ`, prove
```
(F ∩ anchoredCluster Short F p q0 x0).card ≤ 4 * Mτ.toNat   -- (or 2*Mτ with a sharper count)
```
Proof outline: `q ∈ cluster ⇒ ∃ short x, q*x ≡ q0*x0 (mod p)`; since `0<|x|≤Mτ<X≤p`
and `p` prime, `IsCoprime x p`, so `q ≡ q0*x0*x⁻¹ (mod p)` lies in one residue
class mod `p`; an interval of length `X ≤ p` meets each class in ≤ 2 integers;
union over the `≤ 2*Mτ` short `x` gives `≤ 4*Mτ`. (Map `F∩cluster` into
`(short x) × (residue rep)` and bound the image.)

**(B) Regime instantiation.** With `L = 4*Mτ.toNat`, `X0.card ≤ 2*Mτ.toNat`,
`P.card ≤ X.toNat`, `F.card ≥ ⌈X^(7/8)⌉` (say), `Mτ ≤ ⌈X^(1/2)⌉`, `k = 4`, prove the
regime inequality `P.card*X0.card*Nat.choose L k < Nat.choose F.card k`. (At these
scales LHS `≪ X·Mτ⁵ = X^(7/2)` and RHS `≫ X^(7/2)`; make the constants explicit —
this is a concrete `Nat`/`Real` inequality, possibly via `Nat.choose` lower/upper
bounds `(n/k)^k ≤ C(n,k) ≤ n^k`.)

**(C) Unconditional corollary.** Combine (A),(B) with
`good_kSubset_exists_of_size'` to get `hasAnchoredGoodKSubset` from the arithmetic
hypotheses alone (no `hL`/`hregime` assumptions). Name it
`good_kSubset_exists_unconditional`.

This closes the cluster-selection lemma fully and de-islands it further. After
F1b, the next task is **F2** below.

## NEXT TASK — F2 (large): formalize FIE ⇒ ConditionSBEE

Assemble the single-block energy-entropy condition `ConditionSBEE.partition_bound`
from: the cluster selection (F1/F1b), regular-uniqueness (no short kernel ⇒ ≤1
witness per prime), singular-tuple sparsity, the ambient-sensitive entropy descent
(two ranges `D ≪ N^(1/2)` / `D ≫ N^(1/2)`, overlapping; see core packet note 24 §4
and the FIE drafts), and the cross-label divisor-energy ledger
(`SBEE.cross_label_divisor_energy`, already proved). **Isolate every genuinely-open
or not-yet-rigorous step as a clearly named `sorry`** — F2's purpose is to force
the markdown "essentially proved" pieces (esp. the first-capture counting tree of
the entropy descent) into either real proofs or precise sorries. This is the
decisive test of the SBEE route.

---

## (superseded) F1 — reciprocal-cluster selection lemma  [DONE 2026-06-09]

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
