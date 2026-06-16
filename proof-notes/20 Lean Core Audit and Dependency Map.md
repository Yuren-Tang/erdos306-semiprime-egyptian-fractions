# Lean Core Audit and Dependency Map

Back to [[00 README]]. This is a full audit of `lean/RequestProject/` (21 files,
3438 lines) — what is **real**, **assumed/laundered**, **sorry**, **duplicated**,
or **disconnected**. It supersedes the looser [[03 Lean Formalization Map]] as the
authoritative current map. Produced by reading every file's declarations, proof
bodies, and the import DAG.

## 0. Headline

* **Exactly one real `sorry`:** `fourier_positivity_unconditional`
  (`FourierPositivity.lean`). The `admit` flagged by grep is a false positive
  (the word "admit" in a comment).
* **`erdos_306` (unconditional) depends on that one sorry and nothing else hard.**
  `erdos_306 := reduction_to_unit_numerator_avoiding (fun T b hb hbsf =>
  fourier_positivity_unconditional …)`. It does **not** route through
  `ConditionSBEE` or the collision infrastructure.
* **The Lean splits into three essentially disconnected components** (A, B, C
  below). The markdown narrative connects them; the Lean does not.

## 1. The dependency DAG (who imports whom)

```
Component A (main theorem, gap = 1 sorry):
  Erdos306Unconditional ← MainTheorem, FourierPositivity, Defs, SemiprimeInfinity
  MainTheorem           ← Defs, SBEE        (SBEE used only by erdos_306_conditional)
  FourierPositivity     ← Defs, SemiprimeInfinity, LatticeSpan, BernoulliFourier, CrossLabelEnergy

Component B (SBEE conditional route, NOT used by erdos_306):
  SBEE                  ← Defs, LatticeSpan, BernoulliFourier, SemiprimeInfinity

Component C (rational-collision infrastructure, DISCONNECTED from A and B):
  ClusterCoverBookkeeping → AdaptiveClusterSelection → ClusterLineIncidence
       → ReciprocalCRTProduct → ValidCRTLattice → AnchoredCRTLattice
       → AnchoredDeterminantRank → PrimitiveProjectiveNormalization
       → ResidualPrimeShellCRT → SplitStarCorrelation
       AnchoredSelectionPipeline (← AnchoredCRTLattice, AdaptiveClusterSelection)

Orphan: SemiprimeReciprocals (imported by nobody)
```

Roots (imported by nothing): `Erdos306Unconditional` (the goal),
`SplitStarCorrelation`, `AnchoredSelectionPipeline`, `SemiprimeReciprocals`.
The last three are **dead ends** w.r.t. `erdos_306`.

## 2. Component A — main theorem skeleton (REAL modulo the one sorry)

* `MainTheorem.reduction_to_unit_numerator_avoiding` — **REAL** (induction on $a$;
  reduces $a/b$ to disjoint copies of $1/b$). Parametric in the avoiding-rep
  hypothesis `h`; does **not** use `ConditionSBEE` internally.
* `Erdos306Unconditional`: `erdos_306` (uses the sorry), the numeric examples
  `erdos_306_b2..b29` (**REAL** verified subset sums), `triple_prime_sum`
  (**REAL** identity). `erdos_306` ⟸ `fourier_positivity_unconditional`.
* Leaves `Defs, SemiprimeInfinity, LatticeSpan, BernoulliFourier, CrossLabelEnergy`
  — **all REAL** (squarefree/gcd, prime-existence, Bernoulli charFun bounds,
  cross-label energy positivity).
* **Misleading docstring:** `Erdos306Unconditional` says "SBEE is proved / the sole
  condition holds." **False.** SBEE is *bypassed* by assuming
  `fourier_positivity_unconditional` (sorry) directly. Should be corrected.

## 3. Component B — SBEE (mostly LAUNDERED; conditional, unused by `erdos_306`)

`ConditionSBEE : Prop` is an **assumed structure** whose field
`fourier_positivity_avoiding` **is literally the conclusion**. Of its 9 theorems:

* **Laundered (proof returns a hypothesis):** `cross_block_label_mismatch := hlb`,
  `peierls_collapse := hbound`, `ordinary_diagonal_counting := hbound`,
  `global_control_partition := hbound`.
* **Vacuous via the assumed structure:** `single_block_counting`
  (`:= hSBEE.partition_bound …`), `fourier_positivity`
  (`:= hSBEE.fourier_positivity_avoiding …`).
* **Trivially true (not the real statement):** `irving_good_pruning`
  (`⟨P.primes, refl, omega⟩` — gives $2N\ge N$, not a Kloosterman dispersion bound);
  `IrvingKloostermanBound'.bound` concludes **`True`**.
* **Genuinely REAL:** `cross_label_divisor_energy`, `edge_construction`.

So Component B is **not a proof of SBEE** — it is a dependency-structure stub with
two real sub-lemmas. `erdos_306_conditional` is conditional on the assumed
`ConditionSBEE`.

## 4. Component C — rational-collision infrastructure (REAL but DISCONNECTED)

All ~11 files are **REAL, no-sorry** algebra/combinatorics: CRT lattices, the
anchored determinant rank obstruction, primitive normalization, split-star
equivalence and the exact correlation identity `splitCorrelation_eq_card`, the
cluster-cover incidence machinery (`AdaptiveClusterSelection`,
`ClusterCoverBookkeeping`, `ClusterLineIncidence`). These are the formalization of
the active problem of [[02 Active Rational-Collision Problem]] and the cluster
selection of [[19 The Selection Closes Elementarily (Likely No FS)]].

**But:** (i) the top result `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound
:= hbound …` **assumes** the shell bound as a hypothesis; (ii) **nothing connects
C to B or A** — there is no Lean lemma "shell bound ⟹ ConditionSBEE" or "⟹
fourier_positivity_unconditional." The connection lives only in the CP markdown.

So Component C is real scaffolding for the *route* toward the arithmetic input,
not wired into any sorry-free or even conditional `erdos_306`.

## 5. Duplication and dead code

* **`SemiprimeReciprocals` ≈ `SemiprimeInfinity`** (duplicate: `exists_large_semiprime_coprime_not_in`
  vs `exists_semiprime_coprime_not_in`). `SemiprimeReciprocals` is **orphaned** —
  delete or merge.
* **`AnchoredCRTLattice` / `ValidCRTLattice` / `ReciprocalCRTProduct`** share heavily
  duplicated patterns (`base_diff`, `local_residue`, `_smul`, `dvd_of_*Hit`,
  `xi_eq_div`). Anchored = ref-anchored copy of valid. Candidate for a shared
  generic CRT-lattice lemma.
* Archive holds **7 versioned copies** `output-final_aristotle{,_2.._7}` of the
  whole package — fine as history, but only `_7` (the curated source of `lean/`)
  is current.

## 6. The honest formalization state

$$
\texttt{erdos\_306}\ \Longleftarrow\ \texttt{fourier\_positivity\_unconditional}\ (\textbf{sorry}),
$$

with **no hidden dependence** on `ConditionSBEE` or Component C. Everything else is
either (a) genuinely proved support (Component A leaves, the numeric examples),
(b) an assumed/laundered conditional route (Component B), or (c) real but
disconnected route-infrastructure (Component C).

The whole mathematical problem is the single analytic theorem
`fourier_positivity_unconditional`. The SBEE route (B) and the collision route (C)
are two **parallel, unfinished** strategies for it, neither wired to a sorry-free
proof.

## 7. Cleanup actions (good Aristotle tasks)

1. **Correct the false "SBEE is proved" docstring** in `Erdos306Unconditional`.
2. **De-vacuize `SBEE`:** delete or clearly mark the four `:= hbound/hlb`
   restatements; restate `IrvingKloostermanBound'` with its real conclusion
   (currently `True`); state `irving_good_pruning` honestly.
3. **Delete/merge `SemiprimeReciprocals`** into `SemiprimeInfinity`.
4. **Factor the duplicated CRT-lattice machinery** (Valid/Anchored/Reciprocal)
   into one generic file.
5. **Wire Component C to B:** formalize "residual shell bound ⟹ `ConditionSBEE`"
   (currently only markdown), so C stops being an island — or explicitly mark C
   as route-exploration off the critical path.
6. After cleanup, the package honestly reads: **one sorry, two named unfinished
   routes toward it, everything else real.**

## 8. Implication for the analytic work (notes 07–19)

My analysis targets the **correlation bound** = the arithmetic input of Component
C, which (per CP markdown) feeds `ConditionSBEE` (B) ⟹ the *conditional* theorem.
The *unconditional* `erdos_306` instead needs `fourier_positivity_unconditional`
directly. These coincide mathematically (the correlation bound is the crux of the
Fourier-positive extraction), but **in Lean they are different targets**. Any
eventual formalization must either prove `fourier_positivity_unconditional`
outright or build the C ⟹ B ⟹ A wiring. This audit says: **do not mistake the
real Component-C files for progress on the `erdos_306` sorry** — they are a
parallel route whose own top bound is still assumed.
