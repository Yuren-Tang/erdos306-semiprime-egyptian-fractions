# Closure Plan: Lean-Verified vs Markdown

Back to [[00 README]]. This note answers a sharp question: *"you keep saying parts
need auditing — didn't Lean already verify them?"* It separates **machine-verified**
from **hand-audited markdown**, and lays out the finite formalization sequence that
would **actually close** the proof (so this is not an endless audit loop).

## 1. What Lean has actually machine-verified

The `lean/` package builds (`lake build`) with one intended open sorry. Machine-
verified content:

* **Component C** (CRT lattices, `AnchoredDeterminantRank`, `SplitStarCorrelation`,
  the cluster-cover incidence machinery `AdaptiveClusterSelection` /
  `ClusterCoverBookkeeping`, …): sorry-free **algebra/combinatorics**.
* **L1 support leaves**: `BernoulliFourier`, `LatticeSpan`, `CrossLabelEnergy`,
  `SemiprimeInfinity`, `Defs`, and the reduction `reduction_to_unit_numerator_avoiding`.
* The numeric instances `erdos_306_b2..b29`.

**But this verified content is either disconnected or assumes the hard input:**
* Component C is an **island** ([[20 Lean Core Audit and Dependency Map]]); its top
  result `residualPrimeShellBound_of_intervalBound` **assumes** the shell bound.
* `erdos_306` ⟸ `fourier_positivity_unconditional` (**sorry**), and the SBEE route's
  `ConditionSBEE` is an **assumed** structure (its key field *is* the conclusion).

## 2. What is markdown-only (NOT machine-verified) — what "audit" meant

These live only in CP 01–03 and the FIE drafts; Lean has never seen them. My
"audits" were **me reading the informal proofs by hand** — useful, but fallible,
and *not* the same as machine verification:

| Link | Where | Machine-checked? | Hand-audited by me? |
|---|---|---|---|
| L1 circle method (Fourier inversion, main/minor arc) | CP 01 §§3–7 | ❌ | ✓ (standard) |
| Edge construction (Lemma 9.1) | CP 03 §9 | ❌ | ✓ (no gap) |
| L2 SBEE ⇒ minor arc (Prop 8.1) | CP 02 §4 | ❌ | partial |
| L3 cluster selection | [[23 Proof of the Reciprocal-Cluster Selection Lemma]] | ❌ (Lean has the *ingredients*) | ✓ (proved) |
| L3 entropy descent | FIE drafts §§1–11 | ❌ | not yet |
| L3 singular sparsity | CP 02 §21.3 | ❌ | ✓ (elementary) |

So "auditing" ≠ "re-checking what Lean did." Lean verified the island (C) and the
leaves; the **load-bearing main chain is unverified markdown**.

## 3. The honest consequence

Hand-auditing markdown can raise confidence but cannot *close* the proof: an LLM
reading informal mathematics will miss things (note 20 already caught a *false*
"SBEE is proved" claim that had stood in the package). **The only reliable closure
is to formalize the main chain in Lean**, which forces every "standard" /
"essentially proved up to log constants" claim to become a real proof or an
explicit `sorry`.

## 4. Closure sequence (finite, idea-free modulo the proved/audited math)

Each step is an Aristotle formalization task; together they replace the markdown
chain with a machine-verified one. Ordered by leverage:

1. **F1 — Formalize cluster selection (note 23).** De-islands Component C: turn
   `anchored_selection_pipeline`'s trichotomy into the single conclusion
   `hasAnchoredGoodKSubset` in the large-pool regime, using the proved
   `anchored_incidence_le_clusters_mul_choose` + a cluster-size lemma + the
   arithmetic. **Ready now** (note 23 §7); see `aristotle-delivery/TASK.md`.
2. **F2 — Formalize the FIE chain to `ConditionSBEE`.** Assemble cluster selection
   (F1) + regular-uniqueness + singular-sparsity + entropy descent + energy
   ledger into `ConditionSBEE.partition_bound`. The entropy descent (the one link
   I have *not* hand-audited) gets forced into real proofs/sorries here — this is
   where any hidden FIE gap surfaces.
3. **F3 — Formalize L1 (circle method).** `ConditionSBEE ⇒ fourier_positivity_unconditional`:
   Fourier inversion on `ZMod L`, Bernoulli charFun bound (have it), edge
   construction (audited), Gaussian main arc, minor arc from Prop 8.1. Substantial
   Mathlib analysis but standard; the open analytic content is nil (only SBEE).
4. **F4 — Connect.** With F1–F3, `erdos_306` becomes `sorry`-free (or with only
   honestly-named residual sorries pinpointing any real remaining gap).

## 5. What this plan does and does not claim

* It **does** claim there is no remaining *unproved mathematical idea* visible on
  this route (the analytic heart is standard; the combinatorial heart is proved).
* It **does not** claim the proof is finished. Formalization routinely exposes
  gaps the markdown hid — especially in F2 (entropy descent) and F3 (the
  construction details). The plan's value is that it converts vague confidence
  into machine-checkable steps, each of which either closes or names a precise
  residual sorry.

## 6. Immediate action

Drive **F1** now (it is ready, high-leverage, de-islands C). Its task spec is in
`aristotle-delivery/TASK.md` (task **F1**). After F1 returns, F2 is the decisive
test of the FIE route (entropy descent). Stop hand-auditing markdown; let the
machine check.
