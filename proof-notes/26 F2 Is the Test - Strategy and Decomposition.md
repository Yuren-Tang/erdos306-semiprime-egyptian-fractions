# F2 Is the Test: Strategy and Decomposition

Back to [[00 README]]. Records the strategic role of **F2** (formalize
`FIE ⇒ ConditionSBEE`) and its decomposition, after F1+F1b made the cluster
selection unconditional ([[23 Proof of the Reciprocal-Cluster Selection Lemma]],
`ClusterSelectionClosure.lean`: `good_kSubset_exists_unconditional`).

## 1. Why F2 is the decisive test

Remaining unformalized chain:
$$
\texttt{erdos\_306}\ \underset{\text{F3 circle method}}{\Longleftarrow}\ \text{ConditionSBEE}\ \underset{\text{F2 FIE}}{\Longleftarrow}\ \{\text{cluster selection (done)}+\text{uniqueness}+\text{sparsity}+\text{entropy descent}+\text{ledger}\}.
$$

* **F3 (circle method)** is standard analytic NT (audited, edge construction
  sound, [[24 End-to-End Core Map and How Close We Are]] §2,§5). Low *fundamental*
  risk; a large Lean-analysis formalization that may hit *technical* snags.
* **F2 (FIE ⇒ ConditionSBEE)** contains **all genuinely novel content** (SBEE
  single-block counting, the cluster machinery, the ambient-sensitive entropy
  descent). It is the one link with a not-yet-rigorous piece (the first-capture
  counting tree, [[24 End-to-End Core Map and How Close We Are]] §4 / ambient-FIE
  draft §6).

**Consequences (answering "is F2 the whole test?"):**
* If F2 formalizes with **no residual sorry**, the remaining gap (F3) is standard
  ⇒ high confidence. *Caveats:* (a) F3's large analysis formalization could surface
  technical issues; (b) "F2 OK" must mean genuinely closed, not "closed modulo a
  descent sorry"; (c) the F2↔F3 parameter compatibility (edge construction must
  deliver blocks satisfying both SBEE's hypotheses and $\sigma_E\asymp\sigma_{\rm ctrl}$)
  is a joint constraint, audited-sound but unformalized.
* If F2 **fails / needs a sorry that won't close**, it is **almost certainly the
  fundamental problem** — and the deepest such failure would be that
  **ConditionSBEE is false**, not merely hard, which would kill the route. The
  reduction, edge construction, and circle method are routine and unlikely to
  harbor a *fundamental* flaw.

So: **F2 is the crux test of whether the SBEE route is sound.**

## 2. Decomposition of F2 (CP 02 §4 / CP 03 §4)

`ConditionSBEE.partition_bound` ⇔ single-block counting
$\#\{a:Q_P(a)\le R\}\ll_\varepsilon e^{\varepsilon R}(1+\sqrt R/\sigma_P)$, which
splits by the structure of the low-energy assignment:

* **Dominant case** — one label $m$ has $|C_m|\ge(1-\rho)N$: handled by Irving-good
  majority correction; exception entropy $O(\log X)$ paid by energy. *Easier.*
* **Tiny case** — almost all covered vertices in tiny classes: forces the short
  list $\mathcal L$ so large that $R$ is already large enough to pay the crude
  entropy. *Easier.*
* **Non-dominant substantial case** = **Condition SBEE itself**: the hard core,
  proved (on the route) by the FIE/cluster machinery + entropy descent. *Hard.*

### F2a — single-block counting skeleton
Formalize the counting theorem with the dominant and tiny cases **proved**, and
the non-dominant substantial case stated as a named lemma/hypothesis
(`sbee_nondominant`) fed by FIE. Medium effort; isolates the hard case.

### F2b — the non-dominant case (the decisive sub-test)
Assemble `sbee_nondominant` from: `good_kSubset_exists_unconditional` (cluster
selection, done) + regular-uniqueness (no short kernel ⇒ ≤1 witness/prime) +
singular sparsity + the ambient-sensitive entropy descent (two ranges
$D\lessgtr N^{1/2}$, overlapping) + the cross-label divisor-energy ledger
(`cross_label_divisor_energy`, done). **Isolate the first-capture counting tree
and any not-yet-rigorous descent step as clearly named sorries.** The pattern of
which sorries remain *is the diagnostic*: if they are only "tedious counting-tree"
sorries, the route is sound modulo write-up; if a sorry is unprovable (e.g. the
descent inequality genuinely fails, or SBEE is false), that is the fundamental
problem.

## 3. My role from here

The mathematical ideas on this route are, as far as I can determine, complete
([[25 Closure Plan - Lean-Verified vs Markdown]]). So my contribution to F2 is
**the precise assembly recipe** (this note + CP 01–03 + the FIE drafts) and, when
F2/F2b returns sorries, **attacking exactly those sorries as the real
mathematical gaps**. Formalization itself → Aristotle. F2b's returned sorries are
the first machine-level verdict on whether the SBEE route closes.

## 4. Next action

Ferry **F1b** result is integrated; the delivery `TASK.md` now carries **F2a**
then **F2b**. Run F2a (skeleton) first — it is the lower-risk half and sets up the
exact `sbee_nondominant` interface that F2b must hit.
