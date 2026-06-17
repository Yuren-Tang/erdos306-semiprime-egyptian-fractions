# The Real Gap, Atomic Form

Back to [[00 README]]. Consolidates the SBEE/FIE route to its irreducible
endpoint, by reading the archived `Ambient-sensitive FIE proof draft.md` (§§20–23)
to its conclusion and matching it against [[17 The First Moment Is Trivial (Correction)]]–[[19 The Selection Closes Elementarily (Likely No FS)]].

## 1. The whole SBEE/FIE route bottoms out in ONE finite lemma

The FIE draft's own endpoint (its §23) is the **reciprocal-cluster selection
lemma**. With reference seed $q_\ast\sim X$, define for a prime $p\sim X$ and short
$0<|x_\ast|\le2M_\tau$ the **reciprocal cluster**

$$
\mathcal A(p,x_\ast)=\{q\in[X,2X]\cap\mathbb P:\ \exists\,0<|x|\le2M_\tau,\ qx\equiv q_\ast x_\ast\!\!\pmod p\},\qquad |\mathcal A|\ll M_\tau.
$$

Given a fingerprint seed pool $F\subset[X,2X]\cap\mathbb P$, $|F|\asymp M\asymp N/D$:

> **Reciprocal-cluster selection.** Either $F$ contains a $k$-tuple lying in no
> single cluster (a **good seed tuple** ⇒ regular uniqueness, one witness per
> residual prime ⇒ no residual polylog label multiplicity ⇒ FIE/SBEE closes), or
> $F$ is covered by few clusters (**low-entropy structured exception**, charged to
> the ledger).

Everything upstream (DRC extraction, witness matrices, two-core bookkeeping,
single-block counting) is formalized or formalization-ready; this selection is
"the only remaining combinatorial issue" (FIE draft §22).

## 2. The cover logic (computed)

Suppose **no good $k$-tuple**: every $k$-subset of $F$ lies in a cluster. Fix a
$(k-1)$-subset $T$. By `ClusterCoverBookkeeping` (`ksubset_cover` +
`card_le_of_extension_cover`), $F\subseteq T\cup\bigcup\{\mathcal A:T\subseteq\mathcal A\}$, so

$$
|F|\le (k-1)+R(T)\cdot L,\quad R(T)=\#\{(p,x_\ast):T\subseteq\mathcal A(p,x_\ast)\},\ L\ll M_\tau.
$$

Hence no-good-tuple $\Rightarrow R(T)\gtrsim |F|/M_\tau\asymp M/M_\tau\asymp X^{1/2}(\log X)^{-O(1)}$
for some $T$. **Many clusters through $T$** means many primes $p$ admitting a
simultaneous short reciprocal relation $q_jx_j\equiv q_\ast x_\ast\pmod p$ for all
$q_j\in T$ — i.e. $T\cup\{q_\ast\}$ is a **singular (structured) seed tuple**.

## 3. The hard input is already elementary (global sparsity)

The singular tuples are globally sparse, by the **direct count** (FIE draft §21.3,
= [[18 What SBEE Actually Needs (Synthesis)]] §2): fixing $(p,q_\ast,x_\ast,x_i)$,
$q_i\equiv q_\ast x_\ast x_i^{-1}\pmod p$ gives $O(1)$ primes, so each seed
coordinate has $O(M_\tau)$ choices and

$$
\#\{\text{singular tuples}\}\ll N^2 M_\tau^{k+1}(\log X)^{O(1)}\quad\text{vs. free }N^{k+1},
$$

a power saving $X^{k-1}/M_\tau^{k+1}$, positive for $M_\tau^{k+1}\ll X^{k-1}$, i.e.
$k\ge4$ at $M_\tau\asymp X^{1/2}$. **No Fourier/Kloosterman; elementary.** This is
the same fact as the cluster size $|\mathcal A|\ll M_\tau$ and the determinant
structure of [[08 Anchor Energy and the Joint Obstruction]]/[[09 Cluster Concentration and the Structured Family]].

## 4. The residual is a hypergraph-selection packaging step

So the genuinely-remaining piece is **not** an estimate but a packaging:

> Given that the singular $k$-uniform hypergraph $\mathcal H_{\rm sing}$ is globally
> sparse ($\ll N^2M_\tau^{k+1}$) **and** contained in a union of complete
> hypergraphs on size-$\ll M_\tau$ reciprocal clusters, show a pool $F$ of size
> $\asymp M$ either contains an $\mathcal H_{\rm sing}$-free $k$-tuple or is
> low-entropy-covered. The only failure mode (FIE draft §23) is **many clusters
> with large mutual intersections**; but a large intersection
> $\mathcal A(p,x_\ast)\cap\mathcal A(p',x_\ast')$ forces $x_\ast x'-x_\ast'x\equiv0\pmod{p\ (\text{or }p')}$
> with $|x_\ast x'-x_\ast'x|\ll M_\tau^2\asymp X$ — a small-determinant relation,
> hence itself structured. (Same determinant mechanism as the anchor side.)

This is finite, arithmetic, bounded-uniformity hypergraph combinatorics — the
draft calls it "much smaller than the original FIE problem."

## 5. Honest bottom line (consolidates notes 07–21)

* The **single open analytic object** in Lean is `fourier_positivity_unconditional`
  ([[20 Lean Core Audit and Dependency Map]]).
* Its **SBEE-route decomposition** (the only one with formalized infrastructure)
  reduces, after the circle-method/FIE machinery, to the **reciprocal-cluster
  selection lemma** (§1).
* The lemma's **hard input — global singular-tuple sparsity — is elementary and
  proved** (§3), with $k\ge4$ seeds. The **residual is a finite hypergraph-cover
  packaging step** (§4), whose only obstruction (large cluster intersections) is
  itself a small-determinant structured relation.
* Therefore: the SBEE route's remaining mathematics is **finite/arithmetic, not
  analytic**. The heavy Fourier/Irving/FS apparatus (notes 11–16) is **not on this
  route's critical path** (it surfaces only in Irving-good pruning). This vindicates
  the structure-first instinct: the genuine residual is combinatorial bookkeeping.

## 6. The one caveat that keeps this "route", not "done"

The chain "reciprocal-cluster selection ⇒ ConditionSBEE ⇒
`fourier_positivity_unconditional`" is **established only in markdown** (CP 01–03 +
the FIE drafts), **not in Lean** (Component C is disconnected,
[[20 Lean Core Audit and Dependency Map]]). And the circle-method layer
(`ConditionSBEE` ⇒ Fourier positivity) is itself the assumed
`ConditionSBEE.fourier_positivity_avoiding` field — unproven. So two macro-steps
remain unformalized even if the cluster selection (§4) is finished:
1. circle method: `ConditionSBEE` ⇒ `fourier_positivity_unconditional`;
2. FIE/SBEE: cluster selection ⇒ `ConditionSBEE`.

## 7. Next action (the actual frontier) — DONE

The **reciprocal-cluster selection lemma** is now **proved** in
[[23 Proof of the Reciprocal-Cluster Selection Lemma]]: an elementary incidence
count shows that for $|F|\gg X^{1/2+\delta}$ and a fixed $k>3/(2\delta)$ (e.g.
$k=4$), the clusters are simply too few/small to cover all $k$-subsets, so a good
tuple always exists — no structured-exception branch needed in this regime, no
analytic input. The combinatorial atom of the SBEE route is closed. What remains
is the two macro-wiring steps of §6 (FIE ⇒ ConditionSBEE; ConditionSBEE ⇒
`fourier_positivity_unconditional`), which are formalization/integration, not new
mathematics — cf. [[21 Cleanup Tasks for Aristotle]] C3a.
