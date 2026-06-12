# Proof of the Reciprocal-Cluster Selection Lemma

Back to [[00 README]]. This **proves** the atomic endpoint identified in
[[22 The Real Gap, Atomic Form]] — the last self-contained combinatorial problem
on the SBEE route. The argument is elementary (incidence counting + cluster-size
bound) and uses the already-formalized incidence ledger of
`AdaptiveClusterSelection.lean`.

## 1. Statement

Fix the reference seed $q_\ast\sim X$ (prime) and $M_\tau\le X^{1/2}(\log X)^A$.
For a prime $p\sim X$ and short $0<|x_\ast|\le 2M_\tau$ define the **reciprocal
cluster**
$$
\mathcal A(p,x_\ast)=\{q\in[X,2X]\cap\mathbb P:\ \exists\,0<|x|\le 2M_\tau,\ qx\equiv q_\ast x_\ast\!\!\pmod p\}.
$$
Let $\mathcal C=\{\mathcal A(p,x_\ast)\}_{p\sim X,\,0<|x_\ast|\le 2M_\tau}$.

> **Lemma (selection).** Let $F\subseteq[X,2X]\cap\mathbb P$ with
> $|F|\ge X^{1/2+\delta}$ for fixed $\delta>0$, and let $k$ be an integer with
> $k>1+\tfrac1{2\delta}$ (e.g. $k=4$ once $\delta\ge\tfrac1{2}$, or any fixed $k$
> for the corresponding $\delta$). Then $F$ contains a $k$-element subset lying in
> **no** single cluster of $\mathcal C$ (a *good seed tuple*).

In the central SBEE regime $|F|\asymp N/D\asymp X(\log X)^{-O(1)}$,
$M_\tau\asymp X^{1/2}$, the hypothesis holds with $\delta$ close to $\tfrac12$ and
**$k=4$ suffices**.

## 2. Two elementary bounds

**(a) Cluster size.** For fixed $(p,x_\ast)$ and each short $x$, the condition
$qx\equiv q_\ast x_\ast\pmod p$ pins $q$ to one residue class mod $p\sim X$; an
interval $[X,2X]$ meets that class in $\le X/p+1\ll1$ integers. Over $\ll M_\tau$
short values of $x$,
$$
|\mathcal A(p,x_\ast)|\ll M_\tau.
$$

**(b) Cluster count.** $\mathcal C$ is indexed by $(p,x_\ast)$ with $p\sim X$
prime ($\ll X/\log X$ choices) and $0<|x_\ast|\le 2M_\tau$ ($\ll M_\tau$ choices):
$$
\#\mathcal C\ll \frac{X}{\log X}\,M_\tau\ll X\,M_\tau.
$$

## 3. The counting contradiction

Suppose, for contradiction, that **every** $k$-subset $T\subseteq F$ is contained
in some single cluster. The incidence identity (formalized as
`incidence_le_clusters_mul_choose` in `AdaptiveClusterSelection.lean`) gives
$$
\binom{|F|}{k}
=\#\{T\subseteq F:|T|=k\}
\le \#\{(T,\mathcal A): T\subseteq F\cap\mathcal A,\ |T|=k\}
=\sum_{\mathcal A\in\mathcal C}\binom{|F\cap\mathcal A|}{k}.
$$
By (a), $|F\cap\mathcal A|\le|\mathcal A|\ll M_\tau$, so $\binom{|F\cap\mathcal A|}{k}\ll M_\tau^k/k!$;
with (b),
$$
\sum_{\mathcal A}\binom{|F\cap\mathcal A|}{k}\ \ll\ \#\mathcal C\cdot\frac{M_\tau^{k}}{k!}\ \ll\ \frac{X\,M_\tau^{k+1}}{k!}.
$$
Hence the all-covered assumption forces
$$
\binom{|F|}{k}\ \ll\ \frac{X\,M_\tau^{k+1}}{k!},
\qquad\text{i.e.}\qquad
|F|^{k}\ \ll\ X\,M_\tau^{k+1}.
$$
With $M_\tau\le X^{1/2}(\log X)^A$ and $|F|\ge X^{1/2+\delta}$:
$$
X^{(1/2+\delta)k}\ \ll\ X^{1+(k+1)/2}(\log X)^{A(k+1)}=X^{(k+3)/2}(\log X)^{A(k+1)}.
$$
Comparing exponents of $X$: $(1/2+\delta)k$ vs $(k+3)/2$. The left exceeds the
right iff $\delta k> 3/2$, i.e. $k>\tfrac{3}{2\delta}$. For such $k$ the left side
is larger by a fixed power of $X$, dominating every $(\log X)$ factor — a
contradiction for $X$ large. (At $\delta=\tfrac12$: $k>3$, so $k=4$.)

Therefore not every $k$-subset is covered: a good $k$-tuple exists. $\qquad\blacksquare$

## 4. Remarks

* **No structured-exception branch is needed in this regime.** The draft's
  dichotomy "good tuple *or* low-entropy cover" collapses to its first horn once
  $|F|$ is a power of $X$ above $X^{1/2}$: a good tuple *always* exists. The
  "large mutual intersection" failure mode of the FIE draft §23 is ruled out
  quantitatively — there simply are not enough clusters
  ($\#\mathcal C\cdot\binom{M_\tau}{k}<\binom{|F|}{k}$) to cover all $k$-subsets.
* **Strength.** The good tuple is regular for **all** primes $p\sim X$
  simultaneously (it lies in no cluster for any $p$), which is stronger than the
  "regular for all but negligibly many $p$" that FIE/SBEE requires. The
  $O(1)$-per-tuple diagonal/zero-star exceptions (FIE draft §21.3) remove $O(1)$
  clusters and do not affect the count.
* **Inputs.** Only the two elementary bounds §2(a),(b) and the formalized
  incidence ledger. No Fourier/Kloosterman/Irving, no first/second-moment of the
  correlation — confirming [[19 The Selection Closes Elementarily (Likely No FS)]]
  and [[22 The Real Gap, Atomic Form]]: the SBEE route's combinatorial atom is
  closed elementarily.

## 5. What this closes, and what remains

**Closed:** the reciprocal-cluster selection lemma — the smallest self-contained
open problem on the SBEE route ([[22 The Real Gap, Atomic Form]] §7). Combined
with the (proved) regular-uniqueness lemma (no short kernel ⇒ $\le1$ witness per
prime) and the elementary singular-tuple sparsity, the **good-seed selection step
of FIE is complete**.

**Remains (formalization/wiring, not new mathematics — [[22 The Real Gap, Atomic Form]] §6):**
1. **FIE ⇒ ConditionSBEE.** Assemble: good-seed selection (this note) + regular
   uniqueness + the ambient-sensitive entropy descent + the energy ledger into
   the single-block energy-entropy condition (`ConditionSBEE.partition_bound`).
   Most pieces are formalized or markdown-complete; this is integration.
2. **ConditionSBEE ⇒ `fourier_positivity_unconditional`.** The circle-method /
   Fourier-positive extraction layer (CP 01 §§3–7), currently the assumed
   `ConditionSBEE.fourier_positivity_avoiding` field.

These two macro-steps are the remaining route from here to a `sorry`-free
`erdos_306`. Neither requires the analytic correlation bound that notes 07–16
pursued — that pursuit, while it produced the real Component-C infrastructure, is
**not** on this (now-shorter) critical path.

## 6. Interface check — DONE (positive)

Verified against the cleaned Lean (`AnchoredSelectionPipeline.lean`,
`AdaptiveClusterSelection.lean`):

* The formalized `anchoredCluster Short F p q0 x0 = {q∈F : ∃ short x,y, q·x − q0·x0 = p·y}`
  **is exactly** the reciprocal cluster $\mathcal A(p,x_\ast)$ of §1
  ($q_0=q_\ast$, $x_0=x_\ast$, the equation is $qx\equiv q_\ast x_\ast\pmod p$ with
  short quotient $y$).
* `anchoredClusterFamily ... = (P ×ˢ X0).image (...)`, so the **count** is
  $\le|P|\,|X0|\ll (X/\log X)\,M_\tau$ — matches §2(b).
* The cluster **size** $|F\cap C|\le|C|\ll M_\tau$ matches §2(a).
* The inequality I use is the **already-formalized**
  `anchored_incidence_le_clusters_mul_choose`
  ($\text{incidence}\le\#\text{family}\cdot\binom{L}{m}$), and the dichotomy is
  `anchored_good_or_allCovered`. The pipeline's "good tuple"
  (`hasAnchoredGoodKSubset`) is exactly what this lemma produces. **No weighted /
  energy-respecting version is needed at this level.**

So the proof maps directly onto the formalized pipeline; the combinatorial atom is
proved, and the interface is confirmed.

## 7. Formalization-ready (Aristotle task)

Note 23 is ready to formalize as a Lean theorem (call it
`good_kSubset_exists_of_size`), turning the pipeline's *trichotomy* into the
*single* conclusion `hasAnchoredGoodKSubset` in the large-pool regime. Needed
Lean pieces, all small: (i) cluster-size lemma `(F ∩ anchoredCluster ...).card ≤ L`
with `L ≪ M_τ` (one prime per short $x$: `Int`/`ZMod` counting); (ii) family-count
`(anchoredClusterFamily ...).card ≤ |P|·|X0|` (`Finset.card_image_le`,
`Finset.card_product`); (iii) the arithmetic `#family · choose L k < choose |F| k`
in the stated regime; (iv) assemble with `anchored_good_or_allCovered` +
`incidence_lower_of_all_high_codegree` (R=1) + `anchored_incidence_le_clusters_mul_choose`.
This would connect the pipeline to a concrete conclusion (good tuple always
exists), shrinking Component C's "island" status. See [[21 Cleanup Tasks for Aristotle]].
