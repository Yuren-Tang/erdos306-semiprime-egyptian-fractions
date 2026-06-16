# The Selection Closes Elementarily (Likely No FS)

Back to [[00 README]]. Synthesis of [[17 The First Moment Is Trivial (Correction)]],
[[18 What SBEE Actually Needs (Synthesis)]], and the archived cluster-cover
machinery (`../archive/草稿區/Reciprocal cluster cover proof draft.md`,
`AdaptiveClusterSelection.lean`, `ClusterCoverBookkeeping.lean`,
`ClusterLineIncidence.lean`).

**Tentative but well-supported conclusion: the good-seed selection — hence the
regular (non-structured) side — closes by elementary cluster counting with
$\ge4$ seeds. The heavy FS/Kloosterman machinery of notes 11–16 is likely *not*
needed for the active correlation endpoint.**

## 1. The selection uses an averaged incidence ledger, not a per-tuple bound

`AdaptiveClusterSelection.lean` runs the good-seed dichotomy on the **codegree
incidence ledger** (a first-moment / summed quantity):

$$
\sum_{\substack{T\subset F\\|T|=m}}\operatorname{codeg}(T)
\ \le\
\sum_{\mathcal A}\binom{|F\cap\mathcal A|}{m},
$$

with the cardinal cover bound $|F|\le|T|+RL$ (`ClusterCoverBookkeeping.lean`) in
the low-codegree branch. **Both branches consume only the summed ledger and the
cluster sizes — never a per-tuple equidistribution bound.** This is exactly the
first-moment regime that [[17 The First Moment Is Trivial (Correction)]] shows is
elementary.

## 2. The arithmetic inputs are elementary

* **Cluster size.** A reciprocal cluster
  $\mathcal A(p,q_\ast,x_\ast)=\{q\sim X: q\equiv q_\ast x_\ast x^{-1}\,(p),\ |x|\ll M_\tau\}$
  has $\le1$ prime $q$ per $x$, so $|\mathcal A|\ll M_\tau\asymp X^{1/2}$.
  **Elementary** (CP 02 §2 kernel count).
* **Number of clusters.** Indexed by $(p,x_\ast)$, $p\sim X$, $|x_\ast|\ll M_\tau$:
  $\ll X\cdot M_\tau$. **Elementary.**
* **Ledger bound.** Hence
  $\sum_{\mathcal A}\binom{|F\cap\mathcal A|}{m}\ll X M_\tau\binom{M_\tau}{m}\ll X M_\tau^{m+1}$.

## 3. Four seeds close it (the elementary condition)

A good $m$-tuple exists unless $F$ is cluster-covered, which (cardinal bound)
needs $\sum_{\mathcal A}\binom{|F\cap\mathcal A|}{m}\gtrsim\binom{|F|}{m}\asymp M^m$
with $M=|F|\asymp N/D\asymp X(\log X)^{-O(1)}$. So a good tuple exists once

$$
X\,M_\tau^{m+1}\ \ll\ X^{m}(\log X)^{-C}
\iff
M_\tau^{m+1}\ll X^{m-1}(\log X)^{-C}.
$$

At the central scale $M_\tau\asymp X^{1/2}$ this is $X^{(m+1)/2}\ll X^{m-1}$, i.e.
$m>3$ — **$m\ge4$ seeds suffice.** This is exactly CP 02's displayed condition
$M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}$ and its "four non-reference seeds" remark.

**So the good-seed selection closes by elementary cluster counting once $\ge4$
seeds are extracted.** No reciprocal-sum cancellation (Garaev/Irving/FS) enters.

## 4. Reconciliation with the "hard correlation bound" framing

CP 02 and the cluster-cover draft repeatedly *restate* the endpoint as the
per-tuple correlation bound $\sum_pA_{04}(p)B_{123}(p)\ll(\log X)^C(1+H^6/X^3)$
"unless structured." That is the clean, sufficient arithmetic statement — but the
**machinery actually deployed** (`AdaptiveClusterSelection` + incidence ledger)
needs only the *summed* codegree and *elementary* cluster sizes. The per-tuple
correlation bound is a stronger statement than the selection requires.

This dovetails with:
* [[17 The First Moment Is Trivial (Correction)]] — the first moment is trivial;
* [[18 What SBEE Actually Needs (Synthesis)]] §2 — structured tuples power-thin
  elementarily.

Together: **structured side power-thin (elementary) + regular side via summed
ledger with $\ge4$ seeds (elementary) ⟹ the active correlation endpoint closes
without FS.**

## 5. Where FS / Irving still genuinely enters

Irving's Kloosterman bound is still used — but in **Irving-good pruning** (CP 03
Lemma 2.1 / `SBEE.lean` `IrvingKloostermanBound'`), to produce blocks with phase
dispersion, *not* in the correlation endpoint. That pruning is a separate, prior
step. So the project does cite Irving, but the **active arithmetic bottleneck**
(this packet's focus, notes 02–18) is the cluster selection, which is elementary.

## 6. Caveats (why this is "likely", not "certain")

This conclusion is inferred from the file/draft *descriptions* and the exponent
arithmetic of §3, not from line-by-line verification of:

1. that the cardinal cover + incidence ledger genuinely cover *all* low-energy
   non-dominant profiles (the $T_{\rm aux}$ tiny/uncovered terms of CP 02 §3, and
   the recursive ambient-sensitive FIE entropy);
2. that $|F|\asymp N/D$ with $D$ polylog (so $M=|F|$ is polynomial), making the
   $\ge4$-seed condition applicable;
3. that the seed extraction indeed yields $\ge4$ independent non-reference seeds
   with the cluster geometry of `ClusterLineIncidence.lean`.

## 7. Status and next action

* **Re-scoped (major):** the active correlation endpoint is *likely elementary*
  via the cluster-cover selection (§1–3); FS (notes 11–16) is probably
  unnecessary for it.
* **Next action:** verify §6.1–6.3 against `AdaptiveClusterSelection.lean`,
  `ClusterCoverBookkeeping.lean`, and the FIE entropy accounting
  (`Ambient-sensitive FIE proof draft.md`). Specifically confirm the incidence
  ledger + cardinal cover dominate the *full* non-dominant SBEE level set,
  including tiny/uncovered $T_{\rm aux}$ and the recursive descent. If yes, the
  active arithmetic input is essentially closed elementarily; the residual is the
  FIE entropy bookkeeping, not new analysis.
