# What SBEE Actually Needs (Synthesis)

Back to [[00 README]]. Reading the archived `CP 02 The single remaining condition`
(`../archive/conditional proof/`) pins down what strength the correlation bound
must have, and reconnects it to the analytic work of notes 07–17.

## 1. CP 02 wants a per-(non-structured)-tuple dichotomy, not an average

CP 02 states the endpoint as: for **non-structured** seeds
$q_\ast,q_1,q_2,q_3,q_4\sim X$,
$$
\sum_{p\sim X}A_{04}(p)B_{123}(p)\ll(\log X)^C\Big(1+\tfrac{H^6}{X^3}\Big),
\qquad\text{or else the tuple is in a low-entropy structured family.}
$$
So the structure is a **per-tuple dichotomy**: regular bound *or* structured.
This refines [[13 The Averaged Framing Is Essential]] — it is not "average over
all seeds," but "holds for each non-structured tuple, with structured tuples
handled separately."

## 2. The structured side is power-thin — elementarily (CP 02 §3.1)

CP 02 (the kernel count, its lines ~355–372) bounds the singular/structured seed
tuples directly: a short homogeneous kernel forces $q_i\equiv q_\ast x_\ast
x_i^{-1}\pmod p$, giving $O(M_\tau)$ choices per seed coordinate, hence singular
tuples number
$$
\ll N^2 M_\tau^{k+1}(\log X)^{O(1)}\quad\text{vs. free } N^{k+1}.
$$
With $k=4$, $M_\tau\asymp X^{1/2}$, $N\asymp X$: $\ll X^{9/2}$ vs $X^5$ — a
**power saving $X^{-1/2}$**. So the structured family is **power-thin by an
elementary count**; no FS/Kloosterman needed for the structured side. (This is
[[09 Cluster Concentration and the Structured Family]]'s family, now counted.)

## 3. The regular side reduces to bounding $|P_B|$ — an equidistribution statement

CP 02 (its lines ~339–342): for non-structured seeds (no short kernel), **two
witnesses for the same $p$ would force a short kernel**, so each $p$ has at most
one witness, i.e. $B_{123}(p)\le1$. Hence
$$
N_H'=\sum_pA_{04}(p)B_{123}(p)\le\sum_{p\in P_B}A_{04}(p),\qquad P_B=\{p\sim X:B_{123}(p)\ge1\}.
$$
With $A_{04}(p)\ll(\log X)^C$ for non-structured anchor (anchor analogue of
[[09 Cluster Concentration and the Structured Family]] Lemma B), the regular
bound reduces to
$$
\boxed{\ |P_B|=\#\{p\sim X: B_{123}(p)\ge1\}\ \ll\ (\log X)^C\ \text{ for non-structured seeds.}\ }
$$
Now $|P_B|\le\#\{(x_4,\vec a)\ \text{short pinning an in-range prime}\}$: each
witness pins $p$ to one class mod $q_1q_2q_3\asymp X^3$. The **expected** size is
$(2H)^4\cdot X/X^3\asymp H^4/X^2\ll(\log X)^{O(1)}$, but realizing this per tuple
is exactly the statement that the **reachable reciprocal-image residues
equidistribute mod $q_1q_2q_3$** (do not concentrate in $[X,2X]$). That is a
genuine **Kloosterman/equidistribution** statement — the place where FS-type
input (notes 11–16) is actually needed, if a per-tuple bound is required.

## 4. The pivotal sub-question: per-tuple, or does first-moment suffice?

[[17 The First Moment Is Trivial (Correction)]] proved the first moment over
cluster seeds is trivially in budget, giving (Markov) the regular bound for all
but a **$(\log X)^{-D}$-thin** set of tuples. Whether that suffices depends on the
**seed-pool size** in the FIE/DRC good-seed selection (CP 02's "good-seed
selection lemma"):

* **If the fingerprint pool is large ($\gg(\log X)^{D}$):** a log-thin exceptional
  set is fine — selection finds a good tuple. Then **note 17 + the elementary
  structured count (§2) close the regular bound, with no FS needed.**
* **If the pool is small ($O((\log X)^{O(1)})$):** log-thin is not enough; we need
  the per-tuple equidistribution bound on $|P_B|$ (§3), i.e. **FS/Kloosterman is
  required**.

This is now the single decisive question, and it lives in the FIE/DRC bucket
bookkeeping (the archived bucket/fingerprint lemmas, `output-final_aristotle_2`
`Bucket*.lean`), not in the analysis.

## 5. Honest reassessment of the analytic arc (notes 11–16)

* The **first moment is trivial** (note 17) — notes 15–16's cube/stratification is
  unnecessary for it.
* The **structured family is power-thin elementarily** (§2, from CP 02) — notes
  09–10's "structured family" is controlled without FS.
* FS (notes 11–16) is needed **only** for the per-tuple equidistribution of
  $|P_B|$ (§3), and **only if** the FIE pool is small (§4).

So the genuine status is better than notes 11–16 implied: the analytic
heavy-machinery may be **avoidable** depending on a bookkeeping parameter. The
FS apparatus is the fallback, not certainly required.

## 6. Next action

Determine the **fingerprint/DRC pool size** in the SBEE good-seed selection:
read the archived bucket machinery
(`../archive/Aristotle/output-final_aristotle_2/RequestProject/Bucket*.lean`,
`Insights.md`, and `SBEE dyadic proof draft.md`) to find how many candidate seed
tuples the selection draws from. This decides §4 — i.e. whether the project's
last arithmetic input is already met (notes 17 + §2) or genuinely needs FS
(§3 + notes 11–16).
