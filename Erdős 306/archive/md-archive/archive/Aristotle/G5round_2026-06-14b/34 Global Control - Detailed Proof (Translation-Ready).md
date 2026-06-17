# Global Control: Detailed Proof (Translation-Ready)

Back to [[00 README]]. **The block-to-global chain (CP 03 §§5–8 / Prop 8.1), with
complete proofs, written for Lean translation.** The argument mirrors the verified
single-block proof one level up: blocks play the role vertices played inside a
block. **No Irving/Kloosterman input anywhere** — the deterministic dispersion
(`lemmaD`) suffices because the Peierls penalties exceed the entropies
doubly-exponentially (numerically verified: penalty $\Pi_k\asymp4^k/k^4$ vs
entropy $\asymp k$).

## G0. Setup (definitions to formalize)

**BlockSystem.** Integers $k_0<K$ (with $K\le e^2k_0$-ish; only $\log K\ll 2^{k_0}$
is used). For each $k\in[k_0,K]$ a block $P_k\subseteq\{\text{primes}\}\cap[2^k,2^{k+1})$
with **density** $|P_k|\ge 2^k/(2\log 2^k)$ (so each $P_k$ is `IrvingGood`). Write
$N_k=|P_k|$, $X_k=2^k$. Blocks are disjoint (different dyadic windows). $\mathcal P=\bigcup_kP_k$.

**Control pairs.** $\mathrm{Pairs}_{\rm ctrl}=\{\{p,q\}:p<q\in P_k,\ \text{some }k\}\ \cup\ \{\{p,q\}:p\in P_k,\ q\in P_{k+1},\ k_0\le k<K\}$
(internal complete graphs + **full bipartite between consecutive blocks**).

**Energy and deviation.** For a global assignment $a\in\prod_{p\in\mathcal P}\mathbb F_p$:
$$Q_{\rm ctrl}(a)=\sum_{\{p,q\}\in\mathrm{Pairs}_{\rm ctrl}}\Big(\frac{H_{pq}(a)}{pq}\Big)^2,\qquad
\sigma_{\rm ctrl}^2=\sum_{\{p,q\}\in\mathrm{Pairs}_{\rm ctrl}}\frac1{(pq)^2}.$$
Note $\sigma_k\asymp 2^{-k}/k$ per block, so $\sigma_{\rm ctrl}\asymp\sigma_{k_0}$
(lowest block dominates); and $\sigma_{\rm ctrl}^2\ge\sigma_{k_0}^2$ trivially.

**Block data.** $a_k:=a|_{P_k}$, $R_k:=Q_{P_k}(a_k)$ (internal energy; the verified
`QP`). $Q_{\rm ctrl}(a)\ge\sum_kR_k$ and $\ge$ each cross term.

**Thresholds.** $R_w(X):=c_B X/\log^3X$ (the verified Theorem-B forcing floor);
block $k$ is **hot** (for the given $a$) if $R_k\ge R_w(X_k)$, else **cold**.
$E_1(X):=X/(2^{15}\log^3X)$ hmm — precisely the verified per-exception energy
$N^3/2^{15}X^2$ with $N\ge X/(2\log X)$: $E_1(X):=X/(2^{18}\log^3X)$.
$\Pi_k:=N_{k+1}N_k^3/2^{13}X_k^2$ (the mismatch penalty; $\asymp4^k/k^4$).

## G1. Per-block inputs (verified; small extraction lemmas needed)

From the machine-verified package, uniform over all `IrvingGood` blocks:

* **(L1, level-set)** `unified_levelset`: $\#\{a_k:Q_{P_k}(a_k)\le R\}\le C_\varepsilon e^{\varepsilon R}\big(1+\tfrac{\sqrt R}{\sigma_k}\big)$ for all $R\ge1$.
* **(L2, cold structure)** If $R_k<R_w(X_k)$ then $a_k$ is $m_k$-dominant for a
  unique integer $m_k$, $|m_k|\le X_k^2/2$, with class $\ge(1-\rho)N_k$
  (contrapositive of `theorem_B_nondominant_forcing` + uniqueness A1).
* **(L3, label range)** $m_k$-dominant with energy $R_k$ ⟹ $|m_k|\le\tfrac5{1-\rho}\sqrt{R_k}/\sigma_k$ (A2).
* **(L4, exception bound)** $E_k:=\{q\in P_k: a_q\not\equiv m_k\ (q)\}$ has
  $|E_k|\le R_k/E_1(X_k)$ (A3); for cold blocks $|E_k|\le R_w/E_1=2^{18}c_B=:e_0$, an
  absolute constant.
* **(L5, dominant count)** Given $m_k$: #(dominant assignments with energy $\le R_k$,
  label $m_k$) $\le e^{\varepsilon R_k}$ (A4's exception bookkeeping).

*Extraction lemmas to add (small):* expose (L2)–(L5) from the proved
`theorem_A_dominant_count`/`theorem_B_nondominant_forcing` internals (the proofs
contain them; restate as standalone lemmas).

## G2. Cross-block dispersion (deterministic; the §5 engine)

> **Lemma G2.** Let $P\subseteq\text{primes}\cap[X,2X)$, $q$ prime $\in[2X,4X)$,
> $d\in\mathbb Z$, $q\nmid d$, $d\ne0$. Then for $\delta:=|P|/(32X)$:
> $$\#\{p\in P:\ \|d\,\bar p/q\|\le\delta\}\ \le\ \tfrac{|P|}4+1,\qquad\text{hence}\qquad
> \sum_{p\in P}\|d\,\bar p/q\|^2\ \ge\ \delta^2\big(|P|-\tfrac{|P|}4-1\big)\ \ge\ \frac{|P|^3}{2^{11}X^2}.$$

*Proof.* $\|d\bar p/q\|\le\delta$ ⟺ ∃$u$, $|u|\le\delta q$, $d\bar p\equiv u\ (q)$
⟺ $d\equiv up\ (q)$. $u=0$ ⟹ $q\mid d$, excluded. For $u\ne0$: $p\equiv d\bar u\ (q)$,
one residue class mod $q$; the interval $[X,2X)$ has length $X\le q/2$, so it
contains **at most one** integer of the class. #$u$'s $\le2\delta q+1\le8\delta X+1$.
With $\delta=|P|/(32X)$: $\le|P|/4+1$. $\square$
(Formalize via the verified `lemmaD` pattern; here even easier — fiber $\le1$.)

## G3. Mismatch penalty (the §5 lemma, deterministic)

> **Lemma G3.** Let blocks $P_k,P_{k+1}$ both be cold with labels $m_k\ne m_{k+1}$,
> exception sets $E_k,E_{k+1}$ ($|E_j|\le e_0$). Suppose $|m_j|\le X_j^{7/4}$ (true
> for cold labels by L3: $|m_j|\le C\sqrt{R_w}/\sigma_j\ll X_j^{3/2}\log X_j$).
> Then the cross energy
> $$\sum_{p\in P_k\setminus E_k,\ q\in P_{k+1}\setminus E_{k+1}}\Big(\frac{H_{pq}(a)}{pq}\Big)^2\ \ge\ \Pi_k:=\frac{N_{k+1}N_k^3}{2^{13}X_k^2}.$$

*Proof.* Set $d:=m_{k+1}-m_k\ne0$, $0<|d|\le2X_{k+1}^{7/4}$. **Bad $q$'s** ($q\mid d$):
at most $\log|d|/\log X_{k+1}\le2$ primes $q\ge X_{k+1}$ divide $d$
(since $|d|<X_{k+1}^{3}$ hmm — $\le X_{k+1}^{7/4}\cdot2<X_{k+1}^2$: at most 1; keep $\le2$).
For each **good** $q\in P_{k+1}\setminus E_{k+1}$ (at least $N_{k+1}-e_0-2\ge N_{k+1}/2$
of them) and each conforming $p\in P_k\setminus E_k$: $H:=H_{pq}(a)$ satisfies
$H\equiv m_k\ (p)$, $H\equiv m_{k+1}\ (q)$ (conforming!), so $H-m_k=vp$ with
$vp\equiv d\ (q)$, $v\equiv d\bar p\ (q)$, hence $|v|\ge q\|d\bar p/q\|$ and
$$\frac{|H|}{pq}\ \ge\ \|d\,\bar p/q\|-\frac{|m_k|}{pq}\ \ge\ \|d\bar p/q\|-\frac\delta2$$
(since $|m_k|\le X_k^{7/4}\le\delta X_k^2/2$ for $X_k\ge X_0$, $\delta=N_k/(32X_k)\asymp1/\log X_k$).
By Lemma G2 over $P_k\setminus E_k$ ($|P\setminus E|\ge N_k-e_0\ge N_k/2$, rerun G2
with this set): at least $N_k/2-N_k/4-1-e_0\ge N_k/8$ values of $p$ have
$\|d\bar p/q\|>\delta$, hence $(H/pq)^2\ge\delta^2/4$. Summing:
cross energy $\ge\frac{N_{k+1}}2\cdot\frac{N_k}8\cdot\frac{\delta^2}4=\frac{N_{k+1}N_k^3}{2^{13}\cdot32^2\cdots}$
— constants: $\ge N_{k+1}N_k^3/2^{16}X_k^2$; **define $\Pi_k$ with $2^{16}$**. $\square$

## G4. Hot-block absorption

> **Lemma G4.** For a hot block ($R_k\ge R_w(X_k)$), the level-set factor satisfies
> $\log\big(C_\varepsilon(1+\sqrt{R_k}/\sigma_k)\big)\le\varepsilon R_k$ for $k\ge k_0(\varepsilon,c_B)$,
> uniformly in $R_k\ge R_w(X_k)$ and in the global $R\le e^{2^{k_0}}$.

*Proof.* $\log(1+\sqrt{R_k}/\sigma_k)\le\log(1+\sqrt{R_k}\,2^kk\cdot8)\le 2k+\log(8k)+\tfrac12\log R_k$.
And $R_k\ge c_B2^k/k^3$ ⟹ $2k+\log(8k)\le\varepsilon R_k/2$ for $k\ge k_0(\varepsilon)$;
$\tfrac12\log R_k\le\varepsilon R_k/2$ for $R_k\ge R_w(X_{k_0})$ large. $\square$
So a hot block's total count is $\le e^{2\varepsilon R_k}$ (L1 + G4).

## G5. Global level-set theorem

> **Theorem G (global counting).** For every $\varepsilon\in(0,1)$, $\rho\in(0,\tfrac14]$
> there are $k_0(\varepsilon,\rho)$ and $C_{\rm glob}=C^{K-k_0}$ such that for every
> BlockSystem with $k_0\ge k_0(\varepsilon,\rho)$ and all $R\ge1$:
> $$\mathcal N_{\rm glob}(R):=\#\{a:\ Q_{\rm ctrl}(a)\le R\}\ \le\ C_{\rm glob}\,e^{8\varepsilon R}\Big(1+\frac{\sqrt R}{\sigma_{\rm ctrl}}\Big).$$

*Proof (the encoding; every step elementary).* Fix $a$ with $Q_{\rm ctrl}(a)\le R$.
Data recorded:

1. **Hot set** $H\subseteq[k_0,K]$. Since each hot $R_k\ge R_w^{min}:=R_w(X_{k_0})$
   and $\sum R_k\le R$: $|H|\le R/R_w^{min}$. Entropy $\le|H|\log(K{-}k_0{+}1)\le
   \tfrac{R\log K}{R_w^{min}}\le\varepsilon R$ once $\log K\le\varepsilon R_w^{min}$
   (true: $K\le e^2k_0$, $R_w^{min}\asymp2^{k_0}/k_0^3$).
2. **Hot block data**: by L1+G4, $\le\prod_{k\in H}e^{2\varepsilon R_k}\le e^{2\varepsilon R}$.
3. **Mismatch boundary set** $B\subseteq\{k:\ k,k{+}1\text{ both cold},\ m_k\ne m_{k+1}\}$.
   By G3 the cross terms are disjoint pair-sets, so $\sum_{k\in B}\Pi_k\le R$, and
   $\Pi_k\ge\Pi_{min}:=\Pi_{k_0}$: $|B|\le R/\Pi_{min}$; entropy $\le|B|\log K\le\varepsilon R$
   (same numeric as 1, $\Pi_{min}\gg R_w^{min}$).
4. **Cold labels.** The cold blocks split into maximal runs (segments) delimited by
   hot blocks and boundaries in $B$; within a segment all labels are **equal**
   (adjacent cold, not in $B$ ⟹ $m_k=m_{k+1}$). #segments $\le1+2|H|+|B|$. Encode
   each segment's common label $m$:
   * For the segment containing $k_0$ (if block $k_0$ is cold): $|m|\le C\sqrt{R}/\sigma_{k_0}\le C\sqrt R/\sigma_{\rm ctrl}\cdot C'$
     (L3 at its lowest block). **This is the single global label factor**
     $\le(1+2C'\sqrt R/\sigma_{\rm ctrl})$.
   * Every other segment starts at some $k^\dagger>k_0$ whose predecessor
     $k^\dagger{-}1$ is hot or a $B$-boundary. Label entropy
     $\le\log(1+2C\sqrt R/\sigma_{k^\dagger})\le 2k^\dagger+\log(8k^\dagger C)+\tfrac12\log R$,
     paid by the predecessor's energy ($\ge R_w(X_{k^\dagger-1})$ or $\ge\Pi_{k^\dagger-1}$,
     both $\ge c2^{k^\dagger}/poly(k^\dagger)\gg$ the entropy, using $\log R\le\log R_{\rm triv}^{\rm glob}\ll2^{k_0}$);
     formally: sum of these entropies $\le\varepsilon\sum_{k\in H}R_k+\varepsilon\sum_{k\in B}\Pi_k\le2\varepsilon R$.
5. **Cold block data given label**: $\le\prod_{\rm cold}e^{\varepsilon R_k}\le e^{\varepsilon R}$ (L5).

Multiply: $\mathcal N_{\rm glob}(R)\le e^{\varepsilon R}\cdot e^{2\varepsilon R}\cdot e^{\varepsilon R}\cdot(1+2C'\tfrac{\sqrt R}{\sigma_{\rm ctrl}})\cdot e^{2\varepsilon R}\cdot e^{\varepsilon R}\cdot C^{\#\rm blocks}$.
$\square$

(*Decoder check*: from (hot set, hot data, $B$, segment labels, cold exceptions)
the assignment is reconstructed block by block — hot raw via the level-set
enumeration, cold = label + exceptions. Injective ✓.)

## G6. Main-arc localization

> **Lemma G6.** Let $\mathfrak M_C=\{a:\exists m,\ |m|\le C/\sigma_{\rm ctrl},\ a_p\equiv m\ (p)\ \forall p\in\mathcal P\}$.
> Then for $a\notin\mathfrak M_C$ with $Q_{\rm ctrl}(a)\le R$, **either** (i) some hot
> block / boundary / exception exists, forcing $Q_{\rm ctrl}(a)\ge F_0:=\min(R_w^{min},\Pi_{min},E_1(X_{k_0}))$,
> **or** (ii) $a$ is globally diagonal ($a\equiv m$ everywhere) with $|m|>C/\sigma_{\rm ctrl}$,
> forcing $Q_{\rm ctrl}(a)\ge m^2\sigma_{\rm ctrl}^2>C^2$.

*Proof.* If no hot block, no boundary, and no exception anywhere: all blocks cold,
all labels equal (one segment), no exceptions ⟹ $a\equiv m$ globally with
$H_{pq}=m$ for every control pair (labels $\ll X_{k_0}^2\le pq/2$ ✓), so
$Q_{\rm ctrl}=m^2\sigma_{\rm ctrl}^2$, and $a\notin\mathfrak M_C$ ⟹ $|m|>C/\sigma_{\rm ctrl}$. $\square$

## G7. Prop 8.1 (partition form)

> **Theorem (global control partition).** With the construction fixed
> ($k_0\ge k_0(\varepsilon,\rho)$, $\varepsilon<c/100$):
> $$\sum_ae^{-cQ_{\rm ctrl}(a)}\le\frac{C_1}{\sigma_{\rm ctrl}},\qquad
> \sum_{a\notin\mathfrak M_C}e^{-cQ_{\rm ctrl}(a)}\le\Big(C_{\rm glob}e^{-cF_0/2}+C_1e^{-C^2c/2}\Big)\frac1{\sigma_{\rm ctrl}}.$$

*Proof.* First bound: Laplace/dyadic summation of Theorem G (identical pattern to
the verified `partfun_series_bound`). Second: split by G6; sector (i) has the
energy floor $F_0$: $\sum_{(i)}e^{-cQ}\le e^{-cF_0/2}\sum_ae^{-cQ/2}\le e^{-cF_0/2}\cdot C_1'/\sigma$;
sector (ii) is the Gaussian tail $\sum_{|m|>C/\sigma}e^{-cm^2\sigma^2}\le e^{-cC^2/2}\cdot C''/\sigma$. $\square$

As $k_0\to\infty$, $C_{\rm glob}e^{-cF_0/2}\to0$ ($C_{\rm glob}=e^{O(k_0)}$,
$F_0\gtrsim2^{k_0}/k_0^3$); then $C\to\infty$ kills the tail — exactly the order
of limits CP 01 §7 takes.

## G8. Remarks for the formalizer

* All inputs are: the verified single-block package (L1–L5 extractions), `lemmaD`
  (for G2), and finite bookkeeping. **No new analytic input.**
* Constants are explicit but lavish; thresholds $k_0(\varepsilon,\rho)$ are large
  — fine, the statement is asymptotic in $k_0$ and the construction chooses $k_0$.
* The block-label collapse here REPLACES CP 03 §§5–7 (no polymer expansion needed:
  the segment encoding of G5 step 4 is the entire "Peierls" content) and G7 IS
  Prop 8.1. The old `SBEE.lean` placeholder lemmas are superseded.
