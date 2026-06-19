# SBEE Master: Dominant Case Proved, Window Isolated

Back to [[00 README]]. **This document supersedes the scattered SBEE notes as the
mathematical center.** It is self-contained: setup, two theorems **proved in full**
(by direct attack, this session), and the precise isolation of what remains.

Summary of outcomes:

* **Theorem A (dominant case of single-block counting): proved**, elementarily —
  no Irving/Kloosterman input needed.
* **Theorem B (non-dominant forcing): proved** — any non-dominant low-energy
  assignment forces $R\gg X/\log^3X$.
* **Corollary: the SBEE level-set bound holds unconditionally for all
  $R\le c\,X/\log^3X$.** The open core is confined to the thin top window
  $R\in(cX/\log^3X,\ C\varepsilon^{-1}X]$, where the precise difficulty is an
  entropy gap of a polylog factor — exactly the "polylog-ambient compression" the
  FIE drafts identified.

## 1. Setup

Prime block $P\subset[X,2X]$, $|P|=N$, with $N\ge X/(2\log X)$ (the construction's
blocks satisfy this). Assignment $a=(a_p)_{p\in P}$, $a_p\in\mathbb F_p$. For
$p<q$ in $P$, $H_{pq}(a)\in(-pq/2,\,pq/2]$ is the centered CRT representative
($H\equiv a_p\ (p)$, $H\equiv a_q\ (q)$). Energy and deviation:

$$
Q_P(a)=\sum_{p<q}\Big(\frac{H_{pq}(a)}{pq}\Big)^2,\qquad
\sigma_P^2=\sum_{p<q}\frac1{(pq)^2}.
$$

Since $pq\in[X^2,4X^2]$: $\ \tfrac{N(N-1)}{32X^4}\le\sigma_P^2\le\tfrac{N^2}{2X^4}$,
so $\sigma_P\asymp N/X^2$ and $1/\sigma_P\asymp X^2/N\asymp X\log X$.

**Target (single-block counting / SBEE).** For every $\varepsilon>0$ there is
$C_\varepsilon$ with, for all $R\ge1$,
$$
\mathcal N(R):=\#\{a:\ Q_P(a)\le R\}\ \le\ C_\varepsilon\,e^{\varepsilon R}\Big(1+\frac{\sqrt R}{\sigma_P}\Big).
$$

**Sharpness (diagonal).** For an integer $m$, $|m|\le X^2/2$, the assignment
$a\equiv m$ (i.e. $a_p=m\bmod p$) has $H_{pq}=m$ for every pair, so
$Q_P=m^2\sigma_P^2$. Thus all $|m|\le\sqrt R/\sigma_P$ give $Q_P\le R$: the factor
$\sqrt R/\sigma_P$ is exactly the diagonal count. The theorem says the diagonal is
everything, up to $e^{\varepsilon R}$.

**Trivial range.** $\mathcal N(R)\le\prod_p p\le e^{N\log 2X}$, so the bound is
trivial once $R\ge R_{\rm triv}:=\varepsilon^{-1}N\log 2X\asymp\varepsilon^{-1}X$.
Assume throughout $1\le R\le R_{\rm triv}$; for $X\ge X_0(\varepsilon)$ this gives
$R\le X^2/\log^5 X$, which is the only upper restriction the proofs use.

## 2. The deterministic dispersion lemma

The engine of Theorem A. **It is unconditional — no Kloosterman bound is used.**

> **Lemma D.** Let $q\in[X,2X]$ be prime, $w\in\mathbb Z$ with $w\not\equiv0\pmod q$,
> and $U\ge1$ with $U<X$. Then
> $$\#\{(u,p):\ p\in[X,2X]\ \text{prime},\ |u|\le U,\ up\equiv w\ (\mathrm{mod}\ q)\}\ \le\ 2(2U+1).$$

*Proof.* If $u\equiv0\ (q)$ then $w\equiv0$, excluded; since $|u|\le U<X\le q$,
every admissible $u\ne0$ is invertible mod $q$. For each of the $\le 2U+1$ values
of $u$, the congruence pins $p\equiv w\bar u\ (q)$ to one residue class mod $q$;
the interval $[X,2X]$ has length $X\le q$, so it contains at most $2$ integers of
that class. $\square$

## 3. Theorem A: the dominant case

**Definition.** $a$ is *$m$-dominant* (parameter $\rho\in(0,\tfrac14]$) if there is
an integer $m$, $|m|\le X^2/2$, with
$\#\{p\in P:\ a_p\equiv m\ (p)\}\ge(1-\rho)N$. Write $C_m$ for this class and
$E=P\setminus C_m$ (the *exceptions*: $a_q\not\equiv m\ (q)$ for $q\in E$... more
precisely $E:=\{q: a_q\not\equiv m\ (q)\}$, so $|E|\le\rho N$).

**(A1) The dominant label is unique.** If $m\ne m'$ both work, the classes meet in
$\ge(1-2\rho)N\ge N/2$ primes $p$, each dividing $m-m'$; so $|m-m'|\ge X^{N/2}>X^2$
unless $m=m'$. $\square$

**(A2) Label range.** In-class pairs have $H_{pq}=m$ exactly (since
$|m|\le X^2/2\le pq/2$), so $Q_P(a)\ge m^2\sigma_{C_m}^2$ and
$\sigma_{C_m}^2\ge\tfrac{(1-\rho)^2}{24}\,\sigma_P^2$ (compare the pair sums over
$C_m$ and $P$ using $|C_m|\ge(1-\rho)N$ and $pq\asymp X^2$). Hence
$$Q_P(a)\le R\ \Longrightarrow\ |m|\le\frac{5}{1-\rho}\cdot\frac{\sqrt R}{\sigma_P}.$$

**(A3) Each exception carries energy $\ge E_1:=N^3/2^{15}X^2$.**
Fix $q\in E$, set $w:=a_q-m\bmod q\ \not\equiv0$. For $p\in C_m$ consider
$H=H_{pq}$: $H\equiv m\ (p)$, $H\equiv m+w\ (q)$. If $|H|\le\delta pq$, write
$H-m=up$; then $|u|\le\delta q+|m|/p\le 2\delta X+K$ where $K:=|m|/X$, and
$up\equiv w\ (q)$. By Lemma D (with $U=2\delta X+K$; admissible when $U<X$):
$$\#\{p\in C_m:\ |H_{pq}|\le\delta pq\}\ \le\ 2\,(2(2\delta X+K)+1)=8\delta X+4K+2.$$
Choose $\delta:=\min\big(\tfrac18,\ \tfrac{N}{128X}\big)$. Using (A2) and
$\sigma_P\ge N/(8X^2)$: $K\le 8\cdot\tfrac{5}{1-\rho}\sqrt R\,X/N\le N/32$ provided
$R\le c_1(\rho)\,X^2/\log^4X$ — true in our range. Then
$8\delta X+4K+2\le N/16+N/8+2\le N/4$, so at least $|C_m|-N/4\ge N/2$ pairs
$(p,q)$, $p\in C_m$, have $(H_{pq}/pq)^2>\delta^2$, giving this exception vertex
cross-energy $\ge\delta^2N/2\ge N^3/2^{15}X^2=E_1$.

Distinct exceptions use disjoint pair sets, so $Q_P(a)\le R$ forces
$$|E|\ \le\ R/E_1\ =\ 2^{15}RX^2/N^3.$$

**(A4) The count.** An $m$-dominant assignment is determined by: the label $m$
($\le 1+\tfrac{10}{1-\rho}\sqrt R/\sigma_P$ choices by (A1)–(A2)); the exception
set $E$ and its residues ($\le\binom{N}{e}(2X)^e\le e^{3e\log X}$ for $|E|=e$).
By (A3), $e\le 2^{15}RX^2/N^3$, so the exception entropy is
$$3e\log X\ \le\ 3\cdot2^{15}\,\frac{X^2\log X}{N^3}\,R\ \le\ \frac{C\log^4X}{X}\,R\ \le\ \varepsilon R
\qquad(X\ge X_0(\varepsilon)).$$

> **Theorem A.** For every $\varepsilon>0$, $\rho\in(0,\tfrac14]$ and
> $X\ge X_0(\varepsilon,\rho)$: for all $R\ge1$,
> $$\#\{a:\ Q_P(a)\le R,\ a\ \text{dominant}\}\ \le\ e^{\varepsilon R}\Big(1+\frac{10}{1-\rho}\cdot\frac{\sqrt R}{\sigma_P}\Big).$$

*Proof.* Combine (A1)–(A4) for $R\le R_{\rm triv}$; above $R_{\rm triv}$ the
trivial bound is $\le e^{\varepsilon R}$. $\blacksquare$

**Remark.** No Irving input. The dispersion needed in the dominant case is
Lemma D — deterministic. This removes the Irving dependence from this case
entirely (CP 03 had routed it through Irving-good pruning).

## 4. The covering construction (base point and short list)

Let $Q_P(a)\le R$ and $B:=A\sqrt R\,X^2/N$ ($A\ge1$ a parameter). Pairs with
$|H_{pq}|>B$ contribute $>B^2/(4X^2)^2$ each, so
$\#\{pq:\ |H_{pq}|>B\}\le 16RX^4/B^2$. Averaging over base points:
$$\sum_{p_0\in P}\#\{q:\ |H_{p_0q}|>B\}=2\,\#\{\text{pairs}:\ |H|>B\}\le 32RX^4/B^2,$$
so some $p_0$ has $\#\{q:|H_{p_0q}|>B\}\le 32RX^4/(B^2N)=32N/A^2$. Define the
**short list** $\mathcal L:=\{n\in[-B,B]:\ n\equiv a_{p_0}\ (p_0)\}$,
$|\mathcal L|\le 2B/X+1$. Every $q$ with $|H_{p_0q}|\le B$ satisfies
$a_q\equiv n_q\ (q)$ for $n_q:=H_{p_0q}\in\mathcal L$. The **classes**
$C_n:=\{q:\ n_q=n\}$, $n\in\mathcal L$, are disjoint and cover all but
$\le 32N/A^2+1$ vertices. Note $B\le X^2/2$ in our $R$-range, so every label
satisfies $|n|\le X^2/2$.

## 5. The cross-label energy lemma

> **Lemma E.** Let $n\ne n'$ be integers, $|n|,|n'|\le B\le X^2/4$, and let
> $C\subseteq\{p:\ a_p\equiv n\ (p)\}$, $C'\subseteq\{q:\ a_q\equiv n'\ (q)\}$ be
> disjoint sets of primes in $[X,2X]$ with $|C|\ge 32(B/X+1)$ and $|C'|\ge8$. Then
> $$\sum_{p\in C,\,q\in C'}\Big(\frac{H_{pq}}{pq}\Big)^2\ \ge\ c\,\frac{|C|^3|C'|}{X^2},\qquad c>0\ \text{absolute}.$$

*Proof.* Put $d=n'-n\ne0$, $0<|d|\le2B$. For a cross pair, $H\equiv n\ (p)$,
$H\equiv n'\ (q)$; if $|H|\le\delta pq$, write $H-n=up$: $|u|\le2\delta X+B/X$ and,
mod $q$: $up\equiv d\ (q)$. At most $2$ primes $q\ge X$ divide $d$
($|d|\le2B\le X^2/2<X^3$); discard them (≤ $2|C|$ pairs). For the remaining
$q\in C'$, Lemma D (with $w=d$, $U=2\delta X+B/X$) gives
$\#\{p:\ |H_{pq}|\le\delta pq\}\le 8\delta X+4B/X+2$. Hence
$$\#\{(p,q):\ |H_{pq}|\le\delta pq\}\ \le\ 2|C|+|C'|\,(8\delta X+4B/X+2).$$
Choose $\delta=\min(\tfrac14,\,|C|/(64X))$. Then $8\delta X|C'|\le|C||C'|/8$, and
$|C'|(4B/X+2)\le|C||C'|/8$ (by $|C|\ge32(B/X+1)$), and $2|C|\le|C||C'|/4$ (by
$|C'|\ge8$). So at least $|C||C'|/2$ cross pairs have $(H/pq)^2>\delta^2$, giving
energy $\ge\delta^2|C||C'|/2\ge c|C|^3|C'|/X^2$ (as $|C|\le X$). $\square$

## 6. Theorem B: non-dominant forcing

> **Theorem B.** Let $\rho\in(0,\tfrac14]$, $A^2\ge128/\rho$. There are
> $c_2(\rho,A)>0$ and $X_0$ such that for $X\ge X_0$: if $Q_P(a)\le R$ and $a$ is
> **not** dominant (no $m$ as in §3), then
> $$R\ \ge\ c_2\,\frac{N^2}{X\log X}\ \ge\ c_2'\,\frac{X}{\log^3X}\ =:\ R_w.$$

*Proof.* Suppose $R<R_w$ with $c_2$ to be chosen. Run §4: classes
$\{C_n\}_{n\in\mathcal L}$, $k_0:=|\mathcal L|\le 2B/X+1\le 3A\sqrt R\log X$
(using $B/X=A\sqrt R\,X/N\le 2A\sqrt R\log X$ — wait, $X/N\le2\log X$ ✓).
Call $C_n$ *substantial* if $|C_n|\ge s_0:=32(B/X+1)+8$. Mass in tiny classes is
$\le k_0s_0\le C_3A^2R\log^2X\le\rho N/8$ once $R\le\rho N/(8C_3A^2\log^2X)$ —
implied by $R<R_w$ with $c_2$ small. Mass accounting: covered mass
$\ge N-32N/A^2-1$; no class exceeds $(1-\rho)N$ (else $a$ is dominant — labels
satisfy $|n|\le X^2/2$ by §4); let $C^*$ be the largest substantial class and
$M_2$ the substantial mass outside $C^*$:
$$M_2\ \ge\ N\Big(1-\tfrac{32}{A^2}-\tfrac\rho8-(1-\rho)\Big)-1\ \ge\ \tfrac{\rho N}{2}.$$
Cross-pair sets of distinct class pairs are disjoint, so Lemma E gives, summing:
* if some non-$C^*$ substantial class has size $\ge M_2/2$, pair it with $C^*$
  ($|C^*|\ge M_2/2$ as the largest): $Q_P\ge c(M_2/2)^4/X^2$;
* otherwise all non-$C^*$ classes are $\le M_2/2$ and, with $\Sigma:=$ their sizes,
  $\sum_{C\ne C'}|C|^3|C'|\ge(\sum|C|^3)\cdot M_2-\max|C|\sum|C|^3
  \ge\tfrac{M_2}{2}\cdot\tfrac{M_2^3}{k_0^2}$, so $Q_P\ge cM_2^4/(2k_0^2X^2)$.

Either way $R\ge Q_P\ge c\,(\rho N/2)^4/(k_0^2X^2)
\ge c_4\rho^4N^4/(A^2R\log^2X\cdot X^2)$, i.e.
$R^2\ge c_4\rho^4N^4/(A^2X^2\log^2X)$, i.e.
$R\ge c_5\rho^2N^2/(AX\log X)$. Choosing $c_2<c_5\rho^2/A$ contradicts $R<R_w$.
$\blacksquare$

## 7. Corollary: SBEE holds below the window

> **Corollary.** For every $\varepsilon>0$ there are $c',X_0$ such that for
> $X\ge X_0$ and **all** $R\le c'X/\log^3X$:
> $$\mathcal N(R)\ \le\ e^{\varepsilon R}\Big(1+\frac{20\sqrt R}{\sigma_P}\Big).$$

*Proof.* By Theorem B every $Q_P\le R$ assignment in this range is dominant; apply
Theorem A. $\blacksquare$

This is, to my knowledge, the first complete unconditional proof of the
single-block counting bound in any nontrivial range. It covers all
$R\le X/\log^3X$; the needed range is $R\le\varepsilon^{-1}N\log 2X\asymp X$.

## 8. The open window, precisely

What remains of SBEE is exactly:

> **Window problem.** For $R\in(c'X/\log^3X,\ C\varepsilon^{-1}X]$, show
> $$\#\{a:\ Q_P(a)\le R,\ a\ \text{non-dominant}\}\ \le\ e^{\varepsilon R}.$$

Structure of a non-dominant window assignment (by §4–§6): $\ge2$ substantial
classes; by Lemma E any two substantial classes of sizes $K,K'$ satisfy
$cK^3K'/X^2\le R$, so all-but-one have size $\le K_R\asymp(RX^2)^{1/4}$; the number
of classes can be as large as $k\asymp\sqrt R\,\log X\asymp\sqrt X$.

**The entropy gap (why this is the real core).** Encoding such an assignment costs
$\approx N\log k$ bits for the vertex→class map (everything else is cheaper). With
$k\asymp\sqrt X$: $N\log k\asymp X/2$. The budget is $\varepsilon R\le\varepsilon
C X$ — comparable at the very top, but **at the window floor $R\asymp X/\log^3X$
the budget is $\varepsilon X/\log^3X$, short by $\log^4 X$-ish.** Meanwhile the
*cheap* energy lower bound (Lemma E, equal spread) for a $k$-class configuration
is only $\asymp M^4/(k^2X^2)$, which at $k\asymp\sqrt X$ is $\asymp X/\log^4X\le
R$. So cheap energy does **not** contradict spread configurations, and cheap
entropy does not afford them: the gap is a polylog factor. This is precisely the
"polylog-ambient compression" bottleneck the FIE drafts isolated — my derivation
confirms it quantitatively and locates it as the **whole** of what remains.

**What must be true (the inverse problem).** A spread configuration needs, for
*every* pair of its classes $(n,n')$, *most* cross pairs $(p,q)$ to satisfy
$\|(n'-n)\bar p/q\|\lesssim\delta$ — a massive system of simultaneous reciprocal
conspiracies. Lemma D says each single $(d,q)$ constraint confines $p$ to
$\approx\delta X$ residue classes; the believed rigidity is that these systems
have no common solution of positive density unless the classes merge (dominant) or
the labels/classes carry low-entropy arithmetic structure — *the same
reciprocal-cluster rigidity* as [[09 Cluster Concentration and the Structured Family]]
and [[22 The Real Gap, Atomic Form]]/[[23 Proof of the Reciprocal-Cluster Selection Lemma]],
now at the block level. The formalized cluster-selection machinery
(`good_kSubset_exists_unconditional`) is the right tool family for exactly this
counting; what is new in the window is the *recursive entropy accounting* (FIE's
first-capture tree).

## 9. Honest status

* **Proved here, in full, elementarily:** Lemma D, Theorem A (dominant case — no
  Irving), Lemma E, Theorem B (forcing), Corollary (SBEE for all
  $R\le c'X/\log^3X$).
* **Open:** the window problem of §8 — the genuine research core. It is *one*
  counting statement, in a polylog-thin range of $R$, with a precise entropy
  deficit of $\mathrm{polylog}(X)$ to close via reciprocal-conspiracy rigidity.
* These results supersede my earlier hand-wavy assessments: previous claims of
  "essentially proved" are replaced by actual theorems where I could prove them,
  and by an exact statement of what nobody has yet proved where I could not.

## 10. Next

Attack the window problem: (i) try to upgrade Lemma E to a *multi-class* energy
bound exploiting simultaneity (the same $p$ appears in constraints against many
classes — the conspiracies interact); (ii) use the cluster machinery to bound the
number of label systems admitting dense conspiracies; (iii) the FIE first-capture
tree as entropy bookkeeping. Each is a concrete, falsifiable step on a single
well-posed problem.
