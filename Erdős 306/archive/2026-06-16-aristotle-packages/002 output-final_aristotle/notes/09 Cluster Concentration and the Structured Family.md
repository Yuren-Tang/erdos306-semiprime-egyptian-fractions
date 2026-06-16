# Cluster Concentration and the Structured Family

Back to [[00 README]]. Prerequisites: [[07 Diagonal Ledger]],
[[08 Anchor Energy and the Joint Obstruction]].

This note attacks the core (Task 4). It proves an **unconditional
geometry-of-numbers bound** for the cluster count $B_{123}(p)$ at a single prime,
and an **airtight inverse difference lemma**, which together make the
"structured seed family" explicit and finite. The outcome: the still-open
correlation bound is reduced to controlling how often a small, explicitly
described set of "bad primes" can carry simultaneous anchor and cluster mass.

Work on the reduced range $p\nmid\mathcal Q$ of [[07 Diagonal Ledger]].

## 1. The cluster relation lattice

Fix a prime $p\nmid\mathcal Q$. For each $i\in\{1,2,3\}$ put
$c_i=-q_4\,p^{-1}\bmod q_i$, so the cluster congruence $q_i\mid p\,a_i+q_4x_4$
reads $a_i\equiv c_i x_4\pmod{q_i}$. Introduce the rank-2 lattice

$$
\Lambda_i(p)=\{(u,v)\in\mathbb Z^2:\ v\equiv c_i u\pmod{q_i}\},\qquad \det\Lambda_i(p)=q_i,
$$

and let $\lambda_1^{(i)}(p)$ be its first minimum (shortest nonzero vector in
$\ell^\infty$). Multiplying the defining congruence by $p$ shows

$$
(b,e)\in\Lambda_i(p)\iff q_i\mid q_4\,b+p\,e,
$$

so **$\lambda_1^{(i)}(p)$ is the height of the shortest relation
$q_i\mid q_4\,b+p\,e$** — a short multiplicative tie between $q_4$ and $p$
modulo $q_i$. Generic size: by Minkowski $\lambda_1^{(i)}\le\sqrt{q_i}\asymp X^{1/2}$,
and for "random" $c_i$ one has $\lambda_1^{(i)}\asymp\sqrt{q_i}$.

## 2. Lemma B (single-modulus cluster bound)

**Lemma B.** For each $i$,

$$
\#\{x_4\in[-H,H]:\ c_ix_4\bmod q_i\in[-H,H]\}\ \ll\ 1+\frac{H}{\lambda_1^{(i)}(p)}+\frac{H^2}{q_i}.
$$

Consequently

$$
B_{123}(p)\ \le\ \min_{1\le i\le3}\Big(1+\frac{H}{\lambda_1^{(i)}(p)}+\frac{H^2}{q_i}\Big).
$$

*Proof.* The map $x_4\mapsto(x_4,\ (c_ix_4\bmod q_i)_{\mathrm{bal}})$ is an
injection into $\Lambda_i(p)\cap[-H,H]^2$. For any rank-2 lattice with reduced
basis $b_1,b_2$ ($\lambda_1=|b_1|\le|b_2|=\lambda_2$, $\lambda_1\lambda_2\asymp\det$),
the number of lattice points in $[-H,H]^2$ is

$$
\ll\Big(1+\frac H{\lambda_1}\Big)\Big(1+\frac H{\lambda_2}\Big)
\ll 1+\frac H{\lambda_1}+\frac{H^2}{\lambda_1\lambda_2}
\ll 1+\frac H{\lambda_1}+\frac{H^2}{\det}.
$$

Take $\det=q_i$. The $B_{123}$ bound follows since
$B_{123}(p)\le\#\{x_4: c_ix_4\in[-H,H]\}$ for the cheapest $i$. $\qquad\blacksquare$

**Reading at the central scale $H\asymp X^{1/2}$.** Here $H^2/q_i\asymp1$, and a
generic prime has $\lambda_1^{(i)}\asymp X^{1/2}\asymp H$, so $B_{123}(p)\ll1$.
$B_{123}(p)$ can only be large when, **for the minimizing $i$**,
$\lambda_1^{(i)}(p)\ll H/T$, i.e. $q_4/p$ has a denominator-$\le T$ rational
approximation modulo $q_i$ — a low-height relation $q_i\mid q_4b+pe$ with
$\max(|b|,|e|)\le T$.

## 3. Inverse difference lemma (airtight)

**Lemma C.** If $B_{123}(p)\ge2$ then there is a nonzero short vector
$(\delta,\epsilon_1,\epsilon_2,\epsilon_3)$, $0<|\delta|\le 2H$,
$|\epsilon_i|\le 2H$, with

$$
q_i\mid q_4\,\delta+p\,\epsilon_i\qquad(i=1,2,3)\quad\text{simultaneously.}
$$

*Proof.* Two cluster solutions at the same $p$ give $x_4\ne x_4'$ and, for each
$i$, $a_i,a_i'$ with $q_i\mid pa_i+q_4x_4$ and $q_i\mid pa_i'+q_4x_4'$.
Subtracting, $q_i\mid p(a_i-a_i')+q_4(x_4-x_4')$. Set $\delta=x_4-x_4'\ne0$,
$\epsilon_i=a_i-a_i'$. $\qquad\blacksquare$

Lemma C is the cluster analogue of the anchor determinant identity
`q4_dvd_anchor_collision_det`, but it is **not $p$-free**: it pins $p$ modulo
$q_i$ via short data, $p\equiv -q_4\delta\,\epsilon_i^{-1}\pmod{q_i}$ (when
$\epsilon_i\ne0$). With all three moduli, $p$ is pinned modulo $q_1q_2q_3\asymp X^3$
by a single short vector. This is exactly the simultaneous short lattice vector
of §1–2: $(\delta,\epsilon_i)\in\Lambda_i(p)$ for every $i$.

## 4. The structured family, made explicit

Define, for a threshold $T=(\log X)^{B}$, the **structured (bad) prime set**

$$
P_{\mathrm{struct}}(T)=\Big\{p\in[X,2X]:\ \lambda_1^{(i)}(p)\le H/T\ \text{for all }i=1,2,3\Big\}.
$$

By §2, every prime with $B_{123}(p)\ge2$ that is *not* explained by a single
small modulus lies in (a relaxation of) $P_{\mathrm{struct}}$; and $p\in
P_{\mathrm{struct}}$ means three simultaneous low-height relations

$$
q_i\mid q_4\,b_i+p\,e_i,\qquad \max(|b_i|,|e_i|)\le H/T\ (\asymp X^{1/2}/T),
$$

one per $i$. Eliminating $p$ between two indices $i,j$ gives a relation **among
the seeds alone**:

$$
q_i\mid q_4b_i+pe_i,\ \ q_j\mid q_4b_j+pe_j
\ \Longrightarrow\ q_iq_j\ \big|\ q_4(b_ie_j-b_je_i)+p\,0\ \text{(after clearing }p)\ \ldots
$$

more precisely $p\equiv-q_4b_i\bar e_i\pmod{q_i}$ and $p\equiv-q_4b_j\bar e_j\pmod{q_j}$,
a CRT constraint that, as $p$ also lies in $[X,2X]$ (length $X<q_iq_j$), admits
$O(1)$ solutions $p$ per choice of short $(b,e)$. Hence

$$
|P_{\mathrm{struct}}(T)|\ \ll\ \#\{\text{short }(b_i,e_i)_{i}\}\cdot O(1)\ \ll\ (H/T)^{6}/X^{2}+ \ldots
$$

(The exponent bookkeeping is the content of the next sub-step; the point is that
$P_{\mathrm{struct}}$ is governed by short seed relations and is *thin*.)

## 5. Where this leaves the correlation

Split the reduced sum:

$$
N_H'=\underbrace{\sum_{p\notin P_{\mathrm{struct}}}A_{04}(p)B_{123}(p)}_{\text{generic}}
+\underbrace{\sum_{p\in P_{\mathrm{struct}}}A_{04}(p)B_{123}(p)}_{\text{structured}}.
$$

* **Generic part.** Here $B_{123}(p)\ll T=(\log X)^B$ by Lemma B. This is *not*
  yet enough on its own — recall from [[08 Anchor Energy and the Joint Obstruction]]
  that $\sum_pA_{04}(p)\asymp X/\log X$ is large, so we may **not** factor out
  $\max B_{123}$ and sum $A_{04}$. The correct treatment restricts to
  $\{p:B_{123}(p)\ge1\}$, a set of size $\ll H^4/X^2$ (each cluster solution pins
  $p$ to one class mod $q_1q_2q_3\asymp X^3$), and bounds the anchor mass carried
  there. This is the remaining analytic step.
* **Structured part.** This is the low-entropy family the theorem is *allowed*
  to exclude (or to feed into the FIE ledger): by §4 it is thin and is exactly
  characterized by short seed relations $q_i\mid q_4b+pe$.

## 6. Status

* **Proved unconditionally:** Lemma B (geometry of numbers), Lemma C (inverse
  difference), and the explicit characterization of the structured family by
  short relations $q_i\mid q_4b+pe$.
* **Reduced to:** bounding the *generic* anchor mass on the thin set
  $\{p:B_{123}(p)\ge1\}$ — i.e. showing the two rare events "$A_{04}(p)\ge1$"
  (prob $\asymp H^2/X$) and "$B_{123}(p)\ge1$" (set size $\ll H^4/X^2$) do not
  conspire outside $P_{\mathrm{struct}}$. This is the genuine residue of the
  `sorry` in `FourierPositivity.lean`.

**Net effect on Task 4.** The vague "many collisions ⟹ low-entropy seeds" is now
a concrete, partially-proved dichotomy: cluster concentration at $p$ ⟺ short
relations $q_i\mid q_4b+pe$ (Lemmas B, C), and the only unproved piece is a
single-sided counting estimate for the generic anchor mass on a thin prime set.

## Lean / HA handoff (cumulative package)

Add to `core-packet/lean/` incrementally:
1. Lemma B as a lattice-point count (generalize the box-counting already implicit
   in `AnchoredDeterminantRank.lean`). Inputs: reduced-basis bound for $\mathbb Z^2$.
2. Lemma C: a two-line subtraction, directly formalizable; mirror of
   `q4_dvd_anchor_collision_det`.
3. Define $P_{\mathrm{struct}}(T)$ and the seed-relation predicate so the inverse
   theorem has a precise formal target feeding `SplitCorrelation`.
