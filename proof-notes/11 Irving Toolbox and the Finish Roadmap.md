# Irving Toolbox and the Finish Roadmap

Back to [[00 README]]. Prerequisite: [[10 Kloosterman Reduction of the Correlation]].

[[10 Kloosterman Reduction of the Correlation]] reduced the correlation to
reciprocal sums over primes, $S_q(a;x)=\sum_{p\sim x,(p,q)=1}e(a\overline p/q)$,
in the regime $x\asymp q\asymp X$. This note records the exact tools from
Irving's paper (`archive/kloost_paper2.tex`), resolves *why primes are essential*
(Weil alone is on the boundary), resolves the *individual-vs-average* question
(and connects it to SBEE's averaging), and writes the concrete finish roadmap.

## 1. Why Weil alone fails — and where the spare power lives

Irving's own summary (his §3): *"After inverting the Kloosterman fractions … the
Weil estimate for short Kloosterman sums can be used. … In the case that one of
the coefficients is the indicator function of the primes then our theorem does
better than [Duke–Friedlander–Iwaniec's general bilinear bound], provided that
$x$ and $Q$ are sufficiently close in size."*

This is the precise resolution of the barrier flagged in
[[02 Active Rational-Collision Problem]] and [[04 Failure and Risk Ledger]]:

* The Weil bound for a *complete* Kloosterman sum mod $q$ is $\ll q^{1/2}$; at
  length $x\asymp q\asymp X$ and box $H\asymp X^{1/2}$, completion + Weil lands
  exactly on the main term with **no spare power** — the project's claim is
  correct.
* The spare power comes instead from the **bilinear decomposition of the prime
  indicator** (Vaughan/Vinogradov), combined with the **reciprocal-equation
  moment** (Lemma 2 below). This beats the general bilinear (DFI) bound *exactly
  when $x\asymp q$* — our regime.

So primes are not incidental: the extra averaging hidden in
$\mathbf 1_{\text{prime}}$ is the engine. This is why the formal skeleton cites
`IrvingKloostermanBound'` and not a bare Weil bound.

## 2. The toolbox (verbatim from Irving)

**Completion lemma.** For integers $a,q$ ($q>1$) and reals $Y<Z$, any $\epsilon>0$:
$$
\sum_{\substack{Y<n\le Z\\(n,q)=1}}e\!\Big(\frac{a\overline n}{q}\Big)
\ll_\epsilon\Big((a,q)\big(\tfrac{Z-Y}{q}+1\big)+q^{1/2}\Big)q^\epsilon.
$$
(This is the integer/Weil bound; square-root cancellation only.)

**Reciprocal-equation moment (Lemma 2).** For fixed $k$,
$$
\#\Big\{0<n_i\le N:\ \tfrac1{n_1}+\cdots+\tfrac1{n_k}=\tfrac1{n_{k+1}}+\cdots+\tfrac1{n_{2k}}\Big\}\ll_{k,\epsilon}N^{k+\epsilon}.
$$

**Congruence moment.** $J^{(k)}_M(q)=\#\{\overline m_1+\cdots+\overline m_k\equiv\overline m_{k+1}+\cdots+\overline m_{2k}\ (q),\ m_i\le M\}$ satisfies
$\sum_{q\sim Q}J^{(k)}_M(q)\ll_{k,\epsilon}(QM^k+M^{2k})M^\epsilon$.

**Bilinear sums.** With $W_{a,q}=\sum_{l\sim L,m\sim M,(lm,q)=1}\alpha_l\beta_m e(a\overline{lm}/q)$, $|\alpha|,|\beta|\le1$:
* Type I ($\beta_m=1$), individual: $W\ll_\epsilon((a,q)(\tfrac{LM}{Q}+L)+Q^{1/2}L)Q^\epsilon$;
  on average: $\sum_{q\sim Q}\max_{(a,q)=1}|W_{a,q}|\ll_\epsilon(LM+Q^{3/2}L)Q^\epsilon$.
* Type II, on average: $\sum_{q\sim Q}\max_{(a,q)=1}|W_{a,q}|\ll_{\epsilon,k}Q(Q^{\frac1{2k}}L^{\frac{2k-1}{2k}}M^{\frac12}+L^{\frac{2k-1}{2k}}M)Q^\epsilon$.

**Main theorems (the prime sum $S_q(a;x)$).**
* **Thm 1.** $\displaystyle\sum_{q\sim Q}\max_{(a,q)=1}|S_q(a;x)|\ll_\epsilon(Q^{5/4}x^{5/8}+Qx^{9/10}+Q^{7/6}x^{13/18})Q^\epsilon$ for $Q^{3/2}\ge x\ge Q^{2/3}$.
* **Thm 2.** $\displaystyle\sum_{q\sim Q}|S_q(a;x)|\ll_\epsilon(1+\tfrac a{xQ})^{1/2}(Q^{1/2}x^{11/8}+Q^{7/6}x^{2/3})(aQ)^\epsilon$ for $Q^{4/3}\ge x\ge Q^{1/2}$.
* **(Garaev, individual, $q$ prime, $x<q$):** $\max_{(a,q)=1}|S_q(a;x)|\ll_\epsilon(x^{15/16}+x^{2/3}q^{1/4})q^\epsilon$, nontrivial for $x\ge q^{3/4+\delta}$.

## 3. Individual vs. average — and the SBEE connection

Our seed moduli $q_0,\ldots,q_4$ are **fixed**, so a first reading wants an
*individual* bound. Two regimes:

* **Individual (fixed seeds).** Only Garaev's $S_q(a;x)\ll x^{15/16}$ is
  available, saving $x^{1/16}$. This suffices to beat the main term by a small
  power for a *single* tuple outside the structured family, but the bookkeeping
  is tight.
* **Average (the honest route).** Irving's strong Theorems 1–2 average over
  $q\sim Q$. The reduced inverse theorem of [[07 Diagonal Ledger]] does **not**
  need to hold for every fixed tuple — for Fourier positivity / SBEE global
  control it suffices that the correlation is small **on average over the seed
  primes**, with the structured family being the average-negligible exceptional
  set.

> **Key unification.** The "average over $q\sim Q$" in Irving's Theorems 1–2 is
> exactly the "average over prime blocks" in the SBEE global-control partition
> (`SBEE.lean`, `ConditionSBEE`). They are the same averaging. This is why SBEE
> cites Irving: the polymer/partition average *is* the modulus average that
> unlocks Irving's strong bounds. The structured family of
> [[09 Cluster Concentration and the Structured Family]] is the set of seed
> tuples removed before averaging.

This dissolves the individual-vs-average tension: we should prove the **averaged**
correlation bound and feed it to SBEE, not a per-tuple bound.

## 4. Finish roadmap

1. **Reduce to $S_q$-type sums.** From [[10 Kloosterman Reduction of the Correlation]]
   §4: expand the anchor congruence (characters mod $q_4$), Poisson-complete the
   short cluster variables $a_i$ (dual frequencies $h_i\ll q_i/H\asymp X^{1/2}$),
   leaving $\sum_{p\sim X}e_{q_i}(h_i\overline p)\cdot(\text{linear }q_4\text{ phase})$.
2. **Vaughan decomposition.** Replace $\mathbf 1_{\text{prime}}(p)$ by Type I +
   Type II bilinear pieces, turning each into $W_{a,q}$ with $a$ built from the
   dual frequencies, modulus $q_i$ (or $q_iq_4$).
3. **Apply Irving §3.** Bound Type I by the individual/average bilinear bounds;
   Type II by the average bound (using the reciprocal moment, Lemma 2). The
   regime $x\asymp q$ is where these beat DFI.
4. **Sum over dual frequencies $h_i$ ($\ll X^{1/2}$ each) and over $t$.** Use the
   completion lemma to control the frequency sums; verify the total saving sits
   below the main term $\asymp H^6/(X^3)$.
5. **Cluster first moment $M_B$.** Main term clean and unconditional; the error
   needs the single-modulus bilinear treatment (Type I, with the other two
   moduli as AP-restrictions) — **not** a bare $S_q$ bound. See
   [[12 M_B Computation and the Bilinear Necessity]] (which corrects the earlier
   "self-contained/Type-I-only" framing).
6. **Feed the averaged bound to SBEE.** Conclude `fourier_positivity_unconditional`.

## 5. Status

The remaining gap is now fully mapped: it is a Vaughan + Irving-bilinear
computation in the favorable regime $x\asymp q$, to be proved **on average over
seed primes** (matching SBEE's averaging), with the structured family excluded.
No step is mysterious; each is a named, published technique applied to a sum we
have written down explicitly. The next concrete action is the bookkeeping of
steps 1–4 for the simplest piece (Type I / the $M_B$ moment), then the Type II
piece.

## Lean / HA handoff

`IrvingKloostermanBound'` in `SBEE.lean` should be restated to its true content
(Thm 1 and/or Thm 2 above) and wired to the error term; this makes the formal
dependency honest. The toolbox lemmas of §2 are citable external inputs, not
targets for re-proof.
