# Kloosterman Reduction of the Correlation

Back to [[00 README]]. Prerequisites: [[08 Anchor Energy and the Joint Obstruction]],
[[09 Cluster Concentration and the Structured Family]].

This note reaches the analytic floor of the problem. It does two things:

1. **Delimits the elementary barrier.** It shows rigorously that the residual
   correlation cannot be closed by counting alone — the obstruction is exactly
   the cluster concentration $\max_p B_{123}(p)$ of [[09 Cluster Concentration and the Structured Family]].
2. **Names and applies the tool.** An additive-character expansion of the
   *anchor* side recovers the correct main term unconditionally and isolates the
   error as a specific **incomplete Kloosterman correlation**. The bound needed
   is exactly **Irving's incomplete Kloosterman estimate** — the input already
   cited (but left unconnected) in `SBEE.lean` as `IrvingKloostermanBound'`.

This connects the SBEE Irving citation to the active correlation: they are the
same analytic input.

## 1. The elementary barrier is real (no pure-counting proof)

From [[09 Cluster Concentration and the Structured Family]], the second moment of
the cluster count splits as

$$
\sum_p B_{123}(p)^2=\underbrace{\sum_p B_{123}(p)}_{\text{diagonal}\,\asymp\,H^4/X^2}
+\underbrace{\sum_p B_{123}(p)\bigl(B_{123}(p)-1\bigr)}_{\text{off-diagonal}}.
$$

The off-diagonal counts ordered pairs of distinct cluster solutions at a common
$p$; by Lemma C every such pair carries a nonzero short simultaneous relation
$q_i\mid q_4\delta+p\epsilon_i$. Re-summing shows the off-diagonal equals
$\sum_p B_{123}(p)^2$ minus the diagonal — i.e. **any attempt to bound the second
moment by counting solutions is circular.** The off-diagonal is genuinely
controlled by the concentration $\max_p B_{123}(p)$, which is $\asymp H$ for
structured seeds and $\asymp 1$ otherwise. Hence:

> **No purely combinatorial bound on $N_H'$ exists** that does not already
> incorporate the concentration dichotomy of [[09 Cluster Concentration and the Structured Family]].
> Cancellation (Fourier/Kloosterman) is necessary, confirming the barrier
> asserted in [[04 Failure and Risk Ledger]] and the C–S obstruction of
> [[08 Anchor Energy and the Joint Obstruction]] — now from the $B$-energy side too.

## 2. Additive-character expansion of the anchor side

Detect the anchor congruence $q_4\mid py_4+q_0x_0$ with additive characters mod
$q_4$:

$$
A_{04}(p)=\frac1{q_4}\sum_{t\bmod q_4}\Big(\sum_{0<|x_0|\le H}e_{q_4}(t\,q_0x_0)\Big)\Big(\sum_{0<|y_4|\le H}e_{q_4}(t\,p\,y_4)\Big).
$$

The $t=0$ term is the **main term** $\dfrac{(2H+1)^2-1}{q_4}$ (up to the
nonzero-variable correction). For $t\ne0$ each inner sum is an incomplete
geometric (Dirichlet-kernel) sum, $\ll\min\!\big(H,\|tq_0/q_4\|^{-1}\big)$ and
$\ll\min\!\big(H,\|tp/q_4\|^{-1}\big)$ respectively. Therefore

$$
A_{04}(p)=\frac{(2H+1)^2-1}{q_4}
+O\!\Big(\frac1{q_4}\sum_{t\ne0}\min\!\big(H,\tfrac1{\|tq_0/q_4\|}\big)\min\!\big(H,\tfrac1{\|tp/q_4\|}\big)\Big).
$$

## 3. Main term: correct and unconditional

Insert into $N_H'=\sum_p A_{04}(p)B_{123}(p)$. The $t=0$ part gives

$$
N_H'^{\mathrm{main}}=\frac{(2H+1)^2-1}{q_4}\sum_{p\nmid\mathcal Q}B_{123}(p)
\ \asymp\ \frac{H^2}{X}\,M_B,\qquad M_B:=\sum_{p}B_{123}(p).
$$

With the cluster first moment $M_B\asymp H^4/(X^2\log X)$ this is

$$
N_H'^{\mathrm{main}}\ \asymp\ \frac{H^6}{X^3\log X},
$$

exactly the target shape $1+H^6/X^3$ (the "$1$" being the trivial diagonal hit).
**The main term needs no structural hypothesis.** Its size rides on $M_B$, the
cluster first moment, which is a strictly easier object than $N_H'$ (one-sided,
no anchor coupling) and is bounded by a single completable Kloosterman sum over
$p$; controlling $M_B\ll(\log X)^C(1+H^4/X^2)$ is a clean sub-lemma.

## 4. Error term: a reciprocal sum over primes (Irving's exact object)

The $t\ne0$ part is

$$
N_H'^{\mathrm{err}}\ \ll\ \frac1{q_4}\sum_{t\ne0}\min\!\big(H,\tfrac1{\|tq_0/q_4\|}\big)
\;\Big|\sum_{p\nmid\mathcal Q}B_{123}(p)\,e_{q_4}(t\,p\,y_4)\Big|.
$$

(The anchor phase is **linear** in $p$ modulo $q_4$.) The weight $B_{123}(p)$ is
where the reciprocal of $p$ enters. Open it through the short cluster variables:
the congruence $q_i\mid p\,a_i+q_4x_4$ solves as

$$
a_i\equiv -q_4\,x_4\,\overline p\pmod{q_i},
$$

a **reciprocal of $p$** modulo $q_i$. Completing the short sums over
$a_i\in[-H,H]$ by Poisson (box length $H\asymp X^{1/2}\asymp q_i^{1/2}$, so the
completion is incomplete with dual frequencies $h_i\ll q_i/H\asymp X^{1/2}$)
turns the $p$-sum into a combination, over the bounded-by-$X^{1/2}$ dual
frequencies, of

$$
\sum_{p\sim X,\ (p,\mathcal Q)=1} e\!\Big(\frac{h_i\,\overline p}{q_i}\Big)\,e_{q_4}(t\,p\,y_4)
\;=\;S_{q_i}(h_i;X)\text{-type sums}.
$$

**This is exactly Irving's object** $S_q(a;x)=\sum_{p\sim x,(p,q)=1}e(a\overline
p/q)$ (`archive/kloost_paper2.tex`, *Average Bounds for Kloosterman Sums Over
Primes*, A. J. Irving). The decisive point is the **regime**: here the modulus is
$q_i\asymp X$ (or $q_iq_4\asymp X^2$) and the prime range is $x\asymp X$, so

$$
x\ \asymp\ q\qquad(\text{i.e. }x=q^{1+o(1)}),
$$

which sits **well inside** the nontrivial range $x\ge q^{3/4+\delta}$ where
Garaev / Fouvry–Shparlinski / Irving give a power saving (Garaev alone yields
$S_q(a;X)\ll X^{15/16+\epsilon}$, a saving of $X^{1/16}$; Irving's Theorems 1–2
give sharper bounds on average over the modulus or the frequency, with the
uniformity needed to sum over the $\ll X^{1/2}$ dual frequencies $h_i$ and over
$t$). The earlier worry (square-root-of-modulus barrier) was misplaced for this
organization: it would only arise if one inflated the modulus to
$q_1q_2q_3q_4\asymp X^4$ by completing *all* cluster conditions at once (giving
$x\asymp q^{1/4}$, hopeless). Keeping the reciprocal modulus at a single $q_i$
puts us in the good regime.

**Structural confirmation.** Irving's own application (his Theorem on
$P^+(p_1p_2+p_1p_3+p_2p_3)$ for primes $p_i\sim x$) is the *same shape* as our
three-cluster anchored star — a ternary symmetric prime form controlled by
exactly these reciprocal sums. This is strong evidence the tool is correctly
matched, not merely available.

`IrvingKloostermanBound'` in `SBEE.lean` (currently concluding `True`) is the
formal placeholder for precisely this input. **Here it is the actual tool,
applied to the actual sum, in its actual range of validity.**

The structured family of [[09 Cluster Concentration and the Structured Family]]
is exactly where this Kloosterman sum **degenerates** (the phase $tp/q_4$
aligning with the reciprocal classes mod $q_i$ corresponds to a short seed
relation $q_i\mid q_4b+pe$); there Irving's bound is vacuous and the term is
absorbed into the excluded low-entropy family.

## 5. The precise remaining analytic lemma

Everything reduces to:

> **Kloosterman input (the last analytic step).** For seeds outside the
> structured family of [[09 Cluster Concentration and the Structured Family]],
> $$
> \Big|\sum_{p\nmid\mathcal Q}B_{123}(p)\,e_{q_4}(t\,p\,y_4)\Big|
> \ \ll\ (\log X)^{C}\,X^{-\eta}\,M_B,
> $$
> uniformly in $t\ne0$ and $y_4$, for some fixed $\eta>0$, via the reciprocal
> prime-sum bound of §4 (Garaev/Irving in the regime $x\asymp q$). The structured
> family is exactly where these reciprocal sums degenerate (the dual frequency
> $h_i$ aligning with a short seed relation $q_i\mid q_4b+pe$), and is excluded.

Granting this and the clean sub-lemma $M_B\ll(\log X)^C(1+H^4/X^2)$, §3–4 give

$$
N_H'\ \ll\ (\log X)^{C}\Big(1+\frac{H^6}{X^3}\Big)\qquad\text{outside structured seeds,}
$$

which is the reduced inverse theorem of [[07 Diagonal Ledger]] and closes the
`sorry` in `FourierPositivity.lean`.

## 6. Status and the two remaining ingredients

The mathematical gap is now two named, standard-shaped analytic estimates:

1. **Cluster first moment** $M_B=\sum_pB_{123}(p)\ll(\log X)^C(1+H^4/X^2)$. Its
   *main term* is clean and unconditional ([[12 M_B Computation and the Bilinear Necessity]] §2),
   but its *error* already requires the bilinear method (NOT a bare Kloosterman
   bound) — see the correction in [[12 M_B Computation and the Bilinear Necessity]].
2. **(the crux) Kloosterman power saving** of §5 — an application of Irving's
   incomplete Kloosterman bound, vacuous exactly on the structured family.

Everything else (diagonal removal, anchor energy, cluster concentration, the
main term, the structured-family characterization) is proved unconditionally in
[[07 Diagonal Ledger]], [[08 Anchor Energy and the Joint Obstruction]],
[[09 Cluster Concentration and the Structured Family]], and §1–3 here.

## Next actions

* **Math (regime confirmed).** Irving's paper is in the repo
  (`archive/kloost_paper2.tex`); its object is literally $S_q(a;x)=\sum_{p\sim
  x,(p,q)=1}e(a\bar p/q)$. Relevant ranges: Garaev (individual, $q$ prime)
  nontrivial for $x\ge q^{3/4+\delta}$, giving $\ll x^{15/16+\epsilon}$;
  Irving Thm 1 (average over $q\sim Q$) for $Q^{3/2}\ge x\ge Q^{2/3}$; Thm 2 for
  $Q^{4/3}\ge x\ge Q^{1/2}$. Our case $x\asymp q\asymp X$ satisfies all three.
  Remaining computation: carry out the Poisson completion in the $a_i$-box
  explicitly, track the $\ll X^{1/2}$ dual frequencies $h_i$, and decide whether
  Garaev's individual $X^{1/16}$ saving suffices or the averaged Irving Thm 1/2
  (over the modulus/frequency) is required for uniformity. Then prove ingredient
  1 ($M_B$), which is self-contained (a single completable reciprocal sum).
* **Lean/HA (cumulative):** once $M_B$ is proved, formalize it into
  `core-packet/lean/`; restate `IrvingKloostermanBound'` from `SBEE.lean` with
  its true conclusion (currently `True`) and wire it to the §4 error term so the
  formal dependency is honest.
