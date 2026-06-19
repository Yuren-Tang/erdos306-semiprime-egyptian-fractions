# M_B Computation and the Bilinear Necessity

Back to [[00 README]]. Prerequisites: [[10 Kloosterman Reduction of the Correlation]],
[[11 Irving Toolbox and the Finish Roadmap]].

This note carries out the explicit completion for the cluster first moment
$M_B=\sum_{p\sim X,(p,\mathcal Q)=1}B_{123}(p)$. It extracts the **main term
cleanly** and establishes an honest correction: **$M_B$ is not a soft
"self-contained" object** — term-by-term Weil on the completed short sums is
insufficient, so $M_B$ already requires the Irving bilinear machinery. The note
also pins the **regime constraint** (cancellation must stay on a single modulus
$q_i$).

## 1. The completion

Write each cluster count by completing the short $a_i$-sum over $|a_i|\le H$ via
characters mod $q_i$. With $a_i\equiv-q_4x_4\overline p\pmod{q_i}$,

$$
\#\{a_i\}=\frac1{q_i}\sum_{h_i\bmod q_i}D_H\!\Big(\tfrac{h_i}{q_i}\Big)\,e_{q_i}\!\big(h_i q_4 x_4\overline p\big),
\qquad |D_H(\theta)|\ll\min\!\big(2H,\|\theta\|^{-1}\big),
$$

where $D_H$ is the Dirichlet kernel. Hence

$$
M_B=\sum_{p\sim X}\sum_{0<|x_4|\le H}\ \prod_{i=1}^3\frac1{q_i}\sum_{h_i}D_H\!\Big(\tfrac{h_i}{q_i}\Big)e_{q_i}\!\big(h_iq_4x_4\overline p\big).
$$

## 2. Main term (clean, correct)

The term $h_1=h_2=h_3=0$ gives $\prod_i\frac{2H+1}{q_i}$, times
$\sum_{x_4}\sum_{p\sim X}1\asymp 2H\cdot\frac{X}{\log X}$:

$$
M_B^{\mathrm{main}}=\prod_i\frac{2H+1}{q_i}\cdot 2H\cdot\frac{X}{\log X}
\asymp\frac{(2H)^3}{q_1q_2q_3}\cdot\frac{2HX}{\log X}
\asymp\frac{H^4}{X^2\log X}.
$$

This is **exactly the target** $M_B\ll(\log X)^C(1+H^4/X^2)$ — unconditionally, and
matching the heuristic of [[10 Kloosterman Reduction of the Correlation]] §3.

## 3. The error couples the three moduli into a reciprocal phase

Any term with some $h_i\ne0$ collects, by CRT, into a single reciprocal phase

$$
\prod_i e_{q_i}\!\big(h_iq_4x_4\overline p\big)=e_{Q_3}\!\big(\Xi\,x_4\,\overline p\big),
\qquad \Xi=q_4\sum_i h_i\,\overline{(Q_3/q_i)}\bmod Q_3,\ \ Q_3=q_1q_2q_3,
$$

so the $p$-sum is $\sum_{p\sim X}e_{Q_3}(\Xi x_4\overline p)=S_{Q_3}(\Xi x_4;X)$ —
Irving's prime reciprocal sum, **but to the composite modulus $Q_3\asymp X^3$**.

## 4. The regime constraint (decisive)

With modulus $Q_3\asymp X^3$ and length $x\asymp X=Q_3^{1/3}$, we have
$x=Q_3^{1/3}$, which is **outside** every nontrivial range:
$x\ge q^{3/4}$ (Garaev), $x\ge Q^{2/3}$ (Irving Thm 1), $x\ge Q^{1/2}$ (Thm 2).
So **collapsing all three moduli into $Q_3$ is fatal** — it lands in the hopeless
regime warned about in [[10 Kloosterman Reduction of the Correlation]].

**The fix.** Keep genuine cancellation on a *single* modulus $q_i\asymp X$ (length
$x\asymp X\asymp q_i$, the good regime). Complete only one $a_i$ (say $a_1$);
treat the existence of short $a_2,a_3$ as congruence restrictions on $p$ modulo
$q_2,q_3$. Then the $p$-sum is

$$
\sum_{\substack{p\sim X\\ p\in\text{APs mod }q_2q_3}}e_{q_1}\!\big(h_1q_4x_4\overline p\big),
$$

a single-modulus ($q_1$) reciprocal sum over primes restricted to arithmetic
progressions mod $q_2q_3$. The AP restrictions are exactly the **bilinear
coefficients** $\alpha_l,\beta_m$ in Irving's $W_{a,q}=\sum_{l,m}\alpha_l\beta_m
e(a\overline{lm}/q)$. This is why Irving's *bilinear* method (not a bare $S_q$
bound) is the tool, even for the "first moment" $M_B$.

## 5. Honest correction to notes 10–11

Notes [[10 Kloosterman Reduction of the Correlation]] and
[[11 Irving Toolbox and the Finish Roadmap]] called $M_B$ "easier /
self-contained / Type I only." **That was too optimistic.** The main term is
indeed easy (§2), but the *error* in $M_B$ already:

* couples all three moduli unless organized carefully (§3);
* forces the cancellation onto a single modulus with the other two as bilinear
  AP-restrictions (§4);
* therefore needs the full Irving bilinear apparatus (Type I at least, with the
  reciprocal-equation moment), not a term-by-term Weil bound.

Term-by-term Weil ($|S_{q_i}|\ll q_i^{1/2}$ per frequency, then absolute values)
is insufficient: summed over the $\ll(X^{1/2})^3$ frequency tuples it exceeds the
main term by a power of $X$. The required cancellation lives in the **joint**
sum over $x_4$, the frequencies $h_i$, and $p$ — i.e. it is bilinear. This is the
rigorous local form of "Weil alone has no spare power."

## 6. Status and next step

* **Proved:** the main term of $M_B$ is $\asymp H^4/(X^2\log X)$, clean and
  unconditional (§2).
* **Pinned:** the error must be organized as a single-modulus ($q_i$) bilinear
  reciprocal sum over primes in APs mod the other two moduli (§4); the composite-
  modulus organization is fatal (§3–4).
* **Next:** follow Irving's own application (his proof that
  $P^+(p_1p_2+p_1p_3+p_2p_3)>x^\theta$, §4 of `archive/kloost_paper2.tex`), which
  bounds exactly this type of single-modulus bilinear reciprocal sum over primes
  in progressions. Transcribe his Type I bound to our $a=h_1q_4x_4$,
  $q=q_1$, $L,M$ from the $q_2q_3$-progression factorization, and verify the
  saving sits below §2's main term. Then iterate to the full correlation
  $N_H'$ (which adds the anchor frequency, one more modulus $q_4$).
