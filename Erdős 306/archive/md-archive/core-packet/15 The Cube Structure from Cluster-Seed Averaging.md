# The Cube Structure from Cluster-Seed Averaging

Back to [[00 README]]. Prerequisites: [[14 Fouvry-Shparlinski Is the Template]],
[[08 Anchor Energy and the Joint Obstruction]].

This note resolves the one real worry about using Fouvry–Shparlinski as a
template. FS count **three primes against one modulus**; our cluster count is the
**transpose** — one prime $p$ against three moduli $q_1,q_2,q_3$. The transpose
does *not* inherit FS's favorable single-modulus regime directly (this is the
composite-modulus obstruction of [[12 M_B Computation and the Bilinear Necessity]] §4).

The resolution: **averaging over the three cluster seeds $q_1,q_2,q_3$ recovers a
genuine cube / third-moment structure**, exactly FS's $\frac1q\sum_a S_q(a;x)^3$.
The averaging is the SBEE prime-block average ([[13 The Averaged Framing Is Essential]]),
so this is not an extra assumption — it is the form the theorem must take anyway.

## 1. Reading the FS proof (eq. (4.3))

FS reduce $A^*(x;q)=\#\{(p_1,p_2,p_3)\in\mathcal T(x):(p_i,q)=1,\ \overline{p_1}+\overline{p_2}+\overline{p_3}\equiv0\ (q)\}$
to the **third moment**
$$
A^*(x;q)=\frac1q\sum_{a=1}^q S_q(a;x)^3,\qquad S_q(a;x)=\sum_{p\sim x}e\!\Big(\tfrac{a\overline p}{q}\Big).
$$
The $a=q$ term is the main term; the error is $\frac1q\sum_{a\ne0}|S_q(a;x)|^3\le
\max_a|S_q|\cdot\frac1q\sum_a|S_q|^2=\max_a|S_q|\cdot\tilde\pi(x)$ (Parseval), then
Theorem 3.1/3.3 bounds $\max_a|S_q|$. The **cube comes from three independent
prime variables sharing one modulus**.

## 2. The transpose obstruction (why we cannot copy directly)

Our cluster count $B_{123}(p)$ has one prime $p$ and three moduli. Completing all
three short $a_i$-sums merges the moduli into $Q_3=q_1q_2q_3\asymp X^3$, length
$x\asymp X=Q_3^{1/3}$ — outside every nontrivial range
([[12 M_B Computation and the Bilinear Necessity]] §3–4). So a direct copy fails.

## 3. The fix: average over $q_1,q_2,q_3$, get a cube

The cluster seeds $q_1,q_2,q_3$ are themselves primes $\sim X$. Average $N_H'$
over them (the anchor factor $A_{04}(p)$ depends only on $q_0,q_4$, so it is
inert under this average):

$$
\sum_{q_1,q_2,q_3\sim X}N_H'
=\sum_{p}A_{04}(p)\sum_{x_4}\sum_{a_1,a_2,a_3}\prod_{i=1}^3\Big(\sum_{q_i\sim X}\mathbf 1[q_i\mid pa_i+q_4x_4]\Big).
$$

For fixed $(p,x_4,a_i)$ the three $q_i$-sums are independent (each $q_i$ appears
only in factor $i$), and the three $a_i$-sums are independent. Hence the inner
sum **factors into a cube**:

$$
\boxed{\ \sum_{q_1,q_2,q_3\sim X}N_H'=\sum_{p}A_{04}(p)\sum_{x_4}\,g(p,x_4)^3,\qquad
g(p,x_4):=\sum_{0<|a|\le H}\ \#\{q\sim X\ \text{prime}: q\mid pa+q_4x_4\}.\ }
$$

By the reciprocal identity $q\mid pa+q_4x_4\iff a\equiv -q_4x_4\overline p\pmod q$,

$$
g(p,x_4)=\#\{q\sim X\ \text{prime}: \ \|q_4x_4\overline p/q\|\le H/q\}
=\#\{(a,q): |a|\le H,\ q\sim X,\ q\mid pa+q_4x_4\}.
$$

This is the **exact analogue of FS's structure**: a counting function defined by
a reciprocal condition, raised to the cube, summed over the remaining variables.
The "three" of FS's ternary form is our **three cluster seeds**; the cube arises
from the three independent $(a_i,q_i)$ pairs.

## 4. Expansion to the third moment of $S_q$

Expanding $g(p,x_4)$ by detecting $q\mid pa+q_4x_4$ with additive characters
(completion, Lemma 2.1 of [[14 Fouvry-Shparlinski Is the Template]]) gives, per
modulus $q\sim X$, a reciprocal sum; the cube $g^3$ and the sum over $q_1,q_2,q_3$
reproduce a triple
$$
\sim\ \sum_{q_1,q_2,q_3\sim X}\frac1{q_1q_2q_3}\sum_{a_1,a_2,a_3}\widehat W(\cdot)\prod_i S_{q_i}(a_i\cdot;X\ \text{-type}),
$$
each $S_{q_i}$ a **single-modulus** ($q_i\asymp X$) reciprocal prime sum in the
**good regime** $x\asymp q_i$. The composite-modulus obstruction of §2 is gone:
averaging separated the moduli before completion. FS's Theorem 3.1/3.3 and the
Cayley moment (Lemma 2.2/2.3) now apply per modulus, exactly as in their §4.

## 5. The anchor factor rides along

$A_{04}(p)$ is independent of $q_1,q_2,q_3$, so it is a fixed nonnegative weight
on the cube. It is **already controlled unconditionally** by the anchor energy
$\sum_pA_{04}(p)^2\ll H^2(\log X)^C$ ([[08 Anchor Energy and the Joint Obstruction]] §1).
The earlier C–S obstruction ([[08 Anchor Energy and the Joint Obstruction]] §2) was
for the *unaveraged* correlation; after cluster-seed averaging the cluster side
is the well-structured cube, and the anchor weight is handled either by its
$L^2$ bound or by an additional average over $q_0,q_4$. (Determining the cleanest
route is the next sub-step.)

## 6. Status

* **Resolved:** the transpose worry. Averaging over the cluster seeds
  $q_1,q_2,q_3$ (= SBEE averaging) turns the cluster count into a genuine cube
  $\sum_pA_{04}(p)\sum_{x_4}g(p,x_4)^3$, the exact FS third-moment structure, with
  each reciprocal sum single-modulus in the good regime.
* **Confirmed:** FS's §4 method (third moment → $S_q$ bounds → Cayley moment
  averaged) is now a genuine template, not just a toolbox.
* **New piece:** the anchor weight $A_{04}(p)$ (no FS analogue), controlled by
  [[08 Anchor Energy and the Joint Obstruction]].

## 7. Honest correction: the cube is *coupled* through $x_4$ (not the clean FS third moment)

Carrying out §4 explicitly reveals a residual feature absent from FS. Detecting
each $q_j\mid pa_j+q_4x_4$ with characters mod $q_j$ (frequencies $b_j$) gives, at
fixed $p$,

$$
\sum_{x_4}g(p,x_4)^3=\sum_{q_1,q_2,q_3\sim X}\frac1{q_1q_2q_3}\sum_{b_1,b_2,b_3}
\Big(\prod_{j}D_H\!\big(\tfrac{b_jp}{q_j}\big)\Big)\,D_H\!\Big(q_4\textstyle\sum_j\tfrac{b_j}{q_j}\Big),
$$

where $D_H(\theta)\ll\min(2H,\|\theta\|^{-1})$. FS's clean third moment
$\frac1q\sum_aS_q(a;x)^3$ uses **one** modulus and **one** dual variable $a$; here
the three $(b_j,q_j)$ are tied by the **shared variable $x_4$**, which produces the
extra factor $D_H(q_4\sum_jb_j/q_j)$. This factor is large only when

$$
\Big\|q_4\textstyle\sum_j\tfrac{b_j}{q_j}\Big\|\ \lesssim\ \tfrac1H,
$$

a near-vanishing **frequency-coupling condition** across the three moduli. There
is no FS analogue.

So the precise status: averaging gives a *cube* in $(a_j,q_j)$ (real progress,
the composite-modulus obstruction is gone), but with a coupling layer FS does not
have. The earlier "exact FS third-moment structure" (§3–§4 above) is an
overstatement — corrected here.

**Is the coupling benign?** Plausibly yes: it *restricts* the frequency triples
(fewer error terms, not more), and the diagonal $b_1=b_2=b_3=0$ gives the correct
main term $\asymp X^2/(\log X)^3$ at fixed $p$. The "exactly one $b_j\ne0$" strata
reduce to single-modulus sums (FS Theorem 3.3 territory); the "all $b_j\ne0$"
stratum is constrained by the coupling. But "plausibly benign" must be *proved*:
this coupling is the genuinely new analytic sub-problem, the current frontier.

## Next action

Analyze the frequency-coupling $\|q_4\sum_jb_j/q_j\|\lesssim1/H$: stratify the
error by $\#\{j:b_j\ne0\}$, bound the one- and two-nonzero strata by single/double
FS sums, and show the fully-coupled stratum is controlled (the coupling should
reduce its size). Quote FS Thm 3.3 / Lemma 2.3 as black boxes; compute only the
new coupling delta and the box-width ($H$) dependence.
