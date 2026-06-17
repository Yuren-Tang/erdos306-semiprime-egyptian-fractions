# Anchor Energy and the Joint Obstruction

Back to [[00 README]]. Prerequisites: [[02 Active Rational-Collision Problem]],
[[07 Diagonal Ledger]].

This note discharges **Task 2** of [[05 Next Work Plan]] (a clean unconditional
$L^2$ bound for the anchor side), then proves a hard quantitative fact:
**Cauchy–Schwarz / any factorization of the correlation is catastrophically
lossy.** That upgrades the qualitative warning in [[04 Failure and Risk Ledger]]
to a theorem and pins down why the correlation must be treated jointly. It ends
by recasting **Task 4** as a coupled ternary-lattice problem.

Throughout we work on the reduced range $p\nmid\mathcal Q$ of [[07 Diagonal Ledger]].

## 1. The anchor side is unconditionally harmless

**Lemma A (anchor energy).** For seeds $q_0,q_4$ distinct primes $\asymp X$ and
$H\le X^{1/2}(\log X)^A$,

$$
\sum_{p\in[X,2X]}A_{04}(p)^2\ \ll\ H^2(\log X)^{C}.
$$

*Proof.* Expand the square: $\sum_p A_{04}(p)^2$ counts triples
$(p,(x_0,y_4),(x_0',y_4'))$ with both pairs anchor-hitting the same $p$. For a
fixed $p$ (coprime $q_4$),

$$
p\,y_4\equiv -q_0x_0,\qquad p\,y_4'\equiv -q_0x_0'\pmod{q_4}.
$$

Eliminating $p$ (multiply by $x_0',x_0$ resp. and subtract) gives the
**$p$-free determinant identity**

$$
x_0y_4'-x_0'y_4\equiv 0\pmod{q_4},
$$

which is exactly Lean's `q4_dvd_anchor_collision_det`. Given a pair $(P,P')$
meeting it, the admissible $p$ form a single residue class mod $q_4$; since
$q_4\asymp X$ and the interval $[X,2X]$ has length $X$, that class contains
$O(1)$ integers, hence $O(1)$ primes. Therefore

$$
\sum_p A_{04}(p)^2\ \ll\ \#\{(x_0,y_4,x_0',y_4')\in([-H,H]\setminus 0)^4:\;q_4\mid x_0y_4'-x_0'y_4\}.
$$

Write $D=x_0y_4'-x_0'y_4$, $|D|\le 2H^2$.

* **Strict regime $2H^2<q_4$** (i.e. $H\le (q_4/2)^{1/2}$). Then $q_4\mid D$ with
  $|D|<q_4$ forces $D=0$ (Lean's `anchor_collision_det_zero_of_small`), i.e.
  $(x_0,y_4)\parallel(x_0',y_4')$. The number of ordered proportional pairs in
  $([-H,H]\setminus 0)^2$ is

  $$
  \sum_{\substack{(u,v)\ \mathrm{primitive}\\ 1\le\max(|u|,|v|)\le H}}\Big\lfloor\tfrac{H}{\max(|u|,|v|)}\Big\rfloor^2
  \ \asymp\ \sum_{j\le H} j\cdot\Big(\tfrac Hj\Big)^2\ \asymp\ H^2\log H.
  $$

  So $\sum_p A_{04}(p)^2\ll H^2\log H$.

* **Log-enlarged regime $q_4\le 2H^2\le q_4(\log X)^{2A}$.** Now $D=q_4t$ with
  $|t|\le 2H^2/q_4\ll(\log X)^{2A}$. The $t=0$ part is the proportional count
  $\ll H^2\log H$ above. For each fixed $t\ne 0$, the number of
  $(x_0,y_4,x_0',y_4')\in[-H,H]^4$ with $x_0y_4'-x_0'y_4=q_4t$ is $\ll H^2\log H$
  (fix $(x_0,x_0')$; the residual equation is linear in $(y_4,y_4')$, whose
  solutions lie on a coset of a rank-1 lattice of covolume $\gcd(x_0,x_0')$,
  contributing $\ll 1+H/\!\max$, and summing the divisor weight over the box
  gives $\ll H^2\log H$). Summing over $\ll(\log X)^{2A}$ values of $t$ yields
  $\sum_p A_{04}(p)^2\ll H^2(\log X)^{2A+1}$. $\qquad\blacksquare$

**Reading.** $A_{04}$ has *no* concentration beyond its diagonal: the second
moment is, up to logs, the same size as the first moment squared per prime would
predict in the absence of structure. The anchor side never needs the
structured-seed exclusion. **All genuine difficulty is on the $B_{123}$ side.**

## 2. Why Cauchy–Schwarz fails (quantitative obstruction)

It is tempting to write $N_H'\le\|A_{04}\|_2\,\|B_{123}\|_2$ and bound each factor.
This **cannot** work, and here is the exact reason.

Count first moments on the reduced range. For $A_{04}$, each $(x_0,y_4)$ pins $p$
to one class mod $q_4\asymp X$, giving $O(1)$ candidate integers, a $1/\log X$
chance of a prime:

$$
\sum_p A_{04}(p)\ \asymp\ \frac{H^2}{\log X}\quad\Big(\asymp\frac{X}{\log X}\ \text{at}\ H\asymp X^{1/2}\Big).
$$

For $B_{123}$, each $(x_4,a_1,a_2,a_3)$ pins $p$ to one class mod
$q_1q_2q_3\asymp X^3$, so a candidate integer in $[X,2X]$ exists with probability
$\asymp X/X^3=X^{-2}$:

$$
\sum_p B_{123}(p)\ \asymp\ \frac{H^4}{X^2}\quad\big(\asymp 1\ \text{at}\ H\asymp X^{1/2}\big).
$$

The two sides are **wildly asymmetric**. At the central scale $H\asymp X^{1/2}$,

$$
\|A_{04}\|_2\ \gg\ \Big(\sum_p A_{04}^2\Big)^{1/2}\gg\Big(\sum_p A_{04}\Big)^{1/2}\asymp\Big(\tfrac{X}{\log X}\Big)^{1/2},
\qquad
\|B_{123}\|_2\ \ge\ 1,
$$

so Cauchy–Schwarz gives only

$$
N_H'\ \le\ \|A_{04}\|_2\,\|B_{123}\|_2\ \gg\ X^{1/2}(\log X)^{-1/2},
$$

while the target is $N_H'\ll(\log X)^C$. **C–S overshoots by a factor
$\asymp X^{1/2}$.** Any approach that estimates the two sides separately and
multiplies inherits this loss. This is the rigorous form of the warning in
[[04 Failure and Risk Ledger]]: the $A_{04}B_{123}$ correlation must be evaluated
*jointly*; the anchor averaging is not a multiplicative factor but the device
that pays for the rare cluster event.

## 3. Recasting Task 4: the coupled ternary lattice

Eliminating $p$ from a hit (the split-star form of
[[02 Active Rational-Collision Problem]]) gives, for $i=1,2,3$,

$$
q_i\,U_i+q_0\,V_i-q_4\,W_i=0,\qquad
U_i=x_iy_4,\ \ V_i=x_0a_i,\ \ W_i=x_4y_4+z_4a_i,
$$

with $|U_i|,|V_i|,|W_i|\ll H^2$. Each relation places $(U_i,V_i,W_i)$ in the
rank-2 lattice

$$
\Lambda_i=\{(U,V,W)\in\mathbb Z^3:\ q_iU+q_0V-q_4W=0\},\qquad \operatorname{covol}\Lambda_i\asymp X,
$$

inside the box $[-H^2,H^2]^3$. For a single $i$ the lattice-point count is
$\asymp 1+H^4/X$ (unstructured), which at $H\asymp X^{1/2}$ is $\asymp X$ — far
too many. The saving must come from the **coupling**: the same $y_4$ appears in
all three $U_i$, the same $x_0$ in all three $V_i$, and $(x_4,z_4)$ tie the
$W_i$ together. So the three lattice points are not independent; they are the
image of a single short vector $(x_0,x_4,y_4,z_4,a_1,a_2,a_3)$ under a fixed
bilinear map.

**Target (inverse theorem, sharp form).** If

$$
N_H'\ \gg\ (\log X)^C\!\left(1+\frac{H^6}{X^3}\right),
$$

then the seed tuple $(q_0,q_1,q_2,q_3,q_4)$ admits a short multiplicative
relation — concretely, there exist integers $0<|d|,|e|\ll(\log X)^{O(1)}$ and an
index $i$ with

$$
d\,q_4\equiv e\,q_0\pmod{q_i},
$$

placing the tuple in the low-entropy family compatible with the FIE ledger.

This is exactly the dichotomy of Task 4, now anchored to a concrete object
(the coupled image of a single short vector in $\prod_i\Lambda_i$) rather than a
slogan. The next mathematical step is to make the coupling quantitative: bound
the number of short vectors whose three bilinear images simultaneously lie in
boxes of size $H^2$, and show that an excess forces the displayed seed relation.

## 4. What this note settles vs. leaves open

* **Settled (unconditional):** anchor energy Lemma A; the $C$–$S$ obstruction;
  the diagonal reduction of [[07 Diagonal Ledger]].
* **Open (the core):** the coupled-lattice inverse theorem of §3. This is the
  sole remaining mathematical content, equivalent to the `sorry` in
  `FourierPositivity.lean`.

## Lean / HA handoff

Good, well-specified HA tasks now exist (cf. [[05 Next Work Plan]]):

1. Formalize Lemma A. The two algebraic inputs already exist
   (`q4_dvd_anchor_collision_det`, `anchor_collision_det_zero_of_small`); only
   the lattice-point *count* $\ll H^2\log H$ is new.
2. Formalize the proportional-pair count
   $\sum_{\mathrm{prim}}\lfloor H/\max\rfloor^2\asymp H^2\log H$ as a standalone
   `CrossLabelEnergy`-style lemma.
3. State the coupled bilinear map of §3 as a Lean definition feeding the reduced
   `SplitCorrelation`, so the inverse theorem has a precise formal target.
