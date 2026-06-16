# Stratifying the Cube: Strata 0, 1 Done

Back to [[00 README]]. Prerequisite: [[15 The Cube Structure from Cluster-Seed Averaging]].

First **executed** piece of the FS adaptation (not a roadmap). At fixed prime
$p\sim X$ we compute the cube $\sum_{x_4}g(p,x_4)^3$ by stratifying the frequency
expansion of [[15 The Cube Structure from Cluster-Seed Averaging]] §7 according to
$s=\#\{j:b_j\ne0\}$. Target (the averaged cluster bound,
[[13 The Averaged Framing Is Essential]]): $\sum_{x_4}g^3\ll(\log X)^C\cdot X^2$ at
$H\asymp X^{1/2}$ (i.e. $\asymp H^4$ up to logs).

$$
\sum_{x_4}g(p,x_4)^3=\sum_{q_1,q_2,q_3\sim X}\frac1{q_1q_2q_3}\sum_{b_1,b_2,b_3}
\Big(\prod_j D_H(\tfrac{b_jp}{q_j})\Big)D_H\Big(q_4\textstyle\sum_j\tfrac{b_j}{q_j}\Big),
\quad D_H(\theta)=\!\!\sum_{0<|a|\le H}\!\!e(a\theta).
$$

## Stratum 0 ($b_1=b_2=b_3=0$): main term

All kernels $=2H$: $\sum_{q_1,q_2,q_3}\frac{(2H)^3}{q_1q_2q_3}\cdot2H
=(2H)^4\big(\sum_{q\sim X}\tfrac1q\big)^3\asymp (2H)^4(\log X)^{-3}\asymp X^2(\log X)^{-3}$
at $H\asymp X^{1/2}$. **On budget.**

## Stratum 1 (exactly one $b_j\ne0$): secondary main term, controlled

By symmetry take $b_1\ne0,\ b_2=b_3=0$ (×3). The $b_2,b_3=0$ kernels give $(2H)^2$;
the coupling kernel is $D_H(q_4b_1/q_1)$. The stratum is

$$
3\sum_{q_1,q_2,q_3}\frac{(2H)^2}{q_1q_2q_3}\,T_{\ne0}(q_1),\qquad
T_{\ne0}(q_1)=\sum_{b_1\ne0}D_H(\tfrac{b_1p}{q_1})D_H(\tfrac{q_4b_1}{q_1}).
$$

**The key identity.** By orthogonality,
$$
\sum_{b_1\bmod q_1}D_H(\tfrac{b_1p}{q_1})D_H(\tfrac{q_4b_1}{q_1})
=q_1\,\#\{(a,c)\in([-H,H]\setminus0)^2: q_1\mid pa+q_4c\},
$$
and subtracting the $b_1=0$ term $(2H)^2$,
$$
T_{\ne0}(q_1)=q_1\,\#\{(a,c): q_1\mid pa+q_4c\}-(2H)^2.
$$
The lattice count is $\frac{(2H)^2}{q_1}+O(1+H/\lambda_1(q_1))$ where
$\lambda_1(q_1)$ is the first minimum of $\{(a,c):pa+q_4c\equiv0\,(q_1)\}$
(this is the Lemma B lattice of [[09 Cluster Concentration and the Structured Family]]).
**The main part $(2H)^2$ cancels exactly**, leaving

$$
T_{\ne0}(q_1)\ll q_1\big(1+H/\lambda_1(q_1)\big).
$$

So stratum 1 $\ll (2H)^2(\log X)^{-2}\sum_{q_1\sim X}\big(1+H/\lambda_1(q_1)\big)$.

* The "$1$" gives $(2H)^2(\log X)^{-2}\cdot\tfrac{X}{\log X}\asymp X^2(\log X)^{-3}$:
  same order as stratum 0 — a legitimate **secondary main term, on budget**.
* The "$H/\lambda_1(q_1)$" is large only for **structured $q_1$** (small first
  minimum = short relation $q_1\mid q_4b+pe$, cf.
  [[09 Cluster Concentration and the Structured Family]]). Its average
  $\sum_{q_1\sim X}H/\lambda_1(q_1)$ is exactly an FS **Cayley-congruence moment**,
  controlled by Lemma 2.2/2.3 of [[14 Fouvry-Shparlinski Is the Template]]:
  $\sum_{q\sim Q}J_K(q)\ll(K^2Q+K^4)$. This keeps stratum 1 on budget on average.

**Conclusion:** strata 0 and 1 are on budget, the structured part controlled by
the FS Cayley moment. No new analytic input beyond FS is needed for them.

## Stratum 3 (all $b_j\ne0$): the crux — coupling is essential

Drop the coupling kernel (replace $D_H(q_4\sum b_j/q_j)$ by its max $2H$):
$$
2H\sum_{q_1,q_2,q_3}\frac1{q_1q_2q_3}\prod_j\Big(\sum_{b_j\ne0}D_H(\tfrac{b_jp}{q_j})\Big)
=2H\sum_{q_1,q_2,q_3}\frac{\prod_j(q_j-2H)}{q_1q_2q_3}\asymp 2H\Big(\tfrac{X}{\log X}\Big)^3,
$$
using $\sum_{b\ne0}D_H(bp/q)=q-2H$. At $H\asymp X^{1/2}$ this is $\asymp X^{7/2}(\log X)^{-3}$
— **over budget by $\asymp X^{3/2}$.**

Therefore the coupling kernel is **not optional**: it restricts the frequency
triples to $\|q_4\sum_jb_j/q_j\|\lesssim1/H$, and the genuine cancellation (FS
Theorem 3.1/3.3, single modulus $q_i\asymp X$, good regime) must recover the
deficit. Stratum 3 is where the $x_4$-coupling of
[[15 The Cube Structure from Cluster-Seed Averaging]] §7 and the FS reciprocal-sum
cancellation interact. **This is the remaining analytic core.**

(Stratum 2 — two $b_j\ne0$ — is intermediate: one factor cancels as in stratum 1,
the other carries a single-modulus FS sum; expected on budget, to be checked.)

## Status

* **Done, on budget:** stratum 0 (main), stratum 1 (secondary main; the $(2H)^2$
  cancellation is explicit, structured part = FS Cayley moment Lemma 2.3).
* **Crux identified and quantified:** stratum 3 is over budget by $\asymp X^{3/2}$
  without the coupling; the coupling restriction + FS Theorem 3.3 cancellation
  must close it. This is the genuine remaining computation.
* **To check:** stratum 2 (expected benign).

## Next action

Stratum 3: parametrize the coupling $\|q_4\sum_jb_j/q_j\|\lesssim1/H$ (clear
denominators: $q_2q_3b_1+q_1q_3b_2+q_1q_2b_3\equiv r\pmod{q_1q_2q_3}$, $|r|\lesssim
q_1q_2q_3/H$), and bound the constrained triple sum using FS Theorem 3.3 averaged
over one modulus with the other two frequencies as coefficients. Verify the
coupling saving + cancellation covers the $X^{3/2}$ deficit.
