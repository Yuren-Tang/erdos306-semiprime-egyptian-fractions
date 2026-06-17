# The First Moment Is Trivial (Correction)

Back to [[00 README]]. This note corrects [[14 Fouvry-Shparlinski Is the Template]],
[[15 The Cube Structure from Cluster-Seed Averaging]], [[16 Stratifying the Cube - Strata 0,1 Done]].

While attempting stratum 3 of [[16 Stratifying the Cube - Strata 0,1 Done]] on the
**frequency side**, switching to the **spatial side** revealed that the
first-moment (cluster-averaged) bound is **trivial** — the elaborate
cube/Vaughan/FS machinery of notes 14–16 is *unnecessary* for it. An honest
correction.

## 1. The trivial bound

Fix $p,q_0,q_4$. For each $i$, $M_i:=pa_i+q_4x_4$ has size $\le 4XH\asymp X^{3/2}$
(since $|a_i|,|x_4|\le H\le X^{1/2}(\log X)^A$). **An integer $\le X^{3/2}$ has at
most one prime factor $\ge X$** (two would give a product $\ge X^2$). Primes
$q_i\sim X$ satisfy $q_i\ge X$, so

$$
\#\{q_i\sim X\ \text{prime}: q_i\mid M_i\}\le 1\qquad(M_i\ne0,\ \text{forced since }x_4\ne0).
$$

Therefore, summing the cluster count over the three cluster seeds,

$$
\sum_{q_1,q_2,q_3\sim X}B_{123}(p)
=\sum_{(x_4,\vec a)}\prod_{i=1}^3\#\{q_i\mid M_i\}
\ \le\ \#\{(x_4,\vec a)\}=(2H+1)^4\ \asymp\ H^4.
$$

(The true size is $\asymp H^4(\log X)^{-3}$ — the probability all three $M_i$ have
a prime factor $\sim X$ — but the trivial $\le(2H+1)^4$ already suffices.)

## 2. The cluster-averaged correlation, for free

Since $A_{04}(p)$ is independent of $q_1,q_2,q_3$ and $\sum_pA_{04}(p)\ll H^2$
([[08 Anchor Energy and the Joint Obstruction]]),

$$
\sum_{q_1,q_2,q_3\sim X}N_H'=\sum_pA_{04}(p)\sum_{q_1,q_2,q_3}B_{123}(p)
\ \ll\ H^4\sum_pA_{04}(p)\ \ll\ H^6.
$$

Dividing by the number of cluster triples $\asymp(X/\log X)^3$, the **average of
$N_H'$ over cluster seeds** is

$$
\frac{1}{\#}\sum_{q_1,q_2,q_3}N_H'\ \ll\ \frac{H^6}{(X/\log X)^3}\ \asymp\ (\log X)^3\quad(\text{at }H\asymp X^{1/2}),
$$

which matches the per-tuple target $(\log X)^C(1+H^6/X^3)\asymp(\log X)^C$.
**Verified exponent check:** the $X$-power of the per-tuple average is $0$, equal
to the target's. So the first-moment bound is in budget across $H\le X^{1/2}(\log X)^A$.

## 3. What this means (and the honest correction)

* The **first moment over cluster seeds is trivial**, via "a short form has $\le1$
  large prime factor." Notes [[15 The Cube Structure from Cluster-Seed Averaging]]
  and [[16 Stratifying the Cube - Strata 0,1 Done]] expanded the same object on
  the frequency side and ran into the $x_4$-coupling and an $X^{3/2}$ "deficit" —
  that difficulty is an **artifact of the frequency expansion**, not intrinsic.
  On the spatial side it evaporates. (Notes 15–16 are not wrong, just an
  unnecessarily hard route to a trivial bound.)
* By **Markov**, the trivial first moment gives: for all but a
  $\ll(\log X)^{-D}$-fraction of cluster-seed triples, $N_H'\ll(\log X)^{C+D}(1+H^6/X^3)$.
  So the structured family ([[09 Cluster Concentration and the Structured Family]])
  is at worst **log-thin**, unconditionally and elementarily.

## 4. The real question: what strength does SBEE need?

Everything now hinges on a question that must be answered from the SBEE /
Fourier-positivity requirements (archived `CP 01`–`CP 03`, `SBEE.lean`):

> Does the global construction tolerate excluding a $(\log X)^{-D}$-thin set of
> seed configurations, or does it need the correlation bound to hold off only a
> **power-thin** ($X^{-\delta}$) exceptional set (or pointwise, or in variance)?

* **If log-thin suffices:** the active correlation target is **essentially done**
  (this note), and the remaining work is entirely on the SBEE-reduction side, not
  analytic. The FS apparatus (notes 11–16) is then *not needed*.
* **If power-thin / variance is needed:** the first moment is insufficient, and
  FS's strength is exactly the point — their Theorem 1.5 ($\ll\tilde\pi^3\mathcal
  L^{-B}$, arbitrary log saving) and Corollary 3.4 (power-saving control of
  $(\eta,x)$-bad moduli, $\ll Qx^{-\eta/2}$) deliver power-thin exceptional sets.
  Then notes 11–16 become relevant — but via FS's *variance* bound (second moment
  of the count over $q$), not the first moment.

## 5. Status and next action

* **Established (elementary, unconditional):** the cluster-averaged first moment
  of $N_H'$ is in budget; the structured family is log-thin.
* **Pivotal next step (not analytic):** read the archived SBEE requirement
  (`../Aristotle/output-final_aristotle_*/CP 01`–`CP 03`, `SBEE.lean`
  `ConditionSBEE`) to determine whether log-thin control suffices. This decides
  whether the analytic gap is essentially closed or whether FS-strength
  (power-thin, via the second moment) is genuinely required.
* Only if power-thin is needed do we return to a *second-moment* version of
  notes 14–16 (now with FS's Lemma 2.3 / Cor 3.4 doing real work).

This is the most important branch point in the project: it may show the active
correlation target is already met (modulo SBEE bookkeeping), or pinpoint the
exact stronger statement still required.
