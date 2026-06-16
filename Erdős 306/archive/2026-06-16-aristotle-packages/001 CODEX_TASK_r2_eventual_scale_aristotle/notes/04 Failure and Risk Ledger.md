# Failure and Risk Ledger

Back to [[00 README]].

This file records traps we should not re-enter.

## False decompositions

**Abstract Bernoulli subset sum is false.**

Weights with gcd $1$ and a feasible Bernoulli target do not guarantee an exact
subset. Example:

$$
w=(3,5),\qquad m=4.
$$

No subset of $\{3,5\}$ sums to $4$.

**Exceed-then-extract is false.**

Having total reciprocal mass above the target does not imply an exact sub-sum.
Example:

$$
E=\{6,10\},\qquad b=5,\qquad \frac16+\frac1{10}=\frac4{15}>\frac15,
$$

but no subset sums to $1/5$.

## Misleading "unconditional proof" label

The Aristotle file `Erdos306Unconditional.lean` is useful, but it is not an
unconditional proof. It has one remaining theorem-level sorry:

$$
\texttt{fourier\_positivity\_unconditional}.
$$

That sorry is essentially the full Fourier-positive extraction theorem.

## Naive separate bound for $B_{123}$

Do not try to bound $B_{123}$ in isolation and multiply by a crude $A$ bound.
The diagonal

$$
p=q_4,\qquad a_i=-x_4
$$

creates a large $B_{123}$ fibre. It vanishes only after multiplying by the
anchor side $A_{04}$.

This is now quantitative (see [[08 Anchor Energy and the Joint Obstruction]]):
on the reduced range, $\sum_p A_{04}\asymp X/\log X$ but $\sum_p B_{123}\asymp 1$
at $H\asymp X^{1/2}$, so Cauchy–Schwarz gives $N_H'\gg X^{1/2}(\log X)^{-1/2}$,
overshooting the target $(\log X)^C$ by a factor $\asymp X^{1/2}$. **Any
factorization of the correlation fails.** The correlation must be evaluated
jointly.

## The $p=q_0$ anchor diagonal (previously implicit)

Beyond $p=q_4$, the prime $p=q_0$ also produces a maximal anchor fibre
(anti-diagonal $y_4=-x_0$, size $2H$), but unlike $p=q_4$ it does **not**
self-vanish: its contribution $2H\cdot B_{123}(q_0)$ can reach $\asymp X$ at the
central scale. It must be removed by the hypothesis that the adjoined prime is
new, $p\notin\{q_0,\ldots,q_4\}$. See [[07 Diagonal Ledger]]. The reduced sum
$N_H'$ is over $p\nmid\mathcal Q$, and the bound is false without this exclusion.

## One-line Fourier estimate risk

At the central scale $H\asymp X^{1/2}$, incomplete reciprocal sums are at
square-root length. Standard completion plus Weil does not obviously supply the
needed saving. A successful Fourier proof must use the full multilinear
structure or produce an inverse theorem.

## Fragmentation risk

The project became large because many true local interfaces were formalized.
This is useful only if we keep the root theorem in view:

$$
\sum_p A_{04}(p)B_{123}(p)
\ll
(\log X)^C\left(1+\frac{H^6}{X^3}\right)
$$

outside low-entropy structure.

Further HA work should be assigned only when it directly supports this theorem.
