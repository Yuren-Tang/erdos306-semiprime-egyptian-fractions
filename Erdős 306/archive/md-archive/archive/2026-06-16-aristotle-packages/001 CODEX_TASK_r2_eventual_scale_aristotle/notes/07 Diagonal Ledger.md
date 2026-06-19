# Diagonal Ledger

Back to [[00 README]]. Prerequisite reading: [[02 Active Rational-Collision Problem]].

This note discharges **Task 1** of [[05 Next Work Plan]]: enumerate every
seed-prime degeneration of the correlation sum

$$
N_H=\sum_{p\in[X,2X]}A_{04}(p)\,B_{123}(p),
$$

classify each as *vanishing*, *removed-by-definition*, or *boundary*, and state
the exact reduced sum that the inverse theorem must control.

Conventions match the Lean objects in `SplitStarCorrelation.lean`:

$$
A_{04}(p)=\#\{(x_0,y_4): q_4\mid p\,y_4+q_0x_0\},\qquad
B_{123}(p)=\#\{(x_4,a_1,a_2,a_3): q_i\mid p\,a_i+q_4x_4\ (i=1,2,3)\},
$$

all short variables in $[-H,H]\setminus\{0\}$, seeds $q_0,\ldots,q_4$ distinct
primes $\asymp X$, height $H\le X^{1/2}(\log X)^A$, so that $2H<q_m$ for every
seed (each short interval meets each residue class mod $q_m$ at most once).

## The five seed-prime diagonals

### Cluster side: $p=q_1,q_2,q_3$ — vanishing

Take $p=q_1$. The $i=1$ congruence becomes

$$
q_1a_1+q_4x_4\equiv q_4x_4\equiv 0\pmod{q_1}.
$$

Since $q_4$ is invertible mod $q_1$ (distinct primes), $x_4\equiv 0\pmod{q_1}$,
and $|x_4|\le H<q_1$ forces $x_4=0$, which is excluded. Hence

$$
B_{123}(q_1)=B_{123}(q_2)=B_{123}(q_3)=0,
$$

and these three primes contribute nothing. **No hidden fibre.**

### Anchor side, harmless: $p=q_4$ — vanishing despite maximal $B$ fibre

This is the diagonal already flagged in [[02 Active Rational-Collision Problem]]
and [[04 Failure and Risk Ledger]]. With $p=q_4$:

* $A_{04}(q_4)$: $q_4y_4+q_0x_0\equiv q_0x_0\equiv 0\pmod{q_4}$ forces $x_0=0$,
  excluded, so $A_{04}(q_4)=0$.
* $B_{123}(q_4)$: each congruence gives $a_i\equiv -x_4\pmod{q_i}$, i.e.
  $a_i=-x_4$. The fibre $\{(x_4,-x_4,-x_4,-x_4):x_4\ne 0\}$ has the **maximal**
  size $2H$.

The product vanishes because the maximal $B$ fibre is multiplied by $A_{04}(q_4)=0$.
This is the textbook reason not to bound $B_{123}$ in isolation.

### Anchor side, dangerous: $p=q_0$ — NOT self-vanishing (sharpens the docs)

This case is **not** covered by the existing notes and does **not** vanish.
With $p=q_0$:

* $A_{04}(q_0)$: $q_0y_4+q_0x_0\equiv q_0(y_4+x_0)\equiv 0\pmod{q_4}$, and $q_0$
  invertible mod $q_4$ gives $y_4\equiv -x_0\pmod{q_4}$, i.e. $y_4=-x_0$. The
  **anti-diagonal** fibre $\{(x_0,-x_0):x_0\ne 0\}$ has size $2H$ — and unlike
  $p=q_4$ it survives, because $x_0\ne 0,\ y_4=-x_0\ne 0$ are both admissible.
* $B_{123}(q_0)$ is a generic triple reciprocal-image count and is **not**
  forced to zero.

So the contribution of $p=q_0$ is

$$
A_{04}(q_0)\,B_{123}(q_0)=2H\cdot B_{123}(q_0),
$$

which in the worst case ($B_{123}(q_0)$ up to its trivial maximum $2H$) reaches
$\asymp H^2\asymp X$ at the central scale $H\asymp X^{1/2}$. That **exceeds** the
target budget $(\log X)^C\!\left(1+H^6/X^3\right)$, which is only $(\log X)^C$ at
that scale.

**Consequence.** $p=q_0$ cannot be discarded by an internal vanishing argument.
It must be removed by the modelling constraint that the adjoined prime $p$ is
*new*, i.e. $p\notin\{q_0,\ldots,q_4\}$ (equivalently $p\nmid\mathcal Q$ with
$\mathcal Q=q_0q_1q_2q_3q_4$). This hypothesis is natural — in the Egyptian-
fraction construction $p$ indexes a fresh semiprime edge — but it was implicit;
it must be made explicit, because the bound is false without it.

> Action item upstream: confirm the edge-construction step never reuses a seed
> prime as the adjoined prime. The Lean `SplitCorrelationSet` lets $p$ range over
> an arbitrary `Finset P`; the reduced theorem should take $P\subseteq[X,2X]$
> with $P\cap\{q_0,\ldots,q_4\}=\varnothing$.

### Boundary cases: image $\equiv 0$ — excluded by the nonzero constraint

A short variable's reciprocal image hitting $0$ (e.g. $y_4\equiv 0\pmod{q_4}$ in
$A_{04}$, or $a_i\equiv 0\pmod{q_i}$ in $B_{123}$) requires the source variable
$\equiv 0$, hence $=0$ in the short range, which is already excluded. So there is
no separate denominator-zero locus to remove; the nonzero constraints on
$(x_0,x_4,y_4,a_1,a_2,a_3)$ absorb all of them.

## Reduced correlation sum

After the ledger, the only removal with nonzero cost is $p=q_0$ (cost
$\le 2H\cdot B_{123}(q_0)$, removed by definition); the other four seed primes
cost nothing. The theorem to prove is therefore the **reduced** statement

$$
\boxed{\;N_H'=\sum_{\substack{p\in[X,2X]\\ p\,\nmid\,\mathcal Q}}A_{04}(p)\,B_{123}(p)
\ll (\log X)^C\!\left(1+\frac{H^6}{X^3}\right)\quad\text{outside structured seeds.}\;}
$$

> Update: this per-tuple bound is in fact **false** for individual structured
> seed tuples; the correct target is the average over seed tuples. See
> [[13 The Averaged Framing Is Essential]]. The box below states the per-tuple
> shape; the provable statement is its seed-average.

On the reduced range every $p$ is coprime to all five seeds, so $A_{04}(p)$ and
$B_{123}(p)$ are genuine reciprocal-image box counts with invertible multipliers.
The maximal anchor fibre ($p=q_0$) and the maximal cluster fibre ($p=q_4$) are
both gone; what remains is the joint correlation studied in
[[08 Anchor Energy and the Joint Obstruction]].

## Lean status

The algebraic vanishing facts are one-line consequences of invertibility and
`anchor_collision_det_zero_of_small` (`SplitStarCorrelation.lean`). A clean HA
task is to formalize the four vanishing/removal lemmas and to re-state
`SplitCorrelation` over a prime set disjoint from the seeds. This is *good* HA
work in the sense of [[05 Next Work Plan]]: it formalizes a finished, precisely
specified mathematical fact and closes a real (previously implicit) gap.
