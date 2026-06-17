# Minimal Proof Spine

Back to [[00 README]].

## Final theorem

For every positive rational number $a/b$ with squarefree $b$, there should be a
finite representation

$$
\frac ab=\sum_{n\in S}\frac1n,
$$

where the $n$ are distinct squarefree semiprimes.

The squarefree denominator condition is necessary.

## Formal skeleton

The Lean project has a clean skeleton:

1. reduce $a/b$ to enough disjoint representations of $1/b$;
2. construct semiprime edge sets avoiding any finite obstruction set;
3. use Fourier positivity to extract an exact subset sum;
4. conclude the main theorem.

The newest Aristotle package isolates this as:

$$
\texttt{erdos\_306}
\Leftarrow
\texttt{fourier\_positivity\_unconditional}.
$$

The latter is still a `sorry`; it is the main theorem-level analytic gap, not a
minor Lean API issue.

## Current mathematical reduction

Our working route does not try to formalize all Fourier analysis at once.
Instead it isolates the arithmetic input needed for the minor-arc/global-control
step.

The current endpoint is:

**Residual-prime shell inverse theorem.** For distinct seed primes
$q_0,\ldots,q_4\asymp X$ and height $H\le X^{1/2}(\log X)^A$, the number of
nondegenerate short shell hits is

$$
\ll
(\log X)^C\left(1+\frac{H^6}{X^3}\right),
$$

unless the seed tuple belongs to a low-height structured family.

This shell theorem feeds the anchored primitive concentration statement, which
feeds the cluster-cover/FIE ledger, which feeds the SBEE/BCE global control
condition, which feeds Fourier positivity.

## What is already closed

- Fixed-$p$ determinant rank obstruction.
- Primitive projective normalization up to global sign.
- Anchored CRT lattice interface.
- Six-variable CRT shell interface.
- Split-star factorable shell.
- Exact correlation identity
  $$
  N_H=\sum_p A_{04}(p)B_{123}(p).
  $$
- Anchor-side collision determinant.

## What remains

The real remaining theorem is an inverse incidence/correlation statement:

$$
\sum_{p\in[X,2X]} A_{04}(p)B_{123}(p)
\ll
(\log X)^C\left(1+\frac{H^6}{X^3}\right),
$$

outside structured seed families.
