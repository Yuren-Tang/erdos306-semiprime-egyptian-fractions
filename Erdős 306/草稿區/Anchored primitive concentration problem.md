# Anchored primitive concentration problem

Back to [[Reciprocal cluster cover proof draft]] and [[CP 02 The single remaining condition]].

This note isolates the current smallest arithmetic problem.

The short answer is:

$$
\boxed{
\text{yes, the problem is now mostly isolated, but only after keeping the
structured-exception outlet.}
}
$$

The isolated object is a five-prime anchored short-kernel count. The surrounding
FIE machinery is still needed to pay the structured alternatives.

---

# 1. Exact isolated count

Fix distinct seed primes

$$
q_0,q_1,q_2,q_3,q_4\sim X
$$

and a short scale

$$
M\le X^{1/2}(\log X)^A.
$$

For a short vector

$$
\mathbf x=(x_0,x_1,x_2,x_3,x_4),
\qquad
0<|x_i|\le M,
$$

put

$$
n_i(\mathbf x)=q_i x_i-q_0x_0
\qquad(1\le i\le4).
$$

The anchored primitive concentration count is

$$
\mathcal R(q_0,\ldots,q_4;M)
=
\#\left\{
\mathbf x:
\gcd(x_0,x_1,x_2,x_3,x_4)=1,\
\exists p\in[X,2X]\cap\mathbb P,\
p\mid n_i(\mathbf x)\ (1\le i\le4)
\right\}.
$$

Since

$$
|n_i(\mathbf x)|\ll XM
$$

and $M<X$, each $n_i$ has at most one prime divisor in $[X,2X]$, up to harmless
endpoint constants. Thus a primitive short vector usually determines its
residual prime $p$.

The desired pointwise statement is:

$$
\mathcal R(q_0,\ldots,q_4;M)\ll(\log X)^C
$$

unless the seed tuple lies in a low-entropy structured family.

---

# 2. Why this is not quite standalone

The HA cluster-selection pipeline counts clusters indexed by $(p,x_0)$, not
only primitive rays. If a primitive anchored ray

$$
(x_0,x_1,x_2,x_3,x_4;y_1,y_2,y_3,y_4)
$$

has height

$$
H=\max_i\{|x_i|,|y_i|\},
$$

then every scalar multiple $\lambda$ with

$$
|\lambda|H\le M
$$

gives another legal anchored cluster through the same seed tuple. Hence one
primitive ray contributes up to

$$
\left\lfloor\frac{M}{H}\right\rfloor
$$

cluster-codegree hits.

Therefore the truly useful theorem is a weighted primitive statement:

$$
\sum_{\text{primitive anchored rays }r}
\frac{M}{H(r)}
\ll(\log X)^C
$$

outside structured exceptions.

Equivalently, one may prove:

1. primitive rays of height $H\ge M(\log X)^{-C}$ are polylogarithmically many;
2. primitive rays of height $H<M(\log X)^{-C}$ force a low-height rational
   structure and are charged to the FIE exception ledger.

This is why the problem is isolated but not free-floating. The isolated
arithmetic theorem must remember how small primitive rays are paid.

---

# 3. Determinant rank test for one residual prime

There is a useful exact test for the fixed-$p$ fibre.

Suppose two anchored short vectors

$$
\mathbf x=(x_0,x_1,x_2,x_3,x_4),
\qquad
\mathbf z=(z_0,z_1,z_2,z_3,z_4)
$$

both satisfy

$$
q_i x_i-q_0x_0=p\,y_i,
\qquad
q_i z_i-q_0z_0=p\,w_i.
$$

Multiply the first equation by $z_0$ and the second by $x_0$, then subtract.
For each $i$:

$$
q_i(x_i z_0-z_i x_0)
=
p(y_i z_0-w_i x_0).
$$

Since $p\ne q_i$, this gives

$$
p\mid x_i z_0-z_i x_0.
$$

But

$$
|x_i z_0-z_i x_0|\le 2M^2.
$$

Thus, in the stricter central box $2M^2<p$, one has

$$
x_i z_0=z_i x_0
\qquad(1\le i\le4).
$$

So all solutions in the fixed-$p$ short box are projectively proportional to
the reference coordinate. In particular, the fixed-$p$ fibre has essentially one
primitive ray, up to sign and zero-edge exceptions.

This is a real structural gain. In the logarithmically enlarged range
$M\le X^{1/2}(\log X)^A$, the determinant may be nonzero, but then the same
display says that $p$ divides a very small determinant. Nonzero determinants
are therefore themselves chargeable arithmetic structure.

## 3.1 After `AnchoredDeterminantRank.lean`

Aristotle has now formalized this fixed-$p$ rank test.

The file `AnchoredDeterminantRank.lean` proves:

1. for two anchored hits with the same $p,q_0,q_1,\ldots,q_4$,
   $$
   q_i(x_i z_0-z_i x_0)=p(y_i z_0-w_i x_0);
   $$
2. if $p$ is coprime to $q_i$, then
   $$
   p\mid x_i z_0-z_i x_0;
   $$
3. if moreover
   $$
   |x_i z_0-z_i x_0|<|p|
   $$
   for every $i$, then the two rays are projectively proportional:
   $$
   x_i z_0=z_i x_0
   \qquad(1\le i\le4);
   $$
4. every anchored witness gives all six factorable ternary relations
   $$
   q_i x_i y_j-q_j x_j y_i+q_0x_0(y_i-y_j)=0.
   $$

Thus the fixed-$p$ fibre is no longer mysterious. It is controlled by the
dichotomy

$$
\text{projective class}
\quad\text{or}\quad
\text{small determinant quotient }k_i=\frac{x_i z_0-z_i x_0}{p}.
$$

In the strict box $2M^2<p$, only the projective class remains. In the
logarithmically enlarged central range, the non-projective case has

$$
|k_i|\ll\frac{M^2}{X},
$$

which is only polylogarithmic. This should be treated as a structured
determinant quotient, not as random entropy.

One exact algebraic step remains before the fixed-$p$ fibre is fully clean:
projective proportionality plus primitivity should imply equality up to sign.
This is a Bezout/gcd normalization lemma for five integer coordinates.

---

# 4. Inter-prime inverse relation

For a single anchored ray, write

$$
q_i x_i-q_0x_0=p\,y_i.
$$

Eliminating $p$ between $i$ and $j$ gives

$$
y_j(q_i x_i-q_0x_0)
-
y_i(q_j x_j-q_0x_0)
=0,
$$

or

$$
q_i x_i y_j-q_j x_j y_i+q_0x_0(y_i-y_j)=0.
$$

This is a ternary linear relation among the seed primes with factorable short
coefficients. A large supply of primitive anchored rays therefore yields many
relations of the form

$$
A_i q_i+A_j q_j+A_0q_0=0,
\qquad
A_i=x_i y_j,\quad A_j=-x_jy_i,\quad A_0=x_0(y_i-y_j),
$$

where the coefficients have factorable height $O(M^2)$.

This is the natural structured-exception language:

$$
\text{many anchored rays}
\Longrightarrow
\text{many short factorable ternary relations among seed primes}.
$$

The remaining hard step is to turn this into a low-entropy family statement
compatible with the FIE ledger.

---

# 5. Relation to known tools

The nearby literature on modular hyperbolas, short products, reciprocal sets,
and incomplete Kloosterman sums is relevant but does not appear to give a
black-box theorem in exactly this form.

The closest directions are:

- product congruences with variables from short intervals, such as
  Bourgain--Garaev--Konyagin--Shparlinski,
  [arXiv:1203.0017](https://arxiv.org/abs/1203.0017);
- incomplete Kloosterman sums and short modular inverses, such as
  Browning--Haynes, [arXiv:1204.6374](https://arxiv.org/abs/1204.6374);
- additive properties of reciprocal intervals and multilinear Kloosterman
  sums, such as Bourgain--Garaev,
  [arXiv:1211.4184](https://arxiv.org/abs/1211.4184).

These tools study short intervals modulo a fixed prime or reciprocal/product
sets in a finite field. Our problem has a moving residual prime $p$, fixed seed
primes $q_i$, and needs an inverse/exception statement rather than only an
average upper bound. They are guidance, not an immediate substitute for the
anchored primitive theorem.

---

# 6. Current best formulation

The next theorem to prove should be:

**Weighted anchored primitive inverse theorem.**
Let $q_0,\ldots,q_4\sim X$ be distinct primes and
$M\le X^{1/2}(\log X)^A$. Then either

$$
\sum_{r}
\frac{M}{H(r)}
\ll(\log X)^C,
$$

where $r$ ranges over primitive anchored rays and $H(r)$ is their short height,
or the seed tuple $(q_0,\ldots,q_4)$ satisfies many short factorable ternary
relations and hence belongs to a low-entropy rational structured family.

This theorem is exactly the arithmetic input needed by
`AnchoredSelectionPipeline.lean`.

---

# 7. Immediate sublemmas

The next proof should try to establish:

1. **Fixed-$p$ projective rank lemma.** Two fixed-$p$ anchored rays either are
   projectively proportional, or $p$ divides a nonzero determinant
   $x_i z_0-z_i x_0$ of size $O(M^2)$.
2. **Projective primitive normalization lemma.** If two five-coordinate
   primitive rays satisfy
   $$
   x_i z_0=z_i x_0
   \qquad(1\le i\le4),
   $$
   and $x_0,z_0\ne0$, then the two vectors are equal up to sign. Equivalently,
   one projective class contributes only a sign pair after primitive
   normalization.
3. **Small-height exception lemma.** A primitive ray with height
   $H<M(\log X)^{-C}$ puts the seed tuple inside an explicitly encodable
   family
   $$
   q_i=\frac{q_0x_0+p\,y_i}{x_i}.
   $$
4. **Many-rays inverse lemma.** Many primitive rays of comparable height force
   many factorable ternary relations; these relations imply low entropy unless
   the seed tuple is already near the rank-one / near-dominant exit.

The first item has now been handed to Aristotle and closed. The second item is
the next exact algebra task. The third and fourth are the real paper-side
arithmetic tasks.
