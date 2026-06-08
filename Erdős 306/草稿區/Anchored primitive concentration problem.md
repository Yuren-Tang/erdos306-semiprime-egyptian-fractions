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

## 3.2 Stronger all-coordinate determinant

There is a stronger determinant identity that should be used in the paper proof.

Let

$$
Q_0=q_0,\qquad Q_i=q_i\quad(1\le i\le4).
$$

For any two fixed-$p$ anchored solutions $\mathbf x,\mathbf z$, the congruences

$$
Q_i x_i\equiv q_0x_0\pmod p,
\qquad
Q_i z_i\equiv q_0z_0\pmod p
$$

imply, for all $0\le i<j\le4$,

$$
p\mid x_i z_j-z_i x_j,
$$

provided $p$ is coprime to $Q_iQ_j$. Indeed,

$$
Q_iQ_j(x_i z_j-z_i x_j)\equiv0\pmod p.
$$

This matters because one should not always use the reference coordinate $x_0$
as the denominator. If $x_0$ is small, choose a coordinate $j$ of a primitive
base ray with

$$
|z_j|=\max_i|z_i|.
$$

Then every other ray in the same fixed-$p$ fibre has small determinant
quotients

$$
k_i=\frac{x_i z_j-z_i x_j}{p},
\qquad
|k_i|\ll\frac{H^2}{X}
$$

on a dyadic height shell $H\le \max_i|x_i|,\max_i|z_i|\le2H$.

Using a Bezout certificate for the primitive base ray,

$$
\sum_i c_i z_i=1,
$$

the congruences

$$
x_i z_j-z_i x_j=p\,k_i
$$

force $x_j$ into one residue class modulo $z_j$:

$$
x_j\equiv -p\sum_i c_i k_i\pmod {z_j}.
$$

Since $|z_j|\asymp H$, there are only $O(1)$ possible $x_j$ for each tuple
$(k_i)$. Therefore a fixed-$p$, fixed-height shell contains at most

$$
O\left(\left(1+\frac{H^2}{X}\right)^4\right)
$$

primitive rays, up to harmless constants and signs.

This is a real forward step. It says that fixed-$p$ multiplicity is polylog in
the central range. The main remaining problem is no longer the number of rays
over one $p$, but the number of residual primes $p$ which admit even one
primitive ray in a given height shell.

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
- geometric sieve methods of Poonen--Stoll / Ekedahl / Bhargava, especially
  Bhargava's
  [arXiv:1402.0031](https://arxiv.org/abs/1402.0031);
- high-dimensional inverse sieve philosophy, such as the inverse sieve problem
  in high dimensions by Helfgott--Venkatesh.

These tools study short intervals modulo a fixed prime or reciprocal/product
sets in a finite field. Our problem has a moving residual prime $p$, fixed seed
primes $q_i$, and needs an inverse/exception statement rather than only an
average upper bound. The geometric-sieve viewpoint is particularly apt because
the condition

$$
q_i x_i-q_0x_0\equiv0\pmod p
\qquad(1\le i\le4)
$$

cuts out a codimension-$4$ line in $\mathbb A^5_{\mathbb F_p}$. However, the
line moves with $p$ and with the seed tuple, so the needed theorem is an
inverse geometric sieve for moving rational lines, not the standard
density-tail theorem.

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

After the fixed-$p$ determinant analysis, it is better to state the remaining
part in height shells:

**Residual-prime shell inverse theorem.**
For each dyadic height $H\le M$, let

$$
\mathcal P_H(q_0,\ldots,q_4)
$$

be the set of residual primes $p\sim X$ admitting at least one primitive
anchored ray of height in $[H,2H]$. Then either

$$
\sum_H \frac{M}{H}
\left(1+\frac{H^2}{X}\right)^4
|\mathcal P_H(q_0,\ldots,q_4)|
\ll(\log X)^C,
$$

or the seed tuple belongs to a low-entropy structured family.

The determinant-rank lemma proves the factor

$$
\left(1+\frac{H^2}{X}\right)^4
$$

inside each fixed-$p$ fibre. The hard theorem is now the inverse bound for
$|\mathcal P_H|$.

---

# 7. Six-variable CRT interval form

The most useful next reformulation uses the anchored coordinate $y_4$ and the
three differences

$$
a_i=y_i-y_4\qquad(1\le i\le3).
$$

Starting from an anchored ray,

$$
q_i x_i-q_0x_0=p\,y_i\qquad(1\le i\le4),
$$

subtract the fourth equation. This gives

$$
q_i x_i-q_4x_4=p\,a_i\qquad(1\le i\le3),
$$

and the fourth anchored equation is

$$
q_4x_4-q_0x_0=p\,y_4.
$$

If all short $x$-coordinates are nonzero and $H<\min q_i$, then
$a_i\ne0$ and $y_4\ne0$. For example, $a_i=0$ would give
$q_i x_i=q_4x_4$, impossible for distinct primes $q_i,q_4$ and
$0<|x_i|,|x_4|<q_i,q_4$. Thus these denominators are invertible modulo the
corresponding seed primes.

Consequently every nondegenerate ray gives the four local congruences

$$
p\equiv -q_4x_4a_i^{-1}\pmod {q_i}
\qquad(1\le i\le3),
$$

and

$$
p\equiv -q_0x_0y_4^{-1}\pmod {q_4}.
$$

Let

$$
Q=q_1q_2q_3q_4.
$$

For every short six-tuple

$$
(x_0,x_4,y_4,a_1,a_2,a_3),
\qquad
0<|x_0|,|x_4|,|y_4|,|a_i|\le H,
$$

let $R(x_0,x_4,y_4,a_1,a_2,a_3)$ be the unique residue modulo $Q$ satisfying
the four congruences above. The remaining arithmetic theorem can therefore be
stated as a short CRT interval estimate:

$$
\#\left\{
(x_0,x_4,y_4,a_1,a_2,a_3):
R(x_0,x_4,y_4,a_1,a_2,a_3)\in[X,2X]
\right\}
\ll
(\log X)^C\left(1+\frac{H^6}{X^3}\right),
$$

outside low-entropy structured seed families, with the usual small-height
exception ledger.

This is the right scale. The domain has size $O(H^6)$, the modulus is
$Q\asymp X^4$, and the target interval has length $X$, so the random main term
is

$$
\frac{H^6X}{X^4}=\frac{H^6}{X^3}.
$$

At the central scale $H\le X^{1/2}(\log X)^A$, this is polylogarithmic. Thus the
problem is not to beat a power of $X$ by force; it is to prove that the CRT
residue map does not concentrate in the tiny interval $[X,2X]$ unless the seed
tuple has low-height rational structure.

This six-variable form is sharper than the five-$x$ gcd-energy count because it
restores the missing denominator variables which the congruence description had
hidden.

---

# 8. Split-star form and correlation target

The six-variable CRT interval hit has an exact integer interpretation. From

$$
p\equiv -q_4x_4a_i^{-1}\pmod {q_i}
$$

and

$$
p\equiv -q_0x_0y_4^{-1}\pmod {q_4},
$$

define reconstructed coordinates

$$
x_i=\frac{pa_i+q_4x_4}{q_i}\qquad(1\le i\le3),
$$

and

$$
z_4=\frac{py_4+q_0x_0}{q_4}.
$$

Since $p,q_i,q_4\asymp X$ and all six input variables have height $H$, these
reconstructed coordinates have height $O(H)$. Thus a six-variable interval hit
is the same as a **split anchored star**

$$
pa_i=q_i x_i-q_4x_4\qquad(1\le i\le3),
$$

and

$$
py_4=q_4z_4-q_0x_0.
$$

The original anchored ray is the diagonal subcase $z_4=x_4$. The split form is
larger, but it is algebraically cleaner.

Eliminating $p$ between the $i$-th spoke and the anchor spoke gives

$$
y_4(q_i x_i-q_4x_4)
=
a_i(q_4z_4-q_0x_0),
$$

or

$$
q_i(x_i y_4)
+q_0(x_0a_i)
-q_4(x_4y_4+z_4a_i)
=0.
$$

So every split-star hit gives three short factorable ternary relations among

$$
q_0,\ q_4,\ q_i.
$$

This is a more precise structured-exception mechanism than the earlier
five-$x$ gcd-energy language.

There is also a useful analytic decomposition. For a height shell $H$, define

$$
A_{04}(p)
=
\#\left\{
(x_0,y_4):
0<|x_0|,|y_4|\le H,\
p y_4+q_0x_0\equiv0\pmod {q_4}
\right\},
$$

and

$$
B_{123}(p)
=
\#\left\{
(x_4,a_1,a_2,a_3):
0<|x_4|,|a_i|\le H,\
p a_i+q_4x_4\equiv0\pmod {q_i}\ (1\le i\le3)
\right\}.
$$

Then the six-variable interval count is exactly

$$
N_H(q_0,\ldots,q_4)
=
\sum_{p\in[X,2X]\cap\mathbb Z}
A_{04}(p)B_{123}(p),
$$

with primality of $p$ irrelevant for an upper bound.

Heuristically,

$$
\sum_p A_{04}(p)\asymp H^2,
\qquad
\sum_p B_{123}(p)\asymp \frac{H^4}{X^2},
$$

and the expected correlation is

$$
N_H\asymp \frac{H^6}{X^3}.
$$

The next genuine theorem is therefore not just a pointwise CRT statement, but a
short-ratio correlation bound:

$$
\sum_{p\in[X,2X]}A_{04}(p)B_{123}(p)
\ll
(\log X)^C\left(1+\frac{H^6}{X^3}\right),
$$

unless the seed tuple has low-height rational structure.

This target has the right diagnostic behaviour. Large fibres of $A_{04}$ mean
that $p/q_0$ has many short representatives modulo $q_4$. Large fibres of
$B_{123}$ mean that the same $p/q_4$ has simultaneous short representatives
modulo $q_1,q_2,q_3$ with a common numerator $x_4$. Persistent correlation
between these two events is exactly the structure that should feed the
factorable ternary-relation ledger above.

The $A_{04}$ side by itself is already close to harmless. If two pairs
$(x_0,y_4)$ and $(x_0',y_4')$ represent the same residue $p$, then

$$
p y_4+q_0x_0\equiv0\pmod {q_4},
\qquad
p y_4'+q_0x_0'\equiv0\pmod {q_4}
$$

imply

$$
q_4\mid x_0y_4'-x_0'y_4.
$$

In the strict range $2H^2<q_4$, this forces

$$
x_0y_4'=x_0'y_4,
$$

so the collision is only a scalar collision of one rational number. Hence

$$
\sum_{r\bmod q_4}A_{04}(r)^2\ll H^2\log H
$$

by the standard count of scalar multiples of primitive pairs. In the
logarithmically enlarged range, the same determinant quotient

$$
\frac{x_0y_4'-x_0'y_4}{q_4}
$$

is only polylogarithmically large and should be charged to the same structured
determinant ledger used for fixed-$p$ fibres.

Thus the truly new arithmetic difficulty is the three-modulus common-numerator
side $B_{123}$ and its correlation with $A_{04}$, not a generic failure of
short rational representation on the anchor side.

---

# 9. Immediate sublemmas

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
3. **CRT interval reduction lemma.** A nondegenerate primitive anchored ray in a
   height shell maps injectively up to harmless signs/constants to a short
   six-tuple
   $$
   (x_0,x_4,y_4,a_1,a_2,a_3)
   $$
   whose CRT residue lies in $[X,2X]$.
4. **Split-star factorable shell lemma.** A six-variable CRT interval hit
   reconstructs a short split anchored star and hence three short factorable
   ternary relations
   $$
   q_i(x_i y_4)+q_0(x_0a_i)-q_4(x_4y_4+z_4a_i)=0.
   $$
5. **Correlation inverse lemma.** The short-ratio correlation
   $$
   \sum_p A_{04}(p)B_{123}(p)
   $$
   is polylogarithmic unless these factorable ternary relations occupy a
   low-entropy structured family.
6. **Small-height exception lemma.** A primitive ray with height
   $H<M(\log X)^{-C}$ puts the seed tuple inside an explicitly encodable
   family
   $$
   q_i=\frac{q_0x_0+p\,y_i}{x_i}.
   $$
7. **Many-rays inverse lemma.** Many primitive rays of comparable height force
   many factorable ternary relations; these relations imply low entropy unless
   the seed tuple is already near the rank-one / near-dominant exit.

The first item has now been handed to Aristotle and closed. The second item is
also closed by `PrimitiveProjectiveNormalization.lean`, modulo importing the
new package into the workspace. The third item is closed in the latest
Aristotle report via `ResidualPrimeShellCRT.lean`, modulo importing the package.
The fourth item is the next useful exact-algebra interface. The fifth, sixth,
and seventh are the real paper-side arithmetic tasks, with the fifth now the
sharpest target.
