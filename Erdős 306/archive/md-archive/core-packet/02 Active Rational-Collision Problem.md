# Active Rational-Collision Problem

Back to [[00 README]].

## Variables

Fix distinct seed primes

$$
q_0,q_1,q_2,q_3,q_4\asymp X
$$

and a height

$$
H\le X^{1/2}(\log X)^A.
$$

The active six short variables are

$$
(x_0,x_4,y_4,a_1,a_2,a_3),
\qquad
0<|x_0|,|x_4|,|y_4|,|a_i|\le H.
$$

## Correlation form

Define

$$
A_{04}(p)
=
\#\{(x_0,y_4):p y_4+q_0x_0\equiv0\pmod {q_4}\},
$$

and

$$
B_{123}(p)
=
\#\{(x_4,a_1,a_2,a_3):
p a_i+q_4x_4\equiv0\pmod {q_i}\ (1\le i\le3)\}.
$$

The six-variable shell count is exactly

$$
N_H(q_0,\ldots,q_4)
=
\sum_{p\in[X,2X]}A_{04}(p)B_{123}(p).
$$

The expected size is

$$
1+\frac{H^6}{X^3}.
$$

## Split-star form

A six-variable hit reconstructs a split anchored star:

$$
p a_i=q_i x_i-q_4x_4
\qquad(1\le i\le3),
$$

and

$$
p y_4=q_4z_4-q_0x_0.
$$

Equivalently,

$$
p
=
\frac{q_4z_4-q_0x_0}{y_4}
=
\frac{q_i x_i-q_4x_4}{a_i}
\qquad(1\le i\le3).
$$

This rational-value collision is the central object.

## Structured alternative

Eliminating $p$ gives, for each $i=1,2,3$,

$$
q_i(x_i y_4)+q_0(x_0a_i)-q_4(x_4y_4+z_4a_i)=0.
$$

Many hits should therefore force many short factorable ternary relations among

$$
q_0,\ q_4,\ q_i.
$$

The desired inverse theorem is:

$$
\text{many rational-value collisions}
\Longrightarrow
\text{low-entropy seed structure}.
$$

## Important diagnostics

The $A_{04}$ side is close to harmless. Two anchor representations for the same
residue imply

$$
q_4\mid x_0y_4'-x_0'y_4.
$$

In the strict range $2H^2<q_4$, this determinant vanishes; in the logarithmic
range it is a controlled small determinant quotient.

Do not estimate $B_{123}$ alone. There is a seed-prime diagonal

$$
p=q_4,\qquad a_1=a_2=a_3=-x_4,
$$

which creates a large $B_{123}$ fibre but contributes nothing to the full
correlation because the anchor congruence then forces $x_0=0$.

## Fourier diagnostic

A direct character expansion modulo $Q=q_1q_2q_3q_4$ gives incomplete reciprocal
sums at square-root length:

$$
\sum_{0<|x|,|y|\le H} e_q(cxy^{-1}).
$$

At $H\asymp X^{1/2}$, completion plus Weil alone has no obvious spare power.
Any Fourier route must exploit multilinear averaging or prove an inverse
statement for concentration.
