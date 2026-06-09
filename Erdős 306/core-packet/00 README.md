# Erdős 306 Core Packet

This is the current working entry point for the project.

The old folders remain available as archive/reference:

- `../conditional proof/`
- `../草稿區/`
- `../Aristotle/output-final_aristotle_*/`
- `../archive/`

Do not start from those folders unless a specific detail is needed. Start here.

## Current status

The project has a strong conditional and formal spine, but the theorem is not
proved unconditionally yet.

The latest Aristotle packages are useful because they closed many finite and
algebraic interfaces. The important boundary is:

$$
\text{finite/algebraic infrastructure: mostly formalized}
$$

but

$$
\text{inverse incidence / Fourier-analytic positivity: still open}.
$$

The active mathematical target is the rational-value collision theorem in
[[02 Active Rational-Collision Problem]].

## Read order

1. [[01 Minimal Proof Spine]]
2. [[02 Active Rational-Collision Problem]]
3. [[03 Lean Formalization Map]]
4. [[04 Failure and Risk Ledger]]
5. [[05 Next Work Plan]]
6. [[06 Archive Map]]

Lean-side work should use:

- [[lean/README]]

## One-sentence target

Prove that short rational-value collisions

$$
p
=
\frac{q_4z_4-q_0x_0}{y_4}
=
\frac{q_i x_i-q_4x_4}{a_i}
\qquad(1\le i\le3)
$$

occur only at the random scale, unless the seed primes lie in a low-height
structured family.
