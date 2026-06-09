# Next Work Plan

Back to [[00 README]].

## Immediate stance

Do not assign HA another broad task immediately. The formal interface is thick
enough. The next progress must be mathematical: prove or seriously decompose
the inverse incidence/correlation theorem.

## Task 1: diagonal ledger

Prove and record all seed-prime diagonal removals.

Known example:

$$
p=q_4,\qquad a_i=-x_4
$$

gives a large $B_{123}$ fibre but no nonzero $A_{04}$ contribution.

Check analogous cases $p=q_i$ and denominator-zero boundary cases. Each should
either vanish or enter an explicit diagonal ledger.

## Task 2: anchor-side energy

Use the determinant identity

$$
q_4\mid x_0y_4'-x_0'y_4
$$

to prove a clean $L^2$ estimate for $A_{04}$, with a strict-box version and a
logarithmically enlarged determinant-quotient version.

## Task 3: non-diagonal $B_{123}$ structure

Analyze the common-numerator side:

$$
p a_i+q_4x_4\equiv0\pmod {q_i}.
$$

The issue is simultaneous short rational representation of $p/q_4$ modulo
$q_1,q_2,q_3$ with common numerator $x_4$.

Look for either:

- a direct counting bound after removing $p=q_4$;
- an energy argument producing relations between the $q_i$;
- a Fourier/multilinear averaging proof.

## Task 4: inverse collision theorem

Prove the dichotomy:

$$
\sum_p A_{04}(p)B_{123}(p)
\gg
(\log X)^C\left(1+\frac{H^6}{X^3}\right)
$$

implies many factorable ternary relations

$$
q_i(x_i y_4)+q_0(x_0a_i)-q_4(x_4y_4+z_4a_i)=0.
$$

Then show those relations place the seed tuple in a low-entropy structured
family compatible with the FIE ledger.

## Task 5: stitch back upward

Once Task 4 is proved, return to:

1. residual-prime shell bound;
2. weighted primitive ray bound;
3. anchored cluster codegree bound;
4. SBEE/BCE global control;
5. Fourier positivity;
6. main theorem.

## Possible HA use

Good HA tasks:

- formalize diagonal-removal lemmas;
- formalize a proposed $A_{04}$ energy proof;
- formalize exact implications from many split-star relations to a specified
  low-entropy family, once the family is mathematically defined.

Bad HA tasks:

- "prove the theorem" without a new idea;
- repackage the same correlation interface under a new name;
- attempt Fourier analysis without precise lemmas.
