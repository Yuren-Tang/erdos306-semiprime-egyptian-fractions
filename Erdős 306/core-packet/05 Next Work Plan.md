# Next Work Plan

Back to [[00 README]].

## Immediate stance

Do not assign HA another broad task immediately. The formal interface is thick
enough. The next progress must be mathematical: prove or seriously decompose
the inverse incidence/correlation theorem.

## Task 1: diagonal ledger — DONE

See [[07 Diagonal Ledger]]. Result: $p=q_1,q_2,q_3$ give $B_{123}=0$; $p=q_4$
gives $A_{04}=0$ (killing the maximal $B$ fibre); $p=q_0$ does **not** vanish and
must be removed by the new-prime hypothesis $p\nmid\mathcal Q$; boundary cases
are absorbed by the nonzero constraints. The theorem is now the reduced sum
$N_H'$ over $p\nmid\mathcal Q$.

## Task 2: anchor-side energy — DONE

See [[08 Anchor Energy and the Joint Obstruction]] §1. Result:
$\sum_p A_{04}(p)^2\ll H^2(\log X)^C$ unconditionally, strict and log-enlarged
regimes, via the $p$-free determinant identity. The anchor side is harmless; all
difficulty is on $B_{123}$. §2 proves Cauchy–Schwarz overshoots by $X^{1/2}$, so
the correlation must be handled jointly.

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

## Task 4: inverse collision theorem — THE CORE (open)

Now framed concretely in [[08 Anchor Energy and the Joint Obstruction]] §3 as a
**coupled ternary-lattice** problem. A hit sends a single short vector
$(x_0,x_4,y_4,z_4,a_1,a_2,a_3)$ to three points

$$
(U_i,V_i,W_i)=(x_iy_4,\ x_0a_i,\ x_4y_4+z_4a_i)\in\Lambda_i,\quad
\Lambda_i=\{q_iU+q_0V-q_4W=0\},\ \operatorname{covol}\asymp X,
$$

in the box $[-H^2,H^2]^3$. The unstructured single-$i$ count $\asymp 1+H^4/X$ is
too large; the saving must come from the shared variables coupling the three
images. Target dichotomy: an excess

$$
N_H'\gg(\log X)^C\left(1+\frac{H^6}{X^3}\right)
$$

forces a short seed relation $d\,q_4\equiv e\,q_0\pmod{q_i}$ with
$|d|,|e|\ll(\log X)^{O(1)}$, placing the tuple in the low-entropy family.

Next concrete sub-step: make the coupling quantitative — bound the number of
short vectors whose three bilinear images simultaneously lie in $H^2$-boxes.

**Partial progress** in [[09 Cluster Concentration and the Structured Family]]:
proved Lemma B ($B_{123}(p)\ll\min_i(1+H/\lambda_1^{(i)}(p)+H^2/q_i)$ by geometry
of numbers) and Lemma C ($B_{123}(p)\ge2\Rightarrow$ short simultaneous relation
$q_i\mid q_4\delta+p\epsilon_i$). The structured family is now explicit: primes
$p$ with short relations $q_i\mid q_4b+pe$ for all $i$. The sole remaining piece
is a one-sided counting estimate: bound the generic anchor mass $A_{04}$ on the
thin set $\{p:B_{123}(p)\ge1\}$ (size $\ll H^4/X^2$).

**Reduced to a named analytic input** in [[10 Kloosterman Reduction of the Correlation]]:
an additive-character expansion of the anchor side recovers the target main term
$\asymp H^6/(X^3\log X)$ **unconditionally**, and isolates the error as Irving's
reciprocal prime sum $S_q(a;x)=\sum_{p\sim x}e(a\bar p/q)$ in the regime
$x\asymp q\asymp X$ — inside the nontrivial Garaev/Irving range $x\ge q^{3/4}$.
The two remaining ingredients are: (1) cluster first moment
$M_B=\sum_p B_{123}(p)\ll(\log X)^C(1+H^4/X^2)$ (self-contained); (2) the
power-saving reciprocal-sum bound (Irving), vacuous on the structured family.
The barrier is now a concrete literature input, not an open analytic mystery.

**Finish roadmap fully mapped** in [[11 Irving Toolbox and the Finish Roadmap]]:
the spare power that Weil alone lacks comes from the bilinear decomposition of
the prime indicator (Vaughan) + Irving's reciprocal moment, beating DFI exactly
at $x\asymp q$. Crucially, the bound should be proved **on average over the seed
primes** — that average is precisely the SBEE prime-block averaging, which is why
SBEE cites Irving. Concrete steps: Vaughan-decompose the $p$-sum → Irving Type
I/II bilinear bounds → sum dual frequencies $h_i\ll X^{1/2}$. Next action: the
Type I / $M_B$ bookkeeping, then Type II.

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
