# Aristotle prompt: split-star correlation interface

Copy this to Aristotle after `ResidualPrimeShellCRT.lean`.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is an exact algebra and finite-counting interface task. It is **not** to
prove the final analytic correlation estimate. The goal is to formalize the
split-star interpretation of six-variable CRT interval hits and the exact
factorable ternary relations they produce.

Create a new file:

```text
RequestProject/SplitStarCorrelation.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.ResidualPrimeShellCRT
import RequestProject.ClusterLineIncidence
```

If `ClusterLineIncidence` names are inconvenient, do not depend on it; define
the needed relation predicates directly.

## Mathematical background

A six-variable CRT interval hit has variables

$$
(x_0,x_4,y_4,a_1,a_2,a_3)
$$

and congruences

$$
q_i\mid p a_i+q_4x_4\qquad(1\le i\le3),
$$

and

$$
q_4\mid p y_4+q_0x_0.
$$

Therefore one can reconstruct short integer coordinates

$$
x_i=\frac{p a_i+q_4x_4}{q_i}\qquad(1\le i\le3),
$$

and

$$
z_4=\frac{p y_4+q_0x_0}{q_4}.
$$

This gives a split anchored star:

$$
p a_i=q_i x_i-q_4x_4,
\qquad
p y_4=q_4z_4-q_0x_0.
$$

The original anchored ray is the diagonal subcase $z_4=x_4$.

Eliminating $p$ gives, for each $1\le i\le3$,

$$
q_i(x_i y_4)+q_0(x_0a_i)-q_4(x_4y_4+z_4a_i)=0.
$$

These are the factorable ternary relations which should become the structured
exception language.

## Goal 1: split-star structure and predicates

Define a structure:

```lean
structure SplitAnchoredStar where
  p q0 q1 q2 q3 q4 : Int
  x0 x4 z4 y4 a1 a2 a3 : Int
  x1 x2 x3 : Int
  h1 : p * a1 = q1 * x1 - q4 * x4
  h2 : p * a2 = q2 * x2 - q4 * x4
  h3 : p * a3 = q3 * x3 - q4 * x4
  h4 : p * y4 = q4 * z4 - q0 * x0
```

Also define a predicate version if it is easier to use in theorems.

## Goal 2: reconstruct split star from six-variable divisibility

Using `SixVarDivisibility` from `ResidualPrimeShellCRT.lean`, prove that
divisibility data reconstructs a `SplitAnchoredStar` by setting

$$
x_i=(p a_i+q_4x_4)/q_i,\qquad
z_4=(p y_4+q_0x_0)/q_4.
$$

Suggested theorem shape:

```lean
theorem splitAnchoredStar_of_sixVarDivisibility
    (hdiv : SixVarDivisibility p q0 q1 q2 q3 q4 D) :
    ∃ S : SplitAnchoredStar, ...
```

It is fine to package the equality of the fields to `D` explicitly or define a
constructor `splitStar_of_sixVarDivisibility`.

## Goal 3: split star gives six-variable divisibility

Prove the converse:

```lean
theorem sixVarDivisibility_of_splitAnchoredStar
    (S : SplitAnchoredStar) :
    SixVarDivisibility S.p S.q0 S.q1 S.q2 S.q3 S.q4
      { x0 := S.x0, x4 := S.x4, y4 := S.y4,
        a1 := S.a1, a2 := S.a2, a3 := S.a3 }
```

This is just divisibility from the defining equalities.

## Goal 4: diagonal bridge to anchored hits

Formalize that an actual anchored CRT hit gives a split star with $z_4=x_4$.

Conversely, a split star with $z_4=x_4$ gives the corresponding anchored
lattice equations:

$$
q_i x_i-q_4x_4=p a_i,\qquad
q_4x_4-q_0x_0=p y_4.
$$

Use `AnchoredCRTProductHit` or `InAnchoredCRTLattice`, whichever is easier with
the imported API.

## Goal 5: factorable ternary relations

Define a paper-facing predicate:

```lean
def SplitFactorableRelation
    (q0 q4 qi x0 x4 z4 y4 ai xi : Int) : Prop :=
  qi * (xi * y4) + q0 * (x0 * ai) - q4 * (x4 * y4 + z4 * ai) = 0
```

Prove:

```lean
theorem splitFactorableRelation_of_splitStar_1
    (S : SplitAnchoredStar) :
    SplitFactorableRelation S.q0 S.q4 S.q1 S.x0 S.x4 S.z4 S.y4 S.a1 S.x1
```

and similarly for indices 2 and 3.

The proof is the linear combination

$$
y_4\cdot h_i-a_i\cdot h_4.
$$

If useful, package all three into:

```lean
structure SplitFactorableShell ...
```

and prove:

```lean
theorem splitFactorableShell_of_splitStar (S : SplitAnchoredStar) :
  SplitFactorableShell S
```

## Goal 6: representation functions and correlation statement

Define finite-set representation functions in abstract form. For a finite
integer set `P` and bounds represented by finite sets `X0 Y4 X4 A1 A2 A3`,
define:

```lean
def A04 (q0 q4 p : Int) (X0 Y4 : Finset Int) : Nat := ...
def B123 (q1 q2 q3 q4 p : Int)
    (X4 A1 A2 A3 : Finset Int) : Nat := ...
```

where `A04` counts pairs satisfying

$$
p y_4+q_0x_0\equiv0\pmod {q_4},
$$

and `B123` counts quadruples satisfying the three congruences

$$
p a_i+q_4x_4\equiv0\pmod {q_i}.
$$

Then define the correlation sum:

```lean
def SplitCorrelation ... : Nat :=
  ∑ p in P, A04 q0 q4 p X0 Y4 * B123 q1 q2 q3 q4 p X4 A1 A2 A3
```

Prove the exact double-counting identity:

`SplitCorrelation` equals the cardinality of the finite set of six-tuples and
`p ∈ P` satisfying the four congruences.

This goal is finite bookkeeping only; no asymptotic bound is required.

## Optional Goal 7: anchor-side collision determinant

Formalize the exact algebra behind the easy side of the correlation.

If two short pairs represent the same anchor residue:

$$
p y+q_0x\equiv0\pmod {q_4},
\qquad
p y'+q_0x'\equiv0\pmod {q_4},
$$

then, assuming $\gcd(q_0,q_4)=1$,

$$
q_4\mid xy'-x'y.
$$

Suggested theorem shape:

```lean
theorem q4_dvd_anchor_collision_det
    (hc : IsCoprime q0 q4)
    (h1 : (p * y + q0 * x) ≡ 0 [ZMOD q4])
    (h2 : (p * y' + q0 * x') ≡ 0 [ZMOD q4]) :
    q4 ∣ x * y' - x' * y
```

If the exact theorem needs a nonzero/coprime variant, adapt it. A second
optional theorem can state that if $|xy'-x'y|<|q_4|$, then the determinant is
zero, using the existing integer divisibility smallness lemma if available.

## Expected result

- `RequestProject/SplitStarCorrelation.lean` compiles with no `sorry`.
- Main goals are 1--6; Goal 7 is optional but useful.
- No analytic estimates, no SBEE, no entropy theorem.

Paper-side meaning:

$$
\text{six-variable CRT hit}
\Longleftrightarrow
\text{split anchored star}
\Longrightarrow
\text{three factorable ternary relations}.
$$

The file should also expose the exact correlation object

$$
\sum_p A_{04}(p)B_{123}(p),
$$

which is now the remaining analytic/inverse theorem.
