# Aristotle prompt: primitive projective normalization

Copy this to Aristotle after `AnchoredDeterminantRank.lean`.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306
conditional proof.

This is an exact algebra task. It is **not** to prove asymptotic estimates,
entropy bounds, SBEE, or analytic number theory. The goal is to complete the
fixed-$p$ fibre cleanup after `AnchoredDeterminantRank.lean`.

Create a new file:

```text
RequestProject/PrimitiveProjectiveNormalization.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.AnchoredDeterminantRank
```

## Mathematical background

`AnchoredDeterminantRank.lean` proves that, in the small determinant range, two
anchored hits with the same residual prime are projectively proportional:

$$
x_i z_0=z_i x_0
\qquad(1\le i\le4).
$$

The next exact step is:

$$
\text{projectively proportional}
+\text{ primitive}
\Longrightarrow
\text{equal up to sign}.
$$

This removes fixed-$p$ multiplicity from the weighted anchored primitive
inverse theorem.

## Goal 1: five-coordinate primitive and Bezout shell

Define a five-coordinate primitive predicate:

```lean
def PrimitiveFiveRay (x0 x1 x2 x3 x4 : Int) : Prop :=
  ∀ d : Int, 1 < |d| ->
    (d ∣ x0 ∧ d ∣ x1 ∧ d ∣ x2 ∧ d ∣ x3 ∧ d ∣ x4) -> False
```

Also define a Bezout certificate:

```lean
def BezoutFive (x0 x1 x2 x3 x4 : Int) : Prop :=
  ∃ c0 c1 c2 c3 c4 : Int,
    c0*x0 + c1*x1 + c2*x2 + c3*x3 + c4*x4 = 1
```

If Mathlib's gcd API makes it easy, prove

```lean
theorem bezoutFive_of_primitiveFiveRay :
  PrimitiveFiveRay x0 x1 x2 x3 x4 ->
  BezoutFive x0 x1 x2 x3 x4
```

This is useful but optional. If it is API-heavy, keep `BezoutFive` as a
hypothesis in later theorems.

## Goal 2: projective proportionality gives divisibility

Using `SameRefProjective` from `AnchoredDeterminantRank.lean`, prove:

```lean
theorem x0_dvd_z0_of_sameRefProjective_of_bezout
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hbez : BezoutFive x0 x1 x2 x3 x4) :
    x0 ∣ z0
```

The paper proof is:

$$
1=\sum_i c_i x_i.
$$

Multiplying by $z_0$ and using $x_i z_0=z_i x_0$ gives

$$
z_0=x_0\sum_i c_i z_i.
$$

Also prove the symmetric theorem:

```lean
theorem z0_dvd_x0_of_sameRefProjective_of_bezout
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hbez : BezoutFive z0 z1 z2 z3 z4) :
    z0 ∣ x0
```

You may need a lemma that `SameRefProjective` is symmetric.

## Goal 3: mutual divisibility gives sign equality

Prove:

```lean
theorem eq_or_neg_of_mutual_dvd
    {a b : Int} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ∣ b) (hba : b ∣ a) :
    b = a ∨ b = -a
```

Any equivalent form using `|a| = |b|` is fine.

## Goal 4: projective primitive rays agree up to sign

Prove the main normalization theorem with Bezout hypotheses:

```lean
theorem sameRefProjective_eq_or_neg_of_bezout
    (hx0 : x0 ≠ 0) (hz0 : z0 ≠ 0)
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hbezx : BezoutFive x0 x1 x2 x3 x4)
    (hbezz : BezoutFive z0 z1 z2 z3 z4) :
    (z0 = x0 ∧ z1 = x1 ∧ z2 = x2 ∧ z3 = x3 ∧ z4 = x4)
    ∨
    (z0 = -x0 ∧ z1 = -x1 ∧ z2 = -x2 ∧ z3 = -x3 ∧ z4 = -x4)
```

The proof outline:

1. Goal 2 gives $x_0\mid z_0$ and $z_0\mid x_0$.
2. Goal 3 gives $z_0=x_0$ or $z_0=-x_0$.
3. Use projective equalities and $x_0\ne0$ to cancel $x_0$ and get all other
   coordinates.

## Goal 5: optional primitive predicate version

If Goal 1 succeeds in deriving Bezout from `PrimitiveFiveRay`, prove:

```lean
theorem sameRefProjective_eq_or_neg_of_primitive
    (hx0 : x0 ≠ 0) (hz0 : z0 ≠ 0)
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hprimx : PrimitiveFiveRay x0 x1 x2 x3 x4)
    (hprimz : PrimitiveFiveRay z0 z1 z2 z3 z4) :
    ...
```

If not, the Bezout version is already enough for the paper-side argument,
because primitive integer vectors can be represented by such certificates in
ordinary number theory.

## Goal 6: optional connection to determinant rank

Package the conclusion:

If `sameRefProjective_of_small_dets` gives `SameRefProjective`, and both rays
have Bezout certificates and nonzero reference coordinates, then the two rays
are equal up to sign.

This theorem can take a `TwoAnchoredHits` as input and reuse the coprimality and
small determinant hypotheses from `sameRefProjective_of_small_dets`.

## Expected result

- `RequestProject/PrimitiveProjectiveNormalization.lean` compiles with no
  `sorry`.
- Main goals are 1--4, with Goal 1's primitive-to-Bezout theorem optional if
  Mathlib's gcd API is inconvenient.
- No analytic estimates or SBEE.

Paper-side meaning:

$$
\text{one fixed-}p\text{ projective class}
\Longrightarrow
\text{one primitive ray up to sign}.
$$

Together with `AnchoredDeterminantRank.lean`, this shows that fixed-$p$
multiplicity is not the main remaining obstacle.
