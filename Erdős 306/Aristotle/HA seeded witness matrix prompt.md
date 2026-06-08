# Aristotle prompt: seeded witness-matrix bookkeeping

Copy this to Aristotle after the two-core bookkeeping task, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306 conditional proof.

This task is **not** to prove SBEE, divisor-energy estimates, Fourier positivity, or any analytic number theory. It formalizes the finite bookkeeping shell for the seeded witness-matrix inverse inside the ambient-sensitive FIE route.

Create a new file:

```text
RequestProject/SeededWitnessMatrix.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.GeneralizedRankOne
import RequestProject.RankOneRigidity
```

If the previous task created `RequestProject/TwoCoreBookkeeping.lean`, you may import it too, but this prompt should remain meaningful without it.

## Goal 1: two-sided dependent-random-choice averaging

Work with finite sets:

```lean
Γ : Finset V
F₀ : Finset S₀
F₁ : Finset S₁
Adj₀ : V → S₀ → Prop
Adj₁ : V → S₁ → Prop
```

For a tuple of seeds `s₀ : Fin r → S₀` and `s₁ : Fin r → S₁`, define the common residual neighbourhood:

```lean
def commonResidual
    (Γ : Finset V) (Adj₀ : V → S₀ → Prop) (Adj₁ : V → S₁ → Prop)
    (s₀ : Fin r → S₀) (s₁ : Fin r → S₁) : Finset V :=
  Γ.filter (fun v => (∀ i, Adj₀ v (s₀ i)) ∧ (∀ i, Adj₁ v (s₁ i)))
```

You may instead use lists, vectors, `Finset.pi`, or another Mathlib-friendly tuple model.

Prove a division-free averaging theorem of the following type:

```lean
theorem exists_twoSided_commonResidual_large
    ...
    (hdeg₀ : ∀ v ∈ Γ, h₀ ≤ (F₀.filter (fun f => Adj₀ v f)).card)
    (hdeg₁ : ∀ v ∈ Γ, h₁ ≤ (F₁.filter (fun f => Adj₁ v f)).card) :
    ∃ (s₀ : Fin r → S₀) (s₁ : Fin r → S₁),
      Γ.card * h₀^r * h₁^r ≤
        (commonResidual Γ Adj₀ Adj₁ s₀ s₁).card * F₀.card^r * F₁.card^r
```

If this exact statement is hard, prove an equivalent or slightly weaker
division-free version. Repetition of seeds is allowed; this is why functions
`Fin r → Sᵢ` are acceptable.

Mathematical proof idea:

Count triples

```text
(v, s₀, s₁)
```

where `v ∈ Γ` and `v` is adjacent to every selected seed. Counting by `v` gives at least

$$
|\Gamma|h_0^r h_1^r.
$$

Counting by seed tuples gives

$$
\sum_{s_0,s_1} |\Gamma(s_0,s_1)|.
$$

Thus one tuple has at least the average.

This formalizes the finite DRC extraction:

$$
\text{many seed neighbours for every residual vertex}
\Longrightarrow
\text{fixed seed tuples with large common residual neighbourhood}.
$$

## Goal 2: witness matrix mixed defect

Define the mixed defect of a matrix:

```lean
def mixedDefect
    {R C G : Type*} [AddCommGroup G]
    (N : R → C → G) (r r' : R) (c c' : C) : G :=
  N r c - N r c' - N r' c + N r' c'
```

Prove the bridge to the generalized rank-one theorem:

```lean
theorem zero_mixedDefect_iff_rankOne
    {R C G : Type*} [AddCommGroup G] [Nonempty R] [Nonempty C]
    (N : R → C → G) :
    (∀ r r' c c', mixedDefect N r r' c c' = 0) ↔
    ∃ (a : R → G) (b : C → G), ∀ r c, N r c = a r + b c
```

This may be a direct wrapper around `mixedSecondZero_iff` from
`GeneralizedRankOne.lean`.

## Goal 3: paper-language aliases

Add aliases whose names match the draft:

```lean
def WitnessMatrix (R C G : Type*) := R → C → G

def ZeroRectangleDefect (N : R → C → G) : Prop :=
  ∀ r r' c c', mixedDefect N r r' c c' = 0

def AdditiveRankOne (N : R → C → G) : Prop :=
  ∃ (a : R → G) (b : C → G), ∀ r c, N r c = a r + b c
```

Then prove:

```lean
theorem zeroRectangleDefect_iff_additiveRankOne ...
```

## Expected result

- `RequestProject/SeededWitnessMatrix.lean` compiles with no `sorry`.
- Goal 1 is the most useful new finite bookkeeping lemma.
- Goals 2 and 3 should be straightforward wrappers around existing rank-one rigidity.
- Do not add SBEE or analytic assumptions.

The arithmetic statement still remains outside Lean:

$$
\text{nonzero witness-matrix defects produce SBEE energy}.
$$

This Lean task only formalizes the finite extraction and zero-defect structure.
