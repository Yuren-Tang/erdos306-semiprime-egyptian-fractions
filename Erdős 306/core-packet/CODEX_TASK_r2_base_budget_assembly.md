# Codex Task: R2 Base-Budget Assembly

Work in:

```text
/Users/david/erdos-lean-build
```

## Goal

Create:

```lean
RequestProject/R2BaseBudgetAssembly.lean
```

Recommended import:

```lean
import RequestProject.R2BaseLoadUpper
import RequestProject.R2ComponentScaleCard
```

No `sorry`, `admit`, or new axioms.

Do not work on G5/G7/Phase C.  Do not modify thick upstream files.

## Context

`R2BaseLoadUpper.lean` introduced:

```lean
structure R2BaseLoadBudget (D : R2ConcreteData T b)
axiom dyadic_control_recipLoad_eventually_small
theorem exists_k0_controlLoad_lt
```

We now need a clean finite gadget-load bound and a constructor for
`R2BaseLoadBudget D`.

`R2ComponentScaleCard.lean` is now available and can be reused for
`gadgetEdges_ge_mul`, `gadgetEdges_card_le_product`, and related component
scale/cardinality facts.  Do not reprove those if importing them is enough.

## Desired Endpoints

### 1. Gadget reciprocal-load bound

Prove a pointwise lower-bound estimate:

```lean
lemma gadget_recip_le_of_lower_bounds
    {R S : Finset ℕ} {r0 s0 e : ℕ}
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s)
    (he : e ∈ gadgetEdges R S) :
    (1 : ℝ) / (e : ℝ) ≤ 1 / ((r0 * s0 : ℕ) : ℝ)
```

Then prove:

```lean
theorem gadget_recipLoad_le_card_div
    {R S : Finset ℕ} (r0 s0 : ℕ)
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s) :
    R2ConcreteData.recipLoad (gadgetEdges R S)
      ≤ ((R.card * S.card : ℕ) : ℝ) / ((r0 * s0 : ℕ) : ℝ)
```

Use `Finset.card_image_le` if needed.

### 2. Budget constructor from explicit component bounds

Prove:

```lean
def r2BaseLoadBudget_of_component_bounds
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (Cctrl Cgadget : ℝ)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl)
    (hgadget : R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget)
    (hsum : Cctrl + Cgadget < 3 / (2 * (b : ℝ))) :
    R2BaseLoadBudget D
```

### 3. Eventual constructor using the named control input

Prove a theorem of this form:

```lean
theorem exists_k0_baseLoadBudget_of_gadget_bound
    {T : Finset ℕ} {b : ℕ}
    (D0 : R2ConcreteData T b)
    (r0 s0 : ℕ)
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (Cgadget : ℝ)
    (hgap : Cgadget < 3 / (2 * (b : ℝ)))
    (hgadget_bound : ∀ D : R2ConcreteData T b,
      D.R = D0.R → D.S = D0.S →
      R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget) :
    ∃ k0min : ℕ, ∀ D : R2ConcreteData T b, k0min ≤ D.BS.k0 →
      D.R = D0.R → D.S = D0.S →
      R2BaseLoadBudget D
```

It is fine to use `ε = 3/(2b) - Cgadget`; include the needed positivity
hypothesis explicitly if Lean wants it, especially `0 < b`.

If this exact form is awkward, prove a close equivalent:

```lean
theorem baseLoadBudget_of_control_and_gadget
```

where the control bound is supplied as
`R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl`.

### 4. Concrete gadget-card constructor

If possible, combine the gadget card/load bound with an explicit inequality:

```lean
theorem baseLoadBudget_of_control_epsilon_and_gadget_scale
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (ε : ℝ) (r0 s0 : ℕ)
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ ε)
    (hRlow : ∀ r ∈ D.R, r0 ≤ r)
    (hSlow : ∀ s ∈ D.S, s0 ≤ s)
    (hsum :
      ε + ((D.R.card * D.S.card : ℕ) : ℝ) / ((r0 * s0 : ℕ) : ℝ)
        < 3 / (2 * (b : ℝ))) :
    R2BaseLoadBudget D
```

This is the most useful endpoint for the mainline: the control load is handled
by the named dyadic input, while the gadget load is handled by finite size/scale
data.

## Build

Build only the new target:

```bash
lake build RequestProject.R2BaseBudgetAssembly
```

Poll at minute scale; do not repeatedly build tiny edits.
