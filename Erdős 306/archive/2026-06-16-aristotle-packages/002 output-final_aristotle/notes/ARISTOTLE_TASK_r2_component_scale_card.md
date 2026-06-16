# Aristotle Task: R2 Component Scale/Cardinality Supplies

## Goal

Create a new Lean leaf:

```lean
RequestProject/R2ComponentScaleCard.lean
```

Recommended import:

```lean
import RequestProject.R2MassBatchReady
```

Build:

```bash
lake build RequestProject.R2ComponentScaleCard
```

No `sorry`, `admit`, or new axioms.

## Context

The base-load upper socket has been assigned elsewhere.  Do **not** work on
`D.baseLoad < 3/(2b)`, G5, G7, or Phase C.

This task is finite component bookkeeping feeding:

```lean
RequestProject/R2ComponentSupply.lean
RequestProject/R2ComponentNumericAssembly.lean
```

We need practical ways to supply:

```lean
R2ControlSupply.hctrledge
R2GadgetSupply.hgadgetedge
hcomponentCard :
  ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K
```

from simple lower-scale and cardinality assumptions.

## Desired Endpoints

Names can vary, but please try to prove these.

### 1. Control edge lower bound from bottom block scale

Every control edge has both prime factors in `blockSupport BS`, hence each
factor is at least `2^BS.k0`.  Prove:

```lean
lemma ctrlEdges_ge_k0_square
    (BS : BlockSystem) {e : ℕ} (he : e ∈ ctrlEdges BS) :
    2 ^ BS.k0 * 2 ^ BS.k0 ≤ e
```

Then prove the real scale wrapper:

```lean
theorem ctrlEdges_scale_of_k0_square
    (BS : BlockSystem) (N : ℤ) (ρ : ℝ)
    (hscale : (N : ℝ) ≤ ρ * ((2 ^ BS.k0 * 2 ^ BS.k0 : ℕ) : ℝ)) :
    ∀ e ∈ ctrlEdges BS, (N : ℝ) ≤ ρ * (e : ℝ)
```

If Lean needs it, include `0 ≤ ρ` as a hypothesis.

### 2. Gadget edge lower bound from component lower scales

For `gadgetEdges R S`, prove:

```lean
lemma gadgetEdges_ge_mul
    {R S : Finset ℕ} {r0 s0 e : ℕ}
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s)
    (he : e ∈ gadgetEdges R S) :
    r0 * s0 ≤ e
```

and the real scale wrapper:

```lean
theorem gadgetEdges_scale_of_mul
    {R S : Finset ℕ} (N : ℤ) (ρ : ℝ) (r0 s0 : ℕ)
    (hρ : 0 ≤ ρ)
    (hscale : (N : ℝ) ≤ ρ * ((r0 * s0 : ℕ) : ℝ))
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s) :
    ∀ e ∈ gadgetEdges R S, (N : ℝ) ≤ ρ * (e : ℝ)
```

### 3. Cardinality bounds

Prove:

```lean
lemma ctrlEdges_card_le_ctrlPairs_card (BS : BlockSystem) :
    (ctrlEdges BS).card ≤ (ctrlPairs BS).card
```

```lean
lemma gadgetEdges_card_le_product (R S : Finset ℕ) :
    (gadgetEdges R S).card ≤ R.card * S.card
```

Optional but useful:

```lean
lemma ctrlPairs_card_le_support_square (BS : BlockSystem) :
    (ctrlPairs BS).card ≤ (blockSupport BS).card * (blockSupport BS).card
```

using `ctrlPairs_mem_blockSupport`.

### 4. Packaged supply constructors

If feasible, add lightweight structures/constructors:

```lean
theorem r2ControlSupply_of_k0_square
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ)
    (hscale : (N : ℝ) ≤ ρ * ((2 ^ D.BS.k0 * 2 ^ D.BS.k0 : ℕ) : ℝ))
    (havoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T) :
    R2ControlSupply D N ρ
```

and similarly for gadget scale:

```lean
theorem r2GadgetSupply_of_mul_scale
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ)
    (r0 s0 : ℕ)
    ... :
    R2GadgetSupply D N ρ
```

The gadget constructor should keep the existing hypotheses explicit:
`hRprime`, `hSprime`, `hlt`, `hgadgetAvoid`, `hRdvd`, `hSblock`.

## Notes

Prefer small helper lemmas.  Do not modify thick upstream files unless absolutely
necessary.  If a statement is too ambitious, prove the strongest clean variant
and explain what changed.

