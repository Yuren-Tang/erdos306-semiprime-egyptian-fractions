# Aristotle Task: R2 mass-batch from assembled base-budget

Work in the Lean project.  Create one thin downstream file:

```lean
RequestProject/R2MassBatchBaseBudgetReady.lean
```

Imports:

```lean
import RequestProject.R2MassBatchBaseLoadBudget
import RequestProject.R2BaseBudgetAssembly
```

## Goal

Combine the existing eventual mass-batch theorem with the new base-budget
assembly theorem.  Do not work on G5, G7, Phase C, minor support, or the
control analytic estimate itself.

Prove a theorem with this shape, adjusting names only if Lean requires:

```lean
theorem exists_massBatchSupply_of_gadget_scale_eventual
    {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k0min : ℕ, ∀ (D : R2ConcreteData T b), k0min ≤ D.BS.k0 →
      (∀ r ∈ D.R, Nat.Prime r) →
      (∀ r ∈ D.R, r ∉ blockSupport D.BS) →
      blockPrimes D.BS.k0 ⊆ blockSupport D.BS →
      ∀ r0 s0 : ℕ, 0 < r0 → 0 < s0 →
        (∀ r ∈ D.R, r0 ≤ r) →
        (∀ s ∈ D.S, s0 ≤ s) →
        (ε + ((D.R.card * D.S.card : ℕ) : ℝ) /
            ((r0 * s0 : ℕ) : ℝ) < 3 / (2 * (b : ℝ))) →
        ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ D.BS.k0 →
          ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q))
```

## Proof plan

Use:

```lean
exists_massBatchSupply_of_baseLoadBudget_eventual
exists_k0_controlLoad_lt
baseLoadBudget_of_control_epsilon_and_gadget_scale
```

Take `k0min := max k0mass k0ctrl`, where:

- `k0mass` comes from `exists_massBatchSupply_of_baseLoadBudget_eventual hb`;
- `k0ctrl` comes from `exists_k0_controlLoad_lt ε hε`.

Given `D` and `hk : max k0mass k0ctrl ≤ D.BS.k0`, derive:

```lean
have hk_mass : k0mass ≤ D.BS.k0 := le_trans (Nat.le_max_left _ _) hk
have hk_ctrl : k0ctrl ≤ D.BS.k0 := le_trans (Nat.le_max_right _ _) hk
```

Then build:

```lean
have B : R2BaseLoadBudget D :=
  baseLoadBudget_of_control_epsilon_and_gadget_scale D ε r0 s0
    hr0 hs0 (hctrl D.BS hk_ctrl) hRlow hSlow hsum
```

Finally apply:

```lean
hmass D hk_mass hRprime hRout hsub B
```

## Constraints

- No `sorry`, `admit`, or new axioms.
- Keep this file thin; do not edit thick upstream files.
- Preferred check:

```bash
lake build RequestProject.R2MassBatchBaseBudgetReady
```

Report exact theorem names and build status.
