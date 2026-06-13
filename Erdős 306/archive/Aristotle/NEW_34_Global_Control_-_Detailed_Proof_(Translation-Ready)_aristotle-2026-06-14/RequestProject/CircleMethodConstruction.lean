import RequestProject.SemiprimeInfinity

open Finset BigOperators Classical

noncomputable section

namespace CircleMethodConstruction

/-!
# Circle-method edge construction (note 35 §C1)

This file isolates the deterministic C1 construction used by the circle-method
layer.  The target package is: for squarefree `b ≥ 2` and a finite obstruction
set `T`, choose semiprime edge denominators avoiding `T`, Bernoulli weights in
`[1/3, 2/3]`, and a common period `L` such that the weighted reciprocal mass is
exactly `1 / b` and the total load is below `L`.

The audited paper construction uses high-scale control/gadget edges at
`θ = 1/2`, then greedy high-scale semiprime batches with a common
`θ_H = Δ / W_H ∈ [1/3, 1/2]` to tune the mass exactly.  The availability of
large dyadic prime blocks is the Chebyshev/Bertrand input mentioned in note
35 §C1 and note 24.
-/

/-- A Chebyshev-style dyadic prime density input, stated as a local Prop so a
future proof can either discharge it from Mathlib or replace the named C1
construction `sorry` below by an explicit hypothesis-driven proof. -/
def chebyshev_block_density : Prop :=
  ∃ x0 : ℕ, ∀ x : ℕ, x0 ≤ x →
    x / (2 * Nat.log 2 x) ≤
      ((Finset.Ico x (2 * x)).filter Nat.Prime).card

/-- The full C1 construction package.  This is separated from the public theorem
so the remaining audited construction gap has a precise name.

`sorry` reason: this is note 35 §C1 / note 24 Lemma 9.1: the greedy exact-mass
tuning with high-scale semiprime batches, plus the common-period/load
bookkeeping.  It needs the Chebyshev dyadic prime-block density input and a
formal batch-selection proof not currently present in the repo. -/
theorem circle_method_edge_construction_core
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ) (L : ℕ),
      0 < L ∧
      b ∣ L ∧
      (∀ e ∈ E, e ∣ L) ∧
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      (∑ e ∈ E, (L / e : ℕ)) < L := by
  sorry

/-- **C1 edge construction, final route statement.**  For every squarefree
`b ≥ 2` and finite obstruction set `T`, there are semiprime edge denominators,
weights, and a common period satisfying the exact mass and load conditions. -/
theorem circle_method_edge_construction
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ) (L : ℕ),
      0 < L ∧
      b ∣ L ∧
      (∀ e ∈ E, e ∣ L) ∧
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      (∑ e ∈ E, (L / e : ℕ)) < L := by
  exact circle_method_edge_construction_core T b hb hbsf

end CircleMethodConstruction

end
