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

/-- The reciprocal load used in the period bookkeeping. -/
def reciprocalLoad (E : Finset ℕ) : ℝ :=
  ∑ e ∈ E, (1 : ℝ) / (e : ℝ)

/-- A simple common period for a finite edge set.  The paper takes the product
of incident primes; for the denominator-only C1 interface, the product of the
edge values is enough and avoids proving pairwise coprimality here. -/
def commonPeriod (b : ℕ) (E : Finset ℕ) : ℕ :=
  b * ∏ e ∈ E, e

/-- Once the C1 greedy step has produced semiprime denominators, weights with
the exact mass, and reciprocal load `< 1`, the common-period and load
bookkeeping is elementary. -/
theorem assemble_period_from_mass_package
    (T E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (hb : 0 < b)
    (hsemi : ∀ e ∈ E, IsSemiprime e)
    (havoid : ∀ e ∈ E, e ∉ T)
    (hθ : ∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ))
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (hload : reciprocalLoad E < 1) :
    ∃ (L : ℕ),
      0 < L ∧
      b ∣ L ∧
      (∀ e ∈ E, e ∣ L) ∧
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      (∑ e ∈ E, (L / e : ℕ)) < L := by
  classical
  refine ⟨commonPeriod b E, ?_⟩
  have hprod_pos : 0 < ∏ e ∈ E, e := by
    exact Finset.prod_pos fun e he => (hsemi e he).pos
  have hLpos : 0 < commonPeriod b E := by
    unfold commonPeriod
    exact Nat.mul_pos hb hprod_pos
  have hEdvd : ∀ e ∈ E, e ∣ commonPeriod b E := by
    intro e he
    unfold commonPeriod
    exact dvd_trans (Finset.dvd_prod_of_mem id he) (Nat.dvd_mul_left _ _)
  have hload_cast :
      (∑ e ∈ E, ((commonPeriod b E / e : ℕ) : ℝ)) =
        (commonPeriod b E : ℝ) * reciprocalLoad E := by
    unfold reciprocalLoad
    calc
      ∑ x ∈ E, ((commonPeriod b E / x : ℕ) : ℝ)
          = ∑ x ∈ E, (commonPeriod b E : ℝ) / (x : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxpos : 0 < x := (hsemi x hx).pos
            have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hxpos.ne'
            rw [Nat.cast_div (hEdvd x hx) hxR]
      _ = ∑ x ∈ E, (commonPeriod b E : ℝ) * ((1 : ℝ) / (x : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            field_simp
      _ = (commonPeriod b E : ℝ) * ∑ x ∈ E, (1 : ℝ) / (x : ℝ) := by
            rw [Finset.mul_sum]
  have hload_nat :
      (∑ e ∈ E, (commonPeriod b E / e : ℕ)) < commonPeriod b E := by
    rw [← Nat.cast_lt (α := ℝ)]
    rw [Nat.cast_sum]
    rw [hload_cast]
    have hLposR : 0 < (commonPeriod b E : ℝ) := by exact_mod_cast hLpos
    nlinarith
  exact ⟨hLpos, dvd_mul_right b _, hEdvd, hsemi, havoid, hθ, hmass, hload_nat⟩

/-- The C1 greedy mass package, before choosing a common period.

This is the audited note 35 §C1 / note 24 Lemma 9.1 selection step:
control+gadget edges give a small base mass, then a high-scale greedy batch
with `θ_H = Δ / W_H ∈ [1/3, 1/2]` tunes the mass exactly while keeping
`∑ 1/e < 1`.

`sorry` reason: this is note 35 §C1 / note 24 Lemma 9.1: the greedy exact-mass
tuning with high-scale semiprime batches.  It needs the Chebyshev dyadic
prime-block density input and a formal batch-selection proof not currently
present in the repo. -/
theorem circle_method_edge_mass_package
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (_hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ),
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      reciprocalLoad E < 1 := by
  sorry

/-- The full C1 construction package.  This is separated from the public theorem
so the remaining audited construction gap has a precise name. -/
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
  obtain ⟨E, θ, hsemi, havoid, hθ, hmass, hload⟩ :=
    circle_method_edge_mass_package T b hb hbsf
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  obtain ⟨L, hLpos, hbL, hEdvd, hsemi', havoid', hθ', hmass', hload'⟩ :=
    assemble_period_from_mass_package T E θ b hbpos hsemi havoid hθ hmass hload
  exact ⟨E, θ, L, hLpos, hbL, hEdvd, hsemi', havoid', hθ', hmass', hload'⟩

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
