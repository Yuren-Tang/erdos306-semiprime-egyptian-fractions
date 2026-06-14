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

/-- The remaining prime-reciprocal window selection step.

This is the exact divergence/greedy core from `CODEX_TASK_semiprime_window.md`:
after deleting the finite obstruction and taking terms small enough for the
overshoot bound, choose a finite batch of odd primes whose `∑ 1/(2p)` lies in
the target window. -/
theorem exists_finset_primes_recip_between
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p ∧ 2 < p ∧ 2 * p ∉ T) ∧
      (3 / (2 * (b : ℝ)) ≤ ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) ∧
      ((∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) ≤ 3 / (b : ℝ)) ∧
      (∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) < 1 := by
  sorry

/-- The semiprime reciprocal window needed by the common-θ C1 construction.

This is now just the map `p ↦ 2p` from the prime-window lemma. -/
theorem semiprime_window_exists
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ E : Finset ℕ,
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (3 / (2 * (b : ℝ)) ≤ reciprocalLoad E) ∧
      (reciprocalLoad E ≤ 3 / (b : ℝ)) ∧
      reciprocalLoad E < 1 := by
  classical
  obtain ⟨P, hP, hsum_lb, hsum_ub, hsum_lt⟩ :=
    exists_finset_primes_recip_between T b hb
  have hsum_image :
      reciprocalLoad (P.image (fun p => (2 : ℕ) * p)) =
        ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
    rw [reciprocalLoad]
    calc
      ∑ e ∈ P.image (fun p => (2 : ℕ) * p), (1 : ℝ) / (e : ℝ)
          = ∑ p ∈ P, (1 : ℝ) / ((((2 : ℕ) * p : ℕ) : ℝ)) := by
            rw [Finset.sum_image (by
              intro p hp q hq hpq
              exact Nat.mul_left_cancel (by norm_num : 0 < 2)
                (show (2 : ℕ) * p = (2 : ℕ) * q from hpq))]
      _ = ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            norm_num
  refine ⟨P.image (fun p => (2 : ℕ) * p), ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨p, hpP, rfl⟩
    exact ⟨2, p, Nat.prime_two, (hP p hpP).1, (hP p hpP).2.1, rfl⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨p, hpP, rfl⟩
    exact (hP p hpP).2.2
  · simpa [hsum_image] using hsum_lb
  · simpa [hsum_image] using hsum_ub
  · simpa [hsum_image] using hsum_lt

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

This uses the common-θ simplification from `CODEX_TASK_c1_commontheta.md`.
Once `semiprime_window_exists` provides reciprocal load in `[3/(2b), 3/b]`,
the constant choice `θ = (1/b) / reciprocalLoad E` gives exact mass and
automatically lies in `[1/3, 2/3]`. -/

theorem circle_method_edge_mass_package
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (_hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ),
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      reciprocalLoad E < 1 := by
  classical
  obtain ⟨E, hsemi, havoid, hload_lb, hload_ub, hload_lt⟩ :=
    semiprime_window_exists T b hb
  let θ : ℕ → ℝ := fun _ => (1 / (b : ℝ)) / reciprocalLoad E
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hb
  have hload_pos : 0 < reciprocalLoad E := by
    have : 0 < 3 / (2 * (b : ℝ)) := by positivity
    exact lt_of_lt_of_le this hload_lb
  have hload_ub_mul : reciprocalLoad E * (b : ℝ) ≤ 3 := by
    rw [le_div_iff₀ hbpos] at hload_ub
    nlinarith
  have hload_lb_mul : 3 ≤ 2 * (b : ℝ) * reciprocalLoad E := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hbpos)] at hload_lb
    nlinarith
  have hθ_lb : (1 / 3 : ℝ) ≤ (1 / (b : ℝ)) / reciprocalLoad E := by
    rw [le_div_iff₀ hload_pos]
    rw [le_div_iff₀ hbpos]
    nlinarith
  have hθ_ub : (1 / (b : ℝ)) / reciprocalLoad E ≤ (2 / 3 : ℝ) := by
    rw [div_le_iff₀ hload_pos]
    rw [div_le_iff₀ hbpos]
    nlinarith
  have hmass :
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) := by
    have hsum_ne : (∑ x ∈ E, (1 : ℝ) / (x : ℝ)) ≠ 0 := by
      simpa [reciprocalLoad] using hload_pos.ne'
    unfold θ reciprocalLoad
    calc
      ∑ e ∈ E, ((1 / (b : ℝ)) / (∑ x ∈ E, (1 : ℝ) / (x : ℝ))) / (e : ℝ)
          =
        ∑ e ∈ E, ((1 / (b : ℝ)) / (∑ x ∈ E, (1 : ℝ) / (x : ℝ))) *
          ((1 : ℝ) / (e : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            ring
      _ =
        ((1 / (b : ℝ)) / (∑ x ∈ E, (1 : ℝ) / (x : ℝ))) *
          ∑ e ∈ E, (1 : ℝ) / (e : ℝ) := by
            rw [Finset.mul_sum]
      _ = 1 / (b : ℝ) := by
            field_simp [hsum_ne]
  refine ⟨E, θ, hsemi, havoid, ?_, hmass, hload_lt⟩
  intro e he
  exact ⟨hθ_lb, hθ_ub⟩

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
