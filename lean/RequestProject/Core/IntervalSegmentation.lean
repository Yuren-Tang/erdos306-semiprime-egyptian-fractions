import Mathlib.Order.Interval.Finset.Nat

/-! Finite interval segmentation by excluded vertices and cut edges. -/

open Finset Classical

namespace RequestProject

/-- Starts of the available segments in `[k0, K]`. A segment begins at `k0`
or immediately after an excluded vertex or cut edge. -/
def segmentStarts (k0 K : ℕ) (excluded cuts : Finset ℕ) : Finset ℕ :=
  (Finset.Icc k0 K \ excluded).filter
    (fun k => k = k0 ∨ (k - 1) ∈ excluded ∨ (k - 1) ∈ cuts)

/-- Start of the segment containing `k`, found by descending to `k0` or to
the first position preceded by an excluded vertex or cut edge. -/
def segmentStart (k0 : ℕ) (excluded cuts : Finset ℕ) : ℕ → ℕ
  | k => if k ≤ k0 then k0
         else if (k - 1) ∈ excluded ∨ (k - 1) ∈ cuts then k
         else segmentStart k0 excluded cuts (k - 1)
  decreasing_by all_goals omega

theorem segmentStart_le (k0 : ℕ) (excluded cuts : Finset ℕ) (k : ℕ)
    (hk : k0 ≤ k) : segmentStart k0 excluded cuts k ≤ k := by
  induction' k using Nat.strong_induction_on with k ih
  unfold segmentStart
  grind +splitImp

theorem segmentStart_ge (k0 : ℕ) (excluded cuts : Finset ℕ) (k : ℕ) :
    k0 ≤ segmentStart k0 excluded cuts k := by
  induction' k using Nat.strong_induction_on with k ih
  unfold segmentStart
  grind

/-- Strictly inside a segment there are neither excluded vertices nor cuts. -/
theorem segmentStart_interior (k0 : ℕ) (excluded cuts : Finset ℕ) (k j : ℕ)
    (hj1 : segmentStart k0 excluded cuts k ≤ j) (hj2 : j < k) :
    j ∉ excluded ∧ j ∉ cuts := by
  induction' k with k ih generalizing j <;> simp_all +decide
  grind +locals

@[simp] theorem segmentStart_empty (k0 k : ℕ) :
    segmentStart k0 (∅ : Finset ℕ) (∅ : Finset ℕ) k = k0 := by
  induction' k using Nat.strong_induction_on with k ih
  unfold segmentStart
  grind

end RequestProject
