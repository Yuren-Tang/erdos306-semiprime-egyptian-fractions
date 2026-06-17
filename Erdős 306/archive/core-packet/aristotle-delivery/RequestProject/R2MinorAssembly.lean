import RequestProject.R2AssemblySkeleton
import RequestProject.ExtraEnergyMinorArc
import RequestProject.ExtraMinorDamping

open Finset BigOperators

namespace CircleMethod

/-!
# R2 minor-split assembly interface

This leaf isolates the finite-sum partition used by the final R2 `hminor`
field.  The analytic estimates remain external hypotheses here: one bound for
the block-minor part and one bound for the extra-minor part.
-/

variable {α : Type*} [DecidableEq α]

/-- Frequencies assigned to the block-minor estimate. -/
def blockMinorPart (Sm Sblock : Finset α) : Finset α :=
  Sm.filter (fun x => x ∈ Sblock)

/-- Frequencies assigned to the extra-minor estimate, disjointized away from the
block-minor part. -/
def extraMinorPart (Sm Sblock Sextra : Finset α) : Finset α :=
  Sm.filter (fun x => x ∉ Sblock ∧ x ∈ Sextra)

lemma mem_blockMinorPart {Sm Sblock : Finset α} {x : α} :
    x ∈ blockMinorPart Sm Sblock ↔ x ∈ Sm ∧ x ∈ Sblock := by
  simp [blockMinorPart]

lemma mem_extraMinorPart {Sm Sblock Sextra : Finset α} {x : α} :
    x ∈ extraMinorPart Sm Sblock Sextra ↔
      x ∈ Sm ∧ x ∉ Sblock ∧ x ∈ Sextra := by
  simp [extraMinorPart, and_assoc]

lemma blockMinorPart_disjoint_extraMinorPart
    (Sm Sblock Sextra : Finset α) :
    Disjoint (blockMinorPart Sm Sblock) (extraMinorPart Sm Sblock Sextra) := by
  rw [Finset.disjoint_left]
  intro x hxblock hxextra
  rw [mem_blockMinorPart] at hxblock
  rw [mem_extraMinorPart] at hxextra
  exact hxextra.2.1 hxblock.2

lemma minorParts_union_eq_of_cover {Sm Sblock Sextra : Finset α}
    (hcover : Sm ⊆ Sblock ∪ Sextra) :
    blockMinorPart Sm Sblock ∪ extraMinorPart Sm Sblock Sextra = Sm := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_union] at hx
    rcases hx with hxblock | hxextra
    · exact (mem_blockMinorPart.mp hxblock).1
    · exact (mem_extraMinorPart.mp hxextra).1
  · intro hxSm
    have hxcover := hcover hxSm
    rw [Finset.mem_union] at hxcover ⊢
    by_cases hxblock : x ∈ Sblock
    · left
      exact mem_blockMinorPart.mpr ⟨hxSm, hxblock⟩
    · right
      rcases hxcover with hxSblock | hxSextra
      · exact False.elim (hxblock hxSblock)
      · exact mem_extraMinorPart.mpr ⟨hxSm, hxblock, hxSextra⟩

/-- Pure finite-sum splitter for the final R2 minor arc.  The extra part is
disjointized away from the block part, so no inclusion-exclusion loss is needed. -/
lemma sum_le_of_minor_split_bounds
    (Sm Sblock Sextra : Finset α) (F : α → ℝ) {A B : ℝ}
    (hcover : Sm ⊆ Sblock ∪ Sextra)
    (hblock : ∑ x ∈ blockMinorPart Sm Sblock, F x ≤ A)
    (hextra : ∑ x ∈ extraMinorPart Sm Sblock Sextra, F x ≤ B) :
    ∑ x ∈ Sm, F x ≤ A + B := by
  have hdisj := blockMinorPart_disjoint_extraMinorPart Sm Sblock Sextra
  have hsum :
      ∑ x ∈ Sm, F x =
        (∑ x ∈ blockMinorPart Sm Sblock, F x) +
          ∑ x ∈ extraMinorPart Sm Sblock Sextra, F x := by
    calc
      ∑ x ∈ Sm, F x =
          ∑ x ∈ blockMinorPart Sm Sblock ∪ extraMinorPart Sm Sblock Sextra, F x := by
            rw [minorParts_union_eq_of_cover hcover]
      _ = (∑ x ∈ blockMinorPart Sm Sblock, F x) +
            ∑ x ∈ extraMinorPart Sm Sblock Sextra, F x := by
            rw [Finset.sum_union hdisj]
  rw [hsum]
  exact add_le_add hblock hextra

/-- Alias with the intended paper-side name: combine block-minor and extra-minor
estimates into one `hminor`-shaped estimate. -/
theorem r2_minor_bound_split
    (Sm Sblock Sextra : Finset α) (F : α → ℝ) {A B : ℝ}
    (hcover : Sm ⊆ Sblock ∪ Sextra)
    (hblock : ∑ x ∈ blockMinorPart Sm Sblock, F x ≤ A)
    (hextra : ∑ x ∈ extraMinorPart Sm Sblock Sextra, F x ≤ B) :
    ∑ x ∈ Sm, F x ≤ A + B :=
  sum_le_of_minor_split_bounds Sm Sblock Sextra F hcover hblock hextra

end CircleMethod
