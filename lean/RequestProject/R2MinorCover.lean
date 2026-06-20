import RequestProject.R2MinorEstimateInterface
import RequestProject.R2AssemblyFields

open Finset BigOperators

noncomputable section

namespace CircleMethod

/-!
# R2 minor-cover wrappers

This file packages the finite cover statement used by the R2 minor assembly:
every minor frequency is either handled by the block-minor estimate or by the
extra-minor estimate.  The actual analytic bounds remain external hypotheses.
-/

/-- Concrete frequency-cover data for the final R2 minor arc. -/
structure R2MinorCoverData (Sm : Finset ℕ) where
  Sblock : Finset ℕ
  Sextra : Finset ℕ
  hcover : Sm ⊆ Sblock ∪ Sextra

/-- The norm of the Fourier summand at one frequency. -/
def fourierNormWeight (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (h : ℕ) : ℝ :=
  ‖fourierTerm E theta b L h‖

/-- Minor-arc norm bound from block/extra norm estimates and an additive
budget.  This is the finite cover interface consumed by the final R2 assembly. -/
theorem hminor_of_block_extra_norm_bounds
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (Sm : Finset ℕ) (C : R2MinorCoverData Sm)
    (Bblock Bextra Bm : ℝ)
    (hblock :
      ∑ h ∈ blockMinorPart Sm C.Sblock,
        fourierNormWeight E theta b L h ≤ Bblock)
    (hextra :
      ∑ h ∈ extraMinorPart Sm C.Sblock C.Sextra,
        fourierNormWeight E theta b L h ≤ Bextra)
    (hbudget : Bblock + Bextra ≤ Bm) :
    ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm := by
  refine le_trans (norm_sum_le Sm (fun h => fourierTerm E theta b L h)) ?_
  exact le_trans
    (r2_hminor_bound_from_block_and_extra Sm C.Sblock C.Sextra
      (fourierNormWeight E theta b L) C.hcover hblock hextra)
    hbudget

/-- Summed-norm minor-arc bound `∑_{h∈Sm} ‖fourierTerm h‖ ≤ Bm` from block/extra
norm estimates and an additive budget.  This is the form consumed by the
cannon-based existence step (`exists_subset_of_fourier_arcs`), which needs the
sum of norms rather than the norm of the sum. -/
theorem hminorSum_of_block_extra_norm_bounds
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (Sm : Finset ℕ) (C : R2MinorCoverData Sm)
    (Bblock Bextra Bm : ℝ)
    (hblock :
      ∑ h ∈ blockMinorPart Sm C.Sblock,
        fourierNormWeight E theta b L h ≤ Bblock)
    (hextra :
      ∑ h ∈ extraMinorPart Sm C.Sblock C.Sextra,
        fourierNormWeight E theta b L h ≤ Bextra)
    (hbudget : Bblock + Bextra ≤ Bm) :
    (∑ h ∈ Sm, ‖fourierTerm E theta b L h‖) ≤ Bm :=
  le_trans
    (r2_hminor_bound_from_block_and_extra Sm C.Sblock C.Sextra
      (fourierNormWeight E theta b L) C.hcover hblock hextra)
    hbudget

variable {α : Type*} [DecidableEq α]

/-- Data for a finite block/extra cover of the minor frequencies. -/
structure R2MinorCover (α : Type*) [DecidableEq α] where
  Sm : Finset α
  Sblock : Finset α
  Sextra : Finset α
  hcover : Sm ⊆ Sblock ∪ Sextra

namespace R2MinorCover

variable (C : R2MinorCover α)

/-- The part of the minor frequencies assigned to the block-minor estimate. -/
def blockPart : Finset α :=
  blockMinorPart C.Sm C.Sblock

/-- The remaining covered part assigned to the extra-minor estimate. -/
def extraPart : Finset α :=
  extraMinorPart C.Sm C.Sblock C.Sextra

lemma mem_blockPart {x : α} :
    x ∈ C.blockPart ↔ x ∈ C.Sm ∧ x ∈ C.Sblock := by
  simpa [blockPart] using
    (mem_blockMinorPart (Sm := C.Sm) (Sblock := C.Sblock) (x := x))

lemma mem_extraPart {x : α} :
    x ∈ C.extraPart ↔ x ∈ C.Sm ∧ x ∉ C.Sblock ∧ x ∈ C.Sextra := by
  simpa [extraPart] using
    (mem_extraMinorPart (Sm := C.Sm) (Sblock := C.Sblock)
      (Sextra := C.Sextra) (x := x))

lemma blockPart_disjoint_extraPart :
    Disjoint C.blockPart C.extraPart := by
  simpa [blockPart, extraPart] using
    blockMinorPart_disjoint_extraMinorPart C.Sm C.Sblock C.Sextra

lemma blockPart_union_extraPart_eq :
    C.blockPart ∪ C.extraPart = C.Sm := by
  simpa [blockPart, extraPart] using
    minorParts_union_eq_of_cover (Sm := C.Sm) (Sblock := C.Sblock)
      (Sextra := C.Sextra) C.hcover

/-- Combine block-minor and extra-minor estimates using the packaged cover. -/
lemma sum_le_of_part_bounds (F : α → ℝ) {A B : ℝ}
    (hblock : ∑ x ∈ C.blockPart, F x ≤ A)
    (hextra : ∑ x ∈ C.extraPart, F x ≤ B) :
    ∑ x ∈ C.Sm, F x ≤ A + B :=
  r2_minor_bound_split C.Sm C.Sblock C.Sextra F C.hcover
    (by simpa [blockPart] using hblock)
    (by simpa [extraPart] using hextra)

end R2MinorCover

/-- Build the minor-cover package from the usual pointwise classification. -/
def r2MinorCoverOfForallOr (Sm Sblock Sextra : Finset α)
    (h : ∀ x ∈ Sm, x ∈ Sblock ∨ x ∈ Sextra) :
    R2MinorCover α where
  Sm := Sm
  Sblock := Sblock
  Sextra := Sextra
  hcover := by
    intro x hx
    exact Finset.mem_union.mpr (h x hx)

/-- If every non-block minor frequency lies in the extra set, the two sets cover
the minor frequencies. -/
def r2MinorCoverOfExtraForNotBlock (Sm Sblock Sextra : Finset α)
    (h : ∀ x ∈ Sm, x ∉ Sblock → x ∈ Sextra) :
    R2MinorCover α :=
  r2MinorCoverOfForallOr Sm Sblock Sextra
    (by
      intro x hxSm
      by_cases hxblock : x ∈ Sblock
      · exact Or.inl hxblock
      · exact Or.inr (h x hxSm hxblock))

lemma r2Minor_cover_of_forall_or {Sm Sblock Sextra : Finset α}
    (h : ∀ x ∈ Sm, x ∈ Sblock ∨ x ∈ Sextra) :
    Sm ⊆ Sblock ∪ Sextra :=
  (r2MinorCoverOfForallOr Sm Sblock Sextra h).hcover

lemma r2Minor_cover_of_extra_for_not_block {Sm Sblock Sextra : Finset α}
    (h : ∀ x ∈ Sm, x ∉ Sblock → x ∈ Sextra) :
    Sm ⊆ Sblock ∪ Sextra :=
  (r2MinorCoverOfExtraForNotBlock Sm Sblock Sextra h).hcover

/-- One-shot form: pointwise block/extra classification plus the two part bounds
imply the full minor bound. -/
theorem r2_minor_bound_from_forall_or
    (Sm Sblock Sextra : Finset α) (F : α → ℝ) {A B : ℝ}
    (hcover : ∀ x ∈ Sm, x ∈ Sblock ∨ x ∈ Sextra)
    (hblock : ∑ x ∈ blockMinorPart Sm Sblock, F x ≤ A)
    (hextra : ∑ x ∈ extraMinorPart Sm Sblock Sextra, F x ≤ B) :
    ∑ x ∈ Sm, F x ≤ A + B :=
  r2_minor_bound_split Sm Sblock Sextra F
    (r2Minor_cover_of_forall_or hcover) hblock hextra

/-- One-shot form for the common proof shape where only non-block minor
frequencies need to be shown extra. -/
theorem r2_minor_bound_from_extra_for_not_block
    (Sm Sblock Sextra : Finset α) (F : α → ℝ) {A B : ℝ}
    (hcover : ∀ x ∈ Sm, x ∉ Sblock → x ∈ Sextra)
    (hblock : ∑ x ∈ blockMinorPart Sm Sblock, F x ≤ A)
    (hextra : ∑ x ∈ extraMinorPart Sm Sblock Sextra, F x ≤ B) :
    ∑ x ∈ Sm, F x ≤ A + B :=
  r2_minor_bound_split Sm Sblock Sextra F
    (r2Minor_cover_of_extra_for_not_block hcover) hblock hextra

end CircleMethod

end
