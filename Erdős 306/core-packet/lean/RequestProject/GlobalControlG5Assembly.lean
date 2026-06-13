/-
G5 assembly leaf for `GlobalControl`.

This file imports the (stable, cached) cover layer `GlobalControlG5Data` and
develops the remaining `hrhs` ε-budget assembly (note 40 §5): the label-charging
(`weighted_subset_entropy` coupling), the per-fiber count discharge, and the
final `global_levelset` assembly.  Keeping it separate from the large
`GlobalControlG5Data.lean` lets each edit re-elaborate only this leaf.
-/
import RequestProject.GlobalControlG5Data

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### Label-charging (note 40 §5 step (d)) -/

/-- The number of admissible label assignments factors as the product of the
    per-segment-start window sizes. -/
lemma admLabels_card (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) :
    (admLabels BS c2 R H B).card
      = ∏ s ∈ segStarts BS H B, (labelFin BS c2 R s).card := by
  rw [admLabels, Finset.card_image_of_injOn, Finset.card_pi]
  -- the zero-extension map is injective on the pi
  intro ℓ hℓ ℓ' hℓ' heq
  rw [Finset.mem_coe, Finset.mem_pi] at hℓ hℓ'
  funext s hs
  have := congrFun heq s
  simpa [dif_pos hs] using this

end GlobalControl
