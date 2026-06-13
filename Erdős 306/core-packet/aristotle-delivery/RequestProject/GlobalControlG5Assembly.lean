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

/-- Generic charge-sum bound: summing the per-element charge `exp(ε·w j)` over
    all weight-`≤R` subsets is `≤ exp(2εR)·exp(numBlocks)`, via
    `weighted_subset_entropy` (with `ε' = 4ε`).  Instantiated for the hot
    (`w = Rw`) and boundary (`w = Pifloor`) charges. -/
lemma sum_subset_charge_le (BS : BlockSystem) (w : ℕ → ℝ) (R eps : ℝ)
    (heps : 0 < eps) (hw : ∀ j ∈ Finset.Icc BS.k0 BS.K, 0 ≤ w j) :
    (∑ S ∈ (Finset.Icc BS.k0 BS.K).powerset.filter (fun S => ∑ j ∈ S, w j ≤ R),
        ∏ j ∈ S, Real.exp (eps * w j))
      ≤ Real.exp (2 * eps * R) * Real.exp (numBlocks BS) := by
  have hcb : ∀ j ∈ Finset.Icc BS.k0 BS.K,
      Real.exp (eps * w j) ≤ Real.exp (4 * eps * w j / 4) :=
    fun j _ => le_of_eq (by congr 1; ring)
  have hwse := GlobalPeierls.weighted_subset_entropy (Finset.Icc BS.k0 BS.K) w
    (fun j => Real.exp (eps * w j)) (4 * eps) R (by linarith)
    (fun _ _ => Real.exp_nonneg _) hcb
  refine le_trans hwse ?_
  refine mul_le_mul (Real.exp_le_exp.mpr (le_of_eq (by ring)))
    (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (Real.exp_nonneg _)
  calc (∑ j ∈ Finset.Icc BS.k0 BS.K, Real.exp (-(4 * eps) * w j / 4))
      ≤ ∑ _j ∈ Finset.Icc BS.k0 BS.K, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj =>
          Real.exp_le_one_iff.mpr (by nlinarith [hw j hj, heps]))
    _ = (numBlocks BS : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
        norm_cast

end GlobalControl
