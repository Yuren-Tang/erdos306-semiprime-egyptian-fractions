import RequestProject.GlobalControl.LaplaceAboveFloor
import RequestProject.GlobalControl.LevelSetAssembly
import RequestProject.GlobalControl.DiagonalGaussianTail

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-!
# Global control partition

This module is downstream-only: it imports `GlobalControl` and assembles the
headline off-main-arc bound `global_control_partition` from

* the level-set theorem `global_levelset` (factor `exp(A · numBlocks BS)`,
  with `A` fixed before the base-scale threshold, so the growing Peierls floor
  can absorb `A · numBlocks BS`);
* the localization dichotomy (`localization_dichotomy`: off-main implies either
  energy above the floor or global diagonality with a large label and exact
  quadratic energy);
* the high-energy Laplace absorption (`laplace_above_control_floor`);
* the diagonal Gaussian tail (`sectorII_gaussian`).

The earlier free-`Cglob` route form was *unsound* (a `k0min` independent of an
arbitrary later `Cglob` cannot absorb it): here the level-set hypothesis carries
the explicit `exp(A · numBlocks BS)` factor, so the quantifier order is correct.
-/

/-! ## Partition assembly -/

/-- The off-main-arc Laplace sum is bounded by an arbitrarily small `η / σ`
plus the one-dimensional Gaussian tail.

This is the route-closed form of `GlobalControl.global_control_partition`,
assembled from `global_levelset`, `localization_dichotomy`, and the two sector
estimates.  The `Cglob` factor is the *fixed* `exp(A · numBlocks BS)`, so the
quantifier order is sound. -/
theorem global_control_partition (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (_heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (η + Ctail * Real.exp (-C ^ 2 * c / 2)) / sigmaCtrl BS := by
  intro η hη
  classical
  -- Pick an internal level-set exponent eps0 ∈ (0,1) with 8·eps0 < c.
  set eps0 : ℝ := min (c / 16) (1 / 2) with heps0_def
  have heps0_pos : 0 < eps0 := lt_min (by positivity) (by norm_num)
  have heps0_lt1 : eps0 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heps0_c : 8 * eps0 < c := by
    have : eps0 ≤ c / 16 := min_le_left _ _
    nlinarith
  -- The level-set theorem supplies a fixed entropy constant and base scale.
  obtain ⟨levelScale, A, hA, hlevel⟩ := global_levelset eps0 heps0_pos heps0_lt1
  -- The localization dichotomy supplies fixed floor constants.
  obtain ⟨k0loc, c2, e0, hc2, he0, hloc⟩ := localization_dichotomy
  -- Sector I: η-absorption above the floor, depending on A, c2, e0.
  obtain ⟨k0minI, hI⟩ := laplace_above_control_floor c hc eps0 A c2 e0 heps0_pos heps0_c hA hc2 he0 η hη
  -- Sector II: the Gaussian tail constant.
  obtain ⟨Ctail, k0II, hCtail, hII⟩ := sectorII_gaussian c hc
  refine ⟨max levelScale (max k0loc (max k0minI k0II)), Ctail, hCtail, ?_⟩
  intro BS hk0 hadm C hC
  -- Unpack the scale thresholds.
  have hlevelScale : levelScale ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  have hk0loc : k0loc ≤ BS.k0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk0
  have hk0I : k0minI ≤ BS.k0 :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk0
  have hk0II : k0II ≤ BS.k0 :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk0
  -- sigmaCtrl positivity (there is at least one control pair).
  have hσpos : 0 < sigmaCtrl BS := sigmaCtrl_pos BS hadm
  -- The explicit level-set bound for this BS.
  have hlevelBS := hlevel BS hlevelScale hadm
  -- Localization dichotomy for this BS, C.
  have hlocBS := hloc BS hk0loc hadm C hC
  -- Split the off-main-arc sum into the floor sector and the diagonal sector.
  have hsplit :
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)) +
        ∑' a : {a : GlobalAssignment BS // diagSector BS C a},
          Real.exp (-c * Qctrl BS a.1) :=
    RequestProject.fintype_subtype_tsum_le_of_or
      (fun a => a ∉ mainArc BS C)
      (fun a => globalControlFloor BS c2 e0 ≤ Qctrl BS a)
      (fun a => diagSector BS C a)
      (fun a => Real.exp (-c * Qctrl BS a))
      (fun a => (Real.exp_pos _).le)
      (fun a ha => hlocBS a ha)
  -- Bound each sector.
  have hsI := hI BS hk0I hadm hσpos hlevelBS
  have hsII := hII BS hk0II hσpos C hC
  calc ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1)
      ≤ (∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
            Real.exp (-c * Qctrl BS a.1)) +
        ∑' a : {a : GlobalAssignment BS // diagSector BS C a},
            Real.exp (-c * Qctrl BS a.1) := hsplit
    _ ≤ η / sigmaCtrl BS + Ctail * Real.exp (-C ^ 2 * c / 2) / sigmaCtrl BS :=
        add_le_add hsI hsII
    _ = (η + Ctail * Real.exp (-C ^ 2 * c / 2)) / sigmaCtrl BS := by ring

end GlobalControl

end
