import RequestProject.FiniteSums
import RequestProject.GlobalControl.ControlFloorGrowth
import RequestProject.GlobalControl.GlobalLaplaceBound

/-!
# Laplace absorption above the control floor

The full Laplace bound and the superlinear control-floor growth combine to make
the contribution above the floor arbitrarily small.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

theorem laplace_above_control_floor
    (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
    (heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
    (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ η : ℝ, 0 < η →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      0 < sigmaCtrl BS →
      (∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
            (1 + Real.sqrt R / sigmaCtrl BS)) →
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1) ≤ η / sigmaCtrl BS := by
  intro η hη
  classical
  set cbar : ℝ := (8 * eps + c) / 2 with hcbar_def
  set K0 : ℝ := Real.exp (8 * eps) /
    (1 - Real.exp (-(cbar - 8 * eps))) ^ 2 with hK0_def
  obtain ⟨k0grow, hgrow⟩ :=
    control_floor_absorbs_entropy c hc eps A c2 e0 heps hepsc hA hc2 he0 η hη
  refine ⟨max 2 k0grow, ?_⟩
  intro BS hk0 hadm hσ hlevel
  have hk0two : 2 ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  have hk0grow : k0grow ≤ BS.k0 := le_trans (le_max_right _ _) hk0
  have hσle : sigmaCtrl BS ≤ 1 := sigmaCtrl_le_one BS hk0two
  have hcbar_pos : 0 < cbar := by
    rw [hcbar_def]
    nlinarith [heps, hc]
  have h8cbar : 8 * eps < cbar := by
    rw [hcbar_def]
    nlinarith [hepsc]
  have hcbarc : cbar < c := by
    rw [hcbar_def]
    nlinarith [hepsc]
  have hdpos : 0 < c - cbar := sub_pos.mpr hcbarc
  have h8eps_nonneg : 0 ≤ 8 * eps := by nlinarith [heps]
  have hlap := full_laplace_bound_of_global_levelsets cbar eps A hcbar_pos h8eps_nonneg
    h8cbar BS hσ hlevel
  have hgrowBS :
      Real.exp
            (A * (numBlocks BS : ℝ) -
              (c - (8 * eps + c) / 2) * globalControlFloor BS c2 e0) *
          (2 *
            (Real.exp (8 * eps) /
              (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2)) ≤ η :=
    hgrow BS hk0grow hadm
  have hgrowBS' :
      Real.exp
            (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
          (2 * K0) ≤ η := by
    simpa [hcbar_def, hK0_def] using hgrowBS
  have htail :
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)
        ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
          ∑ a : GlobalAssignment BS, Real.exp (-cbar * Qctrl BS a) := by
    rw [RequestProject.fintype_subtype_tsum_eq
      (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a)
      (fun a => Real.exp (-c * Qctrl BS a))]
    calc
      ∑ a ∈ Finset.univ.filter
          (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a),
          Real.exp (-c * Qctrl BS a)
          ≤ ∑ a ∈ Finset.univ.filter
              (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a),
              Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
                Real.exp (-cbar * Qctrl BS a) := by
            refine Finset.sum_le_sum (fun a ha => ?_)
            have hfloor : globalControlFloor BS c2 e0 ≤ Qctrl BS a :=
              (Finset.mem_filter.mp ha).2
            rw [← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            nlinarith [mul_le_mul_of_nonneg_left hfloor hdpos.le]
        _ = Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              ∑ a ∈ Finset.univ.filter
                (fun a : GlobalAssignment BS => globalControlFloor BS c2 e0 ≤ Qctrl BS a),
                Real.exp (-cbar * Qctrl BS a) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              ∑ a : GlobalAssignment BS, Real.exp (-cbar * Qctrl BS a) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun a _ _ => (Real.exp_pos _).le)
  have hsum_bound :
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)
        ≤ Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (1 + 1 / sigmaCtrl BS) := by
    calc
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)
          ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              ∑ a : GlobalAssignment BS, Real.exp (-cbar * Qctrl BS a) := htail
      _ ≤ Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
            (Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps) /
              (1 - Real.exp (-(cbar - 8 * eps))) ^ 2 *
              (1 + 1 / sigmaCtrl BS)) := by
          exact mul_le_mul_of_nonneg_left hlap (Real.exp_pos _).le
      _ = (Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
              Real.exp (A * (numBlocks BS : ℝ))) *
            K0 * (1 + 1 / sigmaCtrl BS) := by
          rw [hK0_def]
          ring
      _ = Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (1 + 1 / sigmaCtrl BS) := by
          have hexp :
              Real.exp (-(c - cbar) * globalControlFloor BS c2 e0) *
                  Real.exp (A * (numBlocks BS : ℝ)) =
                Real.exp (A * (numBlocks BS : ℝ) -
                  (c - cbar) * globalControlFloor BS c2 e0) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hexp]
  have hσ_factor : 1 + 1 / sigmaCtrl BS ≤ 2 / sigmaCtrl BS := by
    have hle_inv : (1 : ℝ) ≤ 1 / sigmaCtrl BS := by
      rw [le_div_iff₀ hσ]
      simpa using hσle
    calc
      1 + 1 / sigmaCtrl BS ≤ 1 / sigmaCtrl BS + 1 / sigmaCtrl BS :=
        by simpa [add_comm] using add_le_add_left hle_inv (1 / sigmaCtrl BS)
      _ = 2 / sigmaCtrl BS := by ring
  have hK0_nonneg : 0 ≤ K0 := by
    rw [hK0_def]
    exact div_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hcoef_nonneg :
      0 ≤ Real.exp (A * (numBlocks BS : ℝ) -
            (c - cbar) * globalControlFloor BS c2 e0) * K0 :=
    mul_nonneg (Real.exp_pos _).le hK0_nonneg
  calc
    ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
        Real.exp (-c * Qctrl BS a.1)
        ≤ Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (1 + 1 / sigmaCtrl BS) := hsum_bound
    _ ≤ Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            K0 * (2 / sigmaCtrl BS) := by
        exact mul_le_mul_of_nonneg_left hσ_factor hcoef_nonneg
    _ = (Real.exp (A * (numBlocks BS : ℝ) -
              (c - cbar) * globalControlFloor BS c2 e0) *
            (2 * K0)) / sigmaCtrl BS := by
        ring
    _ ≤ η / sigmaCtrl BS :=
        div_le_div_of_nonneg_right hgrowBS' hσ.le

end GlobalControl

end
