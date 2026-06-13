import RequestProject.GlobalControl

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-!
# G7 Sector I absorption

This file is downstream-only.  It isolates the sector-I Laplace absorption
above the global control floor, with the corrected level-set hypothesis carrying
the fixed `exp(A * numBlocks BS)` factor.
-/

/-- Smaller of the two energy floors (copy of the route definition). -/
def globalControlFloor (BS : BlockSystem) (c2 e0 : ℝ) : ℝ :=
  min (Rw c2 BS.k0) (Pifloor BS e0 BS.k0)

/-- For a `Fintype` index and a decidable predicate, the subtype `tsum` is the
filtered finite sum. -/
lemma sectorI_fintype_subtype_tsum_eq {α : Type*} [Fintype α] (S : α → Prop)
    [DecidablePred S] (f : α → ℝ) :
    ∑' a : {x // S x}, f a.1 = ∑ a ∈ Finset.univ.filter S, f a := by
  classical
  rw [tsum_fintype]
  exact (Finset.sum_subtype (Finset.univ.filter S) (by intro x; simp) f).symm

/-- Convert the `Set.ncard` level-set hypothesis to the finite-filter form used
by `SBEEAssembly.partfun_series_bound`. -/
lemma sectorI_global_levelset_finset_bound
    (Cglob eps : ℝ) (BS : BlockSystem)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∀ R : ℝ, 1 ≤ R →
      ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS) := by
  intro R hR
  classical
  have hcard :
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) =
        ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset_setOf]
  simpa [hcard] using hlevel R hR

/-- Step A: full Laplace bound at exponent `c'`. -/
lemma sectorI_full_laplace_bound
    (c' eps A : ℝ) (hc' : 0 < c') (heps0 : 0 ≤ 8 * eps)
    (hepsc' : 8 * eps < c') (BS : BlockSystem) (hσ : 0 < sigmaCtrl BS)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∑ a : GlobalAssignment BS, Real.exp (-c' * Qctrl BS a) ≤
      Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps) /
        (1 - Real.exp (-(c' - 8 * eps))) ^ 2 *
        (1 + 1 / sigmaCtrl BS) := by
  exact SBEEAssembly.partfun_series_bound
    (fun a : GlobalAssignment BS => Qctrl BS a)
    (fun a => Qctrl_nonneg BS a)
    c' (8 * eps) (Real.exp (A * (numBlocks BS : ℝ))) (sigmaCtrl BS)
    hc' heps0 hepsc' (Real.exp_pos _).le hσ
    (sectorI_global_levelset_finset_bound
      (Real.exp (A * (numBlocks BS : ℝ))) eps BS hlevel)

/-- The remaining sector-I absorption package after the closed Laplace
conversion above.

`sorry` reason: this is precisely the floor-growth step requested in
`CODEX_TASK_sectorI.md`: prove `globalControlFloor BS c2 e0` beats every affine
function of `BS.k0`, uniformly over admissible block systems.  The `Rw` half is
available via `Rw_large`; the missing formal piece is the density-driven lower
bound showing `Pifloor BS e0 BS.k0` beats affine growth uniformly in `BS`. -/
theorem sectorI_floor_growth_absorption
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
  sorry

theorem sectorI_absorption' (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
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
  exact sectorI_floor_growth_absorption c hc eps A c2 e0 heps hepsc hA hc2 he0

end GlobalControl

end
