import RequestProject.GlobalControl

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-!
Route-closure file for G7.

This module is intentionally downstream-only: it imports `GlobalControl` and
does not edit the shared Phase-G files.  The first lemmas close the analytic
part of the route from an explicit G5 level-set hypothesis to a global
partition-function bound.  The remaining named `sorry`s mark the presently
unexposed G6 localization/sector assembly needed to finish the exact off-main
arc statement.
-/

/-- The globally diagonal assignments, with no small-label restriction. -/
def globallyDiagonal (BS : BlockSystem) (a : GlobalAssignment BS) : Prop :=
  ∃ m : ℤ, ∀ p : {p : ℕ // p ∈ blockSupport BS},
    (a p : ZMod p.1) = (m : ZMod p.1)

/-- The G6 energy floor used by the route: hot floor versus boundary floor at
the first block.  The exception floor from note 38 §6 is folded into the named
localization placeholder below, because no standalone exposed definition exists
in `GlobalControl.lean`. -/
def globalControlFloor (BS : BlockSystem) (c2 e0 : ℝ) : ℝ :=
  min (Rw c2 BS.k0) (Pifloor BS e0 BS.k0)

/-- Convert the explicit G5 route hypothesis, stated with `Set.ncard`, to the
`Finset.univ.filter` form required by `SBEEAssembly.partfun_series_bound`. -/
lemma global_levelset_finset_bound
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

/-- Analytic G7 route core: the explicit G5 level-set bound implies a full
global partition-function bound at exponent `c`. -/
lemma global_partfun_bound_from_hlevel
    (c eps Cglob : ℝ) (hc : 0 < c) (heps : 0 < eps)
    (hepsc : 8 * eps < c) (hCglob : 0 ≤ Cglob)
    (BS : BlockSystem) (hsig : 0 < sigmaCtrl BS)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) *
          (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∑ a : GlobalAssignment BS, Real.exp (-c * Qctrl BS a) ≤
      Cglob * Real.exp (8 * eps) /
        (1 - Real.exp (-(c - 8 * eps))) ^ 2 *
        (1 + 1 / sigmaCtrl BS) := by
  exact SBEEAssembly.partfun_series_bound
    (fun a : GlobalAssignment BS => Qctrl BS a)
    (fun a => Qctrl_nonneg BS a)
    c (8 * eps) Cglob (sigmaCtrl BS)
    hc (by positivity) hepsc hCglob hsig
    (global_levelset_finset_bound Cglob eps BS hlevel)

/-- The G6 localization dichotomy from note 38 §6, in the route form needed by
G7.  It says an off-main-arc assignment is either above the global energy floor,
or is globally diagonal with a label outside the main-arc window and exact
quadratic control energy.

`sorry` reason: the current shared API exposes the cold/hot and boundary
bookkeeping, but not yet the complete G6 proof combining the exception floor,
segment constancy, and the CRT identity `Qctrl = m² sigmaCtrl²`. -/
theorem global_control_localization_dichotomy_route :
    ∃ (k0loc : ℕ) (c2 e0 : ℝ), 0 < c2 ∧ 0 < e0 ∧
      ∀ (BS : BlockSystem), k0loc ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ a : GlobalAssignment BS, a ∉ mainArc BS C →
        globalControlFloor BS c2 e0 ≤ Qctrl BS a ∨
          ∃ m : ℤ,
            (∀ p : {p : ℕ // p ∈ blockSupport BS},
              (a p : ZMod p.1) = (m : ZMod p.1)) ∧
            C / sigmaCtrl BS < |(m : ℝ)| ∧
            Qctrl BS a = (m : ℝ) ^ 2 * (sigmaCtrl BS) ^ 2 := by
  sorry

/-- Route-closure version of G7: it takes the G5 level-set bound as an explicit
hypothesis, so it does not depend on `global_levelset`.

`sorry` reason: after the closed analytic `partfun_series_bound` step above,
the remaining proof requires the unexposed G6 sector split: lower-bounding
`globalControlFloor` strongly enough to absorb the full partition function into
`η / sigmaCtrl`, plus injecting the globally diagonal sector into the integer
Gaussian tail using the exact CRT-energy identity. -/
theorem global_control_partition_route (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (Cglob : ℝ), 0 ≤ Cglob →
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      (∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Cglob * Real.exp (8 * eps * R) *
            (1 + Real.sqrt R / sigmaCtrl BS)) →
      ∀ (C : ℝ), 1 ≤ C →
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (η + Ctail * Real.exp (-C ^ 2 * c / 2)) /
          sigmaCtrl BS := by
  sorry

end GlobalControl

end
