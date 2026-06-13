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

/-- The remaining floor-growth input for Sector I.

This is the density-driven lower bound requested in `CODEX_TASK_pifloor.md`,
packaged in the affine form actually consumed by the absorption arithmetic:
eventually the global floor beats any prescribed affine function of `k₀`.

`sorry` reason: this is the prime-density/Pifloor lower bound from note 35/38:
`Pifloor BS e0 k0` is uniformly bounded below by an exponential-over-polynomial
quantity, while `Rw c2 k0` has the analogous superlinear growth. -/
lemma Pifloor_density_lower
    (c2 e0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ (β A V : ℝ), 0 < β → 0 < A →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
        (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤
          globalControlFloor BS c2 e0 := by
  sorry

/-- The floor-growth input for Sector I.

For `cbar = (8*eps+c)/2` and
`K0 = exp(8eps)/(1-exp(-(cbar-8eps)))^2`, the global control floor eventually
absorbs the fixed block-count factor and the Laplace prefactor. -/
theorem Pifloor_superlinear
    (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
    (heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
    (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ η : ℝ, 0 < η →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
        Real.exp
            (A * (numBlocks BS : ℝ) -
              (c - (8 * eps + c) / 2) * globalControlFloor BS c2 e0) *
          (2 *
            (Real.exp (8 * eps) /
              (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2)) ≤ η := by
  intro η hη
  classical
  set β : ℝ := c - (8 * eps + c) / 2 with hβ_def
  set K0 : ℝ := Real.exp (8 * eps) /
    (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2 with hK0_def
  have hβ_pos : 0 < β := by
    rw [hβ_def]
    nlinarith [hepsc]
  have hβ_alt : (8 * eps + c) / 2 - 8 * eps = β := by
    rw [hβ_def]
    ring
  have hden_ne :
      (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ≠ 0 := by
    rw [hβ_alt]
    have hexplt : Real.exp (-β) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hK0_pos : 0 < K0 := by
    rw [hK0_def]
    exact div_pos (Real.exp_pos _) (sq_pos_of_ne_zero hden_ne)
  set V : ℝ := Real.log ((2 * K0) / η) with hV_def
  obtain ⟨k0floor, hfloor⟩ :=
    Pifloor_density_lower c2 e0 hc2 he0 β A V hβ_pos hA
  refine ⟨max 2 k0floor, ?_⟩
  intro BS hk0 hadm
  have hk0floor : k0floor ≤ BS.k0 := le_trans (le_max_right _ _) hk0
  have hfloorBS :
      (A * (2 * (BS.k0 : ℝ) + 1) + V) / β ≤
        globalControlFloor BS c2 e0 :=
    hfloor BS hk0floor hadm
  have hT_le :
      A * (2 * (BS.k0 : ℝ) + 1) + V ≤
        β * globalControlFloor BS c2 e0 := by
    have := (div_le_iff₀ hβ_pos).mp hfloorBS
    nlinarith
  have hnum_nat : numBlocks BS ≤ 2 * BS.k0 + 1 := by
    unfold numBlocks admissibleGlobalRange at *
    omega
  have hnum :
      (numBlocks BS : ℝ) ≤ 2 * (BS.k0 : ℝ) + 1 := by
    exact_mod_cast hnum_nat
  have hAnum :
      A * (numBlocks BS : ℝ) ≤ A * (2 * (BS.k0 : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hnum hA.le
  have harg :
      A * (numBlocks BS : ℝ) -
          β * globalControlFloor BS c2 e0 ≤ -V := by
    linarith
  have hexp_le :
      Real.exp
          (A * (numBlocks BS : ℝ) -
            β * globalControlFloor BS c2 e0) ≤ Real.exp (-V) :=
    Real.exp_le_exp.mpr harg
  have htwoK0_pos : 0 < 2 * K0 := mul_pos (by norm_num) hK0_pos
  have htwoK0_nonneg : 0 ≤ 2 * K0 := htwoK0_pos.le
  have hratio_pos : 0 < (2 * K0) / η := div_pos htwoK0_pos hη
  calc
    Real.exp
          (A * (numBlocks BS : ℝ) -
            (c - (8 * eps + c) / 2) * globalControlFloor BS c2 e0) *
        (2 *
          (Real.exp (8 * eps) /
            (1 - Real.exp (-((8 * eps + c) / 2 - 8 * eps))) ^ 2))
        = Real.exp
          (A * (numBlocks BS : ℝ) -
            β * globalControlFloor BS c2 e0) * (2 * K0) := by
            rw [hβ_def, hK0_def]
    _ ≤ Real.exp (-V) * (2 * K0) := by
        exact mul_le_mul_of_nonneg_right hexp_le htwoK0_nonneg
    _ = η := by
        rw [hV_def, Real.exp_neg, Real.exp_log hratio_pos]
        field_simp [hK0_pos.ne', hη.ne']

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
  intro η hη
  classical
  set cbar : ℝ := (8 * eps + c) / 2 with hcbar_def
  set K0 : ℝ := Real.exp (8 * eps) /
    (1 - Real.exp (-(cbar - 8 * eps))) ^ 2 with hK0_def
  obtain ⟨k0grow, hgrow⟩ :=
    Pifloor_superlinear c hc eps A c2 e0 heps hepsc hA hc2 he0 η hη
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
  have hlap := sectorI_full_laplace_bound cbar eps A hcbar_pos h8eps_nonneg
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
    rw [sectorI_fintype_subtype_tsum_eq
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
