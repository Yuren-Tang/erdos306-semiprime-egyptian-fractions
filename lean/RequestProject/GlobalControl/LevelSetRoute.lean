import RequestProject.GlobalControl.LevelSetAdmissibility
import RequestProject.GlobalControl.LevelSetFiberBound

/-!
# Global level-set route

The handoff theorem composing the finite cover, admissibility, and aggregate
fiber estimate.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### Route closure (confirms the cover layer composes to `global_levelset`)

This lemma wires the verified cover layer (`cover_card_le` + the four proved
admissibility facts + the cold-class bound) into the *exact* per-`BS` body of
`GlobalControl.global_levelset`.  The only inputs left open are:
  * `hadmL` — the label-range admissibility (`extLabel ∈ admLabels`), the one
    remaining numeric estimate; and
  * `hrhs` — the arithmetic bound on the four-fold fiber sum (the ε-budget).
together with the existential-derived facts `hX0`/`hpen`/`hdom` (supplied by
`cold_isDominant` and `boundary_penalty_per_k` in the final assembly).  Its
type-checking is the machine confirmation that the route closes. -/
lemma global_levelset_route (BS : BlockSystem) (eps c2 e0 X0 R A : ℝ)
    (hR0 : 0 ≤ R)
    (hX0 : X0 ≤ (2:ℝ) ^ BS.k0)
    (hpen : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        ∀ k, BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k →
        k ∈ boundarySet BS c2 a → Pifloor BS e0 k ≤ Xen BS a k)
    (hdom : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4))
    (hadmL : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a)
          ∈ admLabels BS c2 R (hotSet BS c2 a) (boundarySet BS c2 a))
    (hrhs : (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
        ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
        Real.exp (A * (numBlocks BS : ℝ)) *
          Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS)) :
    (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
      Real.exp (A * (numBlocks BS : ℝ)) *
        Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  have hbridge : ({a : GlobalAssignment BS | Qctrl BS a ≤ R}).ncard
      = (Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  have hcov := cover_card_le BS c2 e0 R
    (fun a ha => hotSet_mem_admH BS c2 a R ha)
    (fun a ha => boundarySet_mem_admB BS c2 e0 X0 R a hX0 (hpen a ha) ha)
    (fun a ha => extShell_mem_admShells BS c2 R a hR0 ha)
    hadmL
    (fun a ha => cold_class_of_isDominant BS c2 a (hdom a ha))
  calc (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ)
      = ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) := by
        rw [hbridge]
    _ ≤ (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) := by exact_mod_cast hcov
    _ ≤ _ := hrhs

end GlobalControl

end
