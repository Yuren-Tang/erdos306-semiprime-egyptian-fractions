import RequestProject.GlobalControl.Encoding.BlockData

/-!
# Global control energy budgets

Consequences of a global control-energy bound for internal block energy,
energy shells, hot-block thresholds, and consecutive-block energy.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- The bipartite cross-energy between blocks `k` and `k + 1`. -/
def Xen (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  ∑ pq ∈ bipartitePairs BS k,
    ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2

/-- Internal block energies consume at most the global control-energy budget. -/
lemma sum_blockEnergy_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Icc BS.k0 BS.K, blockEnergy BS a k ≤ R := by
  refine le_trans ?_ hR
  refine le_trans ?_ (energy_splits BS a)
  exact le_add_of_le_of_nonneg (Finset.sum_le_sum fun _ _ => le_rfl)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The integer block-energy shells consume at most the same budget. -/
lemma sum_shellVec_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Icc BS.k0 BS.K, (shellVec BS a k : ℝ) ≤ R := by
  refine le_trans ?_ (sum_blockEnergy_le BS a R hR)
  exact Finset.sum_le_sum fun _ _ =>
    Nat.floor_le (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Every block-energy shell is bounded by the floor of the global budget. -/
lemma shellVec_le_floorR (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (_hR0 : 0 ≤ R) (hR : Qctrl BS a ≤ R) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    shellVec BS a k ≤ ⌊R⌋₊ := by
  refine Nat.floor_mono ?_
  exact le_trans
    (Finset.single_le_sum
      (fun x _ => show 0 ≤ blockEnergy BS a x from
        Finset.sum_nonneg fun _ _ => sq_nonneg _) hk)
    (sum_blockEnergy_le BS a R hR)

/-- The forcing floors of all hot blocks consume at most the global budget. -/
lemma sum_Rw_hot_le (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ hotSet BS c2 a, Rw c2 k ≤ R := by
  refine le_trans ?_ (sum_blockEnergy_le BS a R hR)
  refine le_trans (Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2) ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Consecutive-block energies consume at most the global control-energy budget. -/
lemma sum_bipartite_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Ico BS.k0 BS.K, Xen BS a k ≤ R := by
  refine le_trans ?_ hR
  refine le_trans ?_ (energy_splits BS a)
  exact le_add_of_nonneg_of_le
    (Finset.sum_nonneg fun _ _ => by exact_mod_cast QP_nonneg _ _)
    (Finset.sum_le_sum fun _ _ => by rfl)

end GlobalControl

end
