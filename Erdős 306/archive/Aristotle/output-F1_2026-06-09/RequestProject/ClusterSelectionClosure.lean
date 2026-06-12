/-
# ClusterSelectionClosure

Reciprocal-cluster selection closure: proves that in the large-pool regime
a **good seed tuple always exists**, i.e. turns the trichotomy of
`AnchoredSelectionPipeline.anchored_selection_pipeline` into the single
conclusion `hasAnchoredGoodKSubset`.

**⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
This file is part of the rational-collision / CRT-lattice component.
-/
import Mathlib
import RequestProject.AnchoredSelectionPipeline

open Finset
open Classical

noncomputable section

/-! ## Step 1: Covered ⇒ codegree ≥ 1 -/

/-
If `S` is covered by some cluster in `Clusters`, then the codegree of `S`
    (the number of clusters containing `S`) is at least 1.
-/
theorem codegree_pos_of_covered
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (S : Finset U)
    (h : coveredBySomeCluster Clusters S) :
    1 ≤ clusterCodegree Clusters S := by
  exact Finset.card_pos.mpr ( by obtain ⟨ C, hC, hCS ⟩ := h; exact ⟨ C, Finset.mem_filter.mpr ⟨ hC, hCS ⟩ ⟩ )

/-! ## Step 2: All-covered ⇒ incidence ≥ C(|F|, k) -/

/-
The number of `k`-element subsets of `F` equals `Nat.choose F.card k`.
-/
theorem card_powerset_filter_eq_choose
    {U : Type*} [DecidableEq U]
    (F : Finset U) (k : ℕ) :
    (F.powerset.filter (fun T => T.card = k)).card = Nat.choose F.card k := by
  rw [ ← Finset.powersetCard_eq_filter ] ; aesop;

/-
If all `k`-subsets of `F` are covered, then the total incidence is at least
    `Nat.choose F.card k`.
-/
theorem incidence_ge_choose_of_allCovered
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ)
    (hall : allKSubsetsCovered Clusters F k) :
    Nat.choose F.card k ≤ subsetClusterIncidence Clusters F k := by
  convert incidence_lower_of_all_high_codegree Clusters F k 1 _ using 1;
  · rw [ mul_one, card_powerset_filter_eq_choose ];
  · exact fun T hT hTk => codegree_pos_of_covered Clusters T ( hall T hT hTk )

/-! ## Step 3: Cluster-size bound -/

/-
The anchored cluster is a subset of `F`, so `F ∩ cluster ⊆ F`. This is
    a trivial structural fact; the nontrivial cluster-size bound is captured
    by the hypothesis `hL` in the main theorem.
-/
theorem anchoredCluster_subset_F
    (Short : ℤ → Prop) (F : Finset ℤ) (p q0 x0 : ℤ) :
    anchoredCluster Short F p q0 x0 ⊆ F := by
  exact Finset.filter_subset _ _

/-
Intersection of `F` with an anchored cluster equals the cluster itself.
-/
theorem inter_anchoredCluster_eq
    (Short : ℤ → Prop) (F : Finset ℤ) (p q0 x0 : ℤ) :
    F ∩ anchoredCluster Short F p q0 x0 = anchoredCluster Short F p q0 x0 := by
  exact Finset.inter_eq_right.mpr ( anchoredCluster_subset_F Short F p q0 x0 )

/-! ## Step 4: Family-count bound -/

/-
The anchored cluster family has at most `P.card * X0.card` clusters.
-/
theorem anchoredClusterFamily_card_le
    (Short : ℤ → Prop)
    (F P X0 : Finset ℤ) (q0 : ℤ) :
    (anchoredClusterFamily Short F P X0 q0).card ≤ P.card * X0.card := by
  exact Finset.card_image_le.trans_eq ( Finset.card_product _ _ )

/-! ## Step 5: Arithmetic contradiction -/

/-
If all `k`-subsets are covered, then
    `Nat.choose F.card k ≤ Clusters.card * Nat.choose L k`
    where `L` is the cluster intersection size bound.
-/
theorem allCovered_incidence_contradiction
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k L : ℕ)
    (hall : allKSubsetsCovered Clusters F k)
    (hL : ∀ C ∈ Clusters, (F ∩ C).card ≤ L) :
    Nat.choose F.card k ≤ Clusters.card * Nat.choose L k := by
  exact le_trans ( incidence_ge_choose_of_allCovered Clusters F k hall ) ( incidence_le_clusters_mul_choose Clusters F k L hL )

/-
Main theorem: if the regime inequality
    `Clusters.card * Nat.choose L k < Nat.choose F.card k` holds,
    then a good k-subset must exist.
-/
theorem good_kSubset_of_regime_contradiction
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k L : ℕ)
    (hL : ∀ C ∈ Clusters, (F ∩ C).card ≤ L)
    (hregime : Clusters.card * Nat.choose L k < Nat.choose F.card k) :
    hasGoodKSubset Clusters F k := by
  contrapose! hregime;
  convert allCovered_incidence_contradiction Clusters F k L _ hL;
  exact Classical.not_not.1 fun h => hregime <| Or.resolve_right ( good_or_allKSubsetsCovered Clusters F k ) h

/-! ## Main result: good k-subset exists from anchored cluster parameters -/

/-
In the anchored setting, if the arithmetic regime
    `(anchoredClusterFamily …).card * Nat.choose L k < Nat.choose F.card k` holds
    and every anchored cluster intersects `F` in at most `L` points,
    then `hasAnchoredGoodKSubset`.
-/
theorem good_kSubset_exists_of_size
    (Short : ℤ → Prop)
    (F P X0 : Finset ℤ) (q0 : ℤ) (k L : ℕ)
    (hL : ∀ C ∈ anchoredClusterFamily Short F P X0 q0,
          (F ∩ C).card ≤ L)
    (hregime : (anchoredClusterFamily Short F P X0 q0).card
        * Nat.choose L k < Nat.choose F.card k) :
    hasAnchoredGoodKSubset Short F P X0 q0 k := by
  exact good_kSubset_of_regime_contradiction _ _ _ _ hL hregime

/-
Corollary using the family cardinality bound: if
    `P.card * X0.card * Nat.choose L k < Nat.choose F.card k`
    then `hasAnchoredGoodKSubset`.
-/
theorem good_kSubset_exists_of_size'
    (Short : ℤ → Prop)
    (F P X0 : Finset ℤ) (q0 : ℤ) (k L : ℕ)
    (hL : ∀ C ∈ anchoredClusterFamily Short F P X0 q0,
          (F ∩ C).card ≤ L)
    (hregime : P.card * X0.card * Nat.choose L k < Nat.choose F.card k) :
    hasAnchoredGoodKSubset Short F P X0 q0 k := by
  convert good_kSubset_exists_of_size Short F P X0 q0 k L hL _ using 1;
  exact lt_of_le_of_lt ( Nat.mul_le_mul_right _ ( anchoredClusterFamily_card_le Short F P X0 q0 ) ) hregime

end