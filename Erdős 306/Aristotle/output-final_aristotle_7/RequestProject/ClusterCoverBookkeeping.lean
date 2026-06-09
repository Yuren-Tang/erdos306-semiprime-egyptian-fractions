/-
# ClusterCoverBookkeeping

Pure finite set-system bookkeeping for the reciprocal-cluster selection step
of the Erdős 306 conditional proof.

No SBEE, no number theory, no analytic assumptions.
-/
import Mathlib

open Finset

/-! ## Goal 1: Definitions -/

/-- A finite set `S` is covered by some cluster in `Clusters`. -/
def coveredBySomeCluster
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (S : Finset U) : Prop :=
  ∃ C ∈ Clusters, S ⊆ C

/-- The sub-family of clusters that contain a given set `T`. -/
def clustersContaining
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (T : Finset U) : Finset (Finset U) :=
  Clusters.filter (fun C => T ⊆ C)

/-- The union of all sets in a finite family. -/
def unionClusters
    {U : Type*} [DecidableEq U]
    (Cs : Finset (Finset U)) : Finset U :=
  Cs.biUnion id

/-! ## Goal 2: One-set extension cover lemma -/

/-- If every element `v ∈ F` has `insert v T` covered by some cluster,
then `F ⊆ T ∪ ⋃(clusters containing T)`. -/
theorem covered_extension_subset_unionContaining
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U)
    (_hT : T ⊆ F)
    (hcover : ∀ v ∈ F, coveredBySomeCluster Clusters (insert v T)) :
    F ⊆ T ∪ unionClusters (clustersContaining Clusters T) := by
  intro v hv; by_cases hvT : v ∈ T <;> simp_all +decide [ unionClusters, clustersContaining ] ;
  rcases hcover v hv with ⟨ C, hC₁, hC₂ ⟩ ; exact ⟨ C, ⟨ hC₁, Finset.Subset.trans ( Finset.subset_insert _ _ ) hC₂ ⟩, hC₂ ( Finset.mem_insert_self _ _ ) ⟩ ;

/-! ## Goal 3: Cardinal cover bound -/

/-- The union of clusters containing `T` has at most `R * L` elements
when there are at most `R` such clusters each of size at most `L`. -/
theorem card_unionClusters_le
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (T : Finset U) (L R : ℕ)
    (hR : (clustersContaining Clusters T).card ≤ R)
    (hL : ∀ C ∈ clustersContaining Clusters T, C.card ≤ L) :
    (unionClusters (clustersContaining Clusters T)).card ≤ R * L := by
  exact card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => hL x hx ) |> le_trans <| by simpa using mul_le_mul_right' hR L;

/-- Combining the extension cover lemma with the cardinality bound. -/
theorem card_le_of_extension_cover
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U) (L R : ℕ)
    (hT : T ⊆ F)
    (hcover : ∀ v ∈ F, coveredBySomeCluster Clusters (insert v T))
    (hR : (clustersContaining Clusters T).card ≤ R)
    (hL : ∀ C ∈ clustersContaining Clusters T, C.card ≤ L) :
    F.card ≤ T.card + R * L := by
  have h_union_bound : F.card ≤ T.card + (unionClusters (clustersContaining Clusters T)).card := by
    exact le_trans ( Finset.card_le_card ( covered_extension_subset_unionContaining Clusters F T hT hcover ) ) ( Finset.card_union_le _ _ );
  exact h_union_bound.trans ( Nat.add_le_add_left ( card_unionClusters_le Clusters T L R hR hL ) _ )

/-! ## Goal 2': Variant with weaker hypothesis (only v ∉ T needed) -/

/-
The extension cover lemma only needs `insert v T` covered for `v ∉ T`,
since elements of `T` are already in the left summand.
-/
theorem covered_extension_subset_unionContaining'
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U)
    (_hT : T ⊆ F)
    (hcover : ∀ v ∈ F, v ∉ T → coveredBySomeCluster Clusters (insert v T)) :
    F ⊆ T ∪ unionClusters (clustersContaining Clusters T) := by
  intro v hv; by_cases hvT : v ∈ T <;> simp_all +decide [ coveredBySomeCluster ] ;
  obtain ⟨ C, hC₁, hC₂ ⟩ := hcover v hv hvT; exact Finset.mem_biUnion.2 ⟨ C, Finset.mem_filter.2 ⟨ hC₁, by aesop_cat ⟩, by aesop_cat ⟩ ;

/-
Cardinal bound using the weaker hypothesis.
-/
theorem card_le_of_extension_cover'
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U) (L R : ℕ)
    (hT : T ⊆ F)
    (hcover : ∀ v ∈ F, v ∉ T → coveredBySomeCluster Clusters (insert v T))
    (hR : (clustersContaining Clusters T).card ≤ R)
    (hL : ∀ C ∈ clustersContaining Clusters T, C.card ≤ L) :
    F.card ≤ T.card + R * L := by
  -- By the previous lemma, F is a subset of T ∪ clustersContaining.
  have h_subset : F ⊆ T ∪ unionClusters (clustersContaining Clusters T) := by
    exact covered_extension_subset_unionContaining' Clusters F T hT hcover;
  refine' le_trans ( Finset.card_le_card h_subset ) ( le_trans ( Finset.card_union_le _ _ ) _ );
  exact Nat.add_le_add_left ( card_unionClusters_le _ _ _ _ hR hL ) _

/-! ## Goal 4: k-subset corollary -/

/-
If every `k`-element subset of `F` containing `T` is covered by some cluster,
`T ⊆ F`, and `T.card + 1 = k`, then for every `v ∈ F \ T`,
`insert v T` is covered. Combined with `covered_extension_subset_unionContaining'`,
this gives the seed-pool covering bound.
-/
theorem ksubset_cover_gives_extension_cover
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U) (k : ℕ)
    (hT : T ⊆ F)
    (hcard : T.card + 1 = k)
    (hkcover : ∀ S ⊆ F, S.card = k → T ⊆ S → coveredBySomeCluster Clusters S) :
    ∀ v ∈ F, v ∉ T → coveredBySomeCluster Clusters (insert v T) := by
  grind +qlia