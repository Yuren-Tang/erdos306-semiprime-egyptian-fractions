/-
# AdaptiveClusterSelection

Finite selection and incidence bookkeeping around the cluster-cover lemma.
Formalizes the dichotomy: either a good k-set exists, or low-codegree cover

**⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
This file is part of the rational-collision / CRT-lattice component,
which is sorry-free algebra/combinatorics but is **disconnected** from
the main theorem `erdos_306`. The top result of this component,
`ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
assumes the shell bound as a hypothesis.
/ high-codegree incidence mass applies.

No SBEE, no number theory, no analytic assumptions.
-/
import Mathlib
import RequestProject.ClusterCoverBookkeeping

open Finset

/-! ## Goal 1: Cluster codegree -/

/-- The cluster codegree of `T` is the number of clusters containing `T`. -/
@[reducible]
def clusterCodegree
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (T : Finset U) : ℕ :=
  (clustersContaining Clusters T).card

theorem clusterCodegree_def
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (T : Finset U) :
    clusterCodegree Clusters T = (clustersContaining Clusters T).card :=
  rfl

/-! ## Goal 2: Good tuple / all-covered dichotomy -/

/-- Every `k`-element subset of `F` is covered by some cluster. -/
def allKSubsetsCovered
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ) : Prop :=
  ∀ S : Finset U, S ⊆ F → S.card = k → coveredBySomeCluster Clusters S

/-- There exists a `k`-element subset of `F` not covered by any cluster. -/
def hasGoodKSubset
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ) : Prop :=
  ∃ S : Finset U, S ⊆ F ∧ S.card = k ∧ ¬ coveredBySomeCluster Clusters S

theorem good_or_allKSubsetsCovered
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ) :
    hasGoodKSubset Clusters F k ∨ allKSubsetsCovered Clusters F k := by
  by_cases h : ∀ S : Finset U, S ⊆ F → S.card = k → coveredBySomeCluster Clusters S
  · exact Or.inr h
  · push_neg at h
    exact Or.inl h

/-! ## Goal 3: Low-codegree cover bound -/

theorem allCovered_lowCodegree_gives_card_bound
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U) (k L R : ℕ)
    (hTsub : T ⊆ F)
    (hTcard : T.card + 1 = k)
    (hall : allKSubsetsCovered Clusters F k)
    (hR : clusterCodegree Clusters T ≤ R)
    (hL : ∀ C ∈ clustersContaining Clusters T, C.card ≤ L) :
    F.card ≤ T.card + R * L := by
  have hext : ∀ v ∈ F, v ∉ T → coveredBySomeCluster Clusters (insert v T) := by
    exact ksubset_cover_gives_extension_cover Clusters F T k hTsub hTcard
      (fun S hSF hScard hTS => hall S hSF hScard)
  exact card_le_of_extension_cover' Clusters F T L R hTsub hext hR hL

/-! ## Goal 4: Incidence ledger -/

/-- Incidence count: sum of cluster codegrees over all `m`-element subsets of `F`. -/
def subsetClusterIncidence
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (m : ℕ) : ℕ :=
  ∑ T ∈ F.powerset.filter (fun T => T.card = m),
    clusterCodegree Clusters T

/-- Lower bound: if every `m`-subset has codegree ≥ R, the total incidence is large. -/
theorem incidence_lower_of_all_high_codegree
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (m R : ℕ)
    (hhigh : ∀ T, T ⊆ F → T.card = m → R ≤ clusterCodegree Clusters T) :
    (F.powerset.filter (fun T => T.card = m)).card * R
      ≤ subsetClusterIncidence Clusters F m := by
  unfold subsetClusterIncidence
  exact Finset.card_nsmul_le_sum _ _ _ (fun T hT => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    exact hhigh T hT.1 hT.2)

/-
Double-counting upper bound:
    ∑_{T ⊆ F, |T|=m} #{C : T ⊆ C} ≤ ∑_{C ∈ Clusters} #{T ⊆ F ∩ C : |T|=m}.
-/
theorem incidence_upper_bound
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (m : ℕ) :
    subsetClusterIncidence Clusters F m
      ≤ ∑ C ∈ Clusters, ((F ∩ C).powerset.filter (fun T => T.card = m)).card := by
  unfold subsetClusterIncidence;
  simp +decide only [clusterCodegree, clustersContaining, card_filter];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro C hC;
  simp +decide;
  congr 1 with x ; simp +contextual [ Finset.subset_iff ];
  constructor <;> intro h;
  · exact ⟨ ⟨ x, h.1.1, x, h.2, by aesop ⟩, h.1.2 ⟩;
  · grind

/-! ## Goal 5: Optional cardinal upper bound -/

/-
If every cluster intersects `F` in at most `L` points, the incidence is bounded.
-/
theorem incidence_le_clusters_mul_choose
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (m L : ℕ)
    (hL : ∀ C ∈ Clusters, (F ∩ C).card ≤ L) :
    subsetClusterIncidence Clusters F m
      ≤ Clusters.card * Nat.choose L m := by
  convert incidence_upper_bound Clusters F m |> le_trans <| Finset.sum_le_card_nsmul _ _ _ _;
  intro C hC; specialize hL C hC; simp_all +decide;
  rw [ ← Finset.powerset_inter ];
  rw [ ← Finset.powersetCard_eq_filter ] ; exact Finset.card_powersetCard _ _ ▸ Nat.choose_le_choose _ hL;