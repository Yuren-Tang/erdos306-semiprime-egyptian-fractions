import Mathlib
import RequestProject.BucketExposure

/-!
# BucketBudget: Finite incidence-budget bookkeeping

This file formalizes only the finite incidence-budget bookkeeping:
repeated extraction of cores with large new incidence mass is bounded
by the total incidence mass. It does **not** prove the reduced-ambient
inverse theorem or SBEE.

## Mathematical purpose

In the SBEE bucket-container argument, after repeated exposures one tracks
"new incidences" captured by successive bucket cores. Since every vertex has
bounded bucket degree, the total incidence mass is bounded. Therefore one
cannot extract many disjoint/new incidence cores, each carrying a large
amount of new incidence.

## Contents

- **Part A** — Incidence mass monotonicity (in both bucket and vertex sets).
- **Part B** — Total incidence bound from vertex degree.
- **Part C** — Disjoint bucket cores: sum of masses ≤ total mass.
- **Part D** — Budget bound: `Idx.card * m ≤ Uset.card * M`.
- **Part E** — New-incidence version via `newCore`.
- **Part F** — Documentation (this header).
-/

open Finset BigOperators

/-! ## Part A — Incidence mass monotonicity -/

/-- Monotonicity of `incidenceMass` in the bucket set:
    if `B₁ ⊆ B₂` then `incidenceMass Inc Uset B₁ ≤ incidenceMass Inc Uset B₂`. -/
theorem incidenceMass_mono_buckets
    {U B : Type*}
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (B₁ B₂ : Finset B) (h : B₁ ⊆ B₂) :
    incidenceMass Inc Uset B₁ ≤ incidenceMass Inc Uset B₂ :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

/-- Monotonicity of `incidenceMass` in the vertex set:
    if `U₁ ⊆ U₂` then `incidenceMass Inc U₁ Core ≤ incidenceMass Inc U₂ Core`. -/
theorem incidenceMass_mono_vertices
    {U B : Type*} [DecidableEq U]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (U₁ U₂ : Finset U) (Core : Finset B) (h : U₁ ⊆ U₂) :
    incidenceMass Inc U₁ Core ≤ incidenceMass Inc U₂ Core :=
  Finset.sum_le_sum fun _ _ =>
    Finset.card_le_card (Finset.filter_subset_filter _ h)

/-! ## Part B — Total incidence bound from vertex degree -/

/-- `incidenceMass` and `bucketIncidenceMass` are definitionally equal. -/
theorem incidenceMass_eq_bucketIncidenceMass
    {U B : Type*}
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (AllBuckets : Finset B) :
    incidenceMass Inc Uset AllBuckets =
      bucketIncidenceMass Inc Uset AllBuckets := by
  simp [incidenceMass, bucketIncidenceMass, bucketOccupancy]

/-- If every vertex in `Uset` has degree into `AllBuckets` at most `M`, then
    `incidenceMass Inc Uset AllBuckets ≤ Uset.card * M`. -/
theorem incidenceMass_le_card_mul_degree
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (AllBuckets : Finset B) (M : ℕ)
    (hM : ∀ u ∈ Uset, (AllBuckets.filter (fun b => Inc u b)).card ≤ M) :
    incidenceMass Inc Uset AllBuckets ≤ Uset.card * M := by
  rw [incidenceMass_eq_sum_contributions]
  calc ∑ u ∈ Uset, vertexContribution Inc u AllBuckets
      = ∑ u ∈ Uset, (AllBuckets.filter (fun b => Inc u b)).card := by
        simp [vertexContribution]
    _ ≤ ∑ _u ∈ Uset, M := Finset.sum_le_sum fun u hu => hM u hu
    _ = Uset.card * M := by simp [Finset.sum_const, smul_eq_mul]

/-! ## Part C — Disjoint bucket cores -/

/-
If bucket cores indexed by `Idx` are pairwise disjoint subsets of `AllBuckets`,
    then the sum of their incidence masses is at most the total incidence mass.
-/
theorem sum_incidenceMass_disjoint_le
    {U B ι : Type*} [DecidableEq B] [DecidableEq ι]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (AllBuckets : Finset B)
    (Idx : Finset ι) (Cores : ι → Finset B)
    (hSub : ∀ i ∈ Idx, Cores i ⊆ AllBuckets)
    (hDisj : ∀ i ∈ Idx, ∀ j ∈ Idx, i ≠ j → Disjoint (Cores i) (Cores j)) :
    ∑ i ∈ Idx, incidenceMass Inc Uset (Cores i) ≤
      incidenceMass Inc Uset AllBuckets := by
  -- By definition of `incidenceMass`, we can rewrite the left-hand side of the inequality.
  simp [incidenceMass] at *;
  rw [ ← Finset.sum_biUnion ];
  · exact Finset.sum_le_sum_of_subset ( Finset.biUnion_subset.mpr hSub );
  · exact fun i hi j hj hij => hDisj i hi j hj hij

/-! ## Part D — Budget bound -/

/-- If each core carries at least `m` incidences and cores are pairwise disjoint
    subsets of `AllBuckets`, then `Idx.card * m ≤ incidenceMass Inc Uset AllBuckets`. -/
theorem budget_bound_mass
    {U B ι : Type*} [DecidableEq B] [DecidableEq ι]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (AllBuckets : Finset B)
    (Idx : Finset ι) (Cores : ι → Finset B) (m : ℕ)
    (hSub : ∀ i ∈ Idx, Cores i ⊆ AllBuckets)
    (hDisj : ∀ i ∈ Idx, ∀ j ∈ Idx, i ≠ j → Disjoint (Cores i) (Cores j))
    (hMin : ∀ i ∈ Idx, m ≤ incidenceMass Inc Uset (Cores i)) :
    Idx.card * m ≤ incidenceMass Inc Uset AllBuckets := by
  calc Idx.card * m
      ≤ ∑ i ∈ Idx, incidenceMass Inc Uset (Cores i) := by
        have := Finset.card_nsmul_le_sum Idx _ m hMin
        omega
    _ ≤ incidenceMass Inc Uset AllBuckets :=
        sum_incidenceMass_disjoint_le Inc Uset AllBuckets Idx Cores hSub hDisj

/-- Combined budget bound: if each core carries at least `m` incidences,
    cores are pairwise disjoint, and every vertex has degree ≤ `M`, then
    `Idx.card * m ≤ Uset.card * M`. -/
theorem budget_bound_combined
    {U B ι : Type*} [DecidableEq U] [DecidableEq B] [DecidableEq ι]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (AllBuckets : Finset B)
    (Idx : Finset ι) (Cores : ι → Finset B) (m M : ℕ)
    (hSub : ∀ i ∈ Idx, Cores i ⊆ AllBuckets)
    (hDisj : ∀ i ∈ Idx, ∀ j ∈ Idx, i ≠ j → Disjoint (Cores i) (Cores j))
    (hMin : ∀ i ∈ Idx, m ≤ incidenceMass Inc Uset (Cores i))
    (hM : ∀ u ∈ Uset, (AllBuckets.filter (fun b => Inc u b)).card ≤ M) :
    Idx.card * m ≤ Uset.card * M :=
  le_trans
    (budget_bound_mass Inc Uset AllBuckets Idx Cores m hSub hDisj hMin)
    (incidenceMass_le_card_mul_degree Inc Uset AllBuckets M hM)

/-! ## Part E — New-incidence version -/

/-- The new (residual) core after removing already-exposed buckets. -/
def newCore {B : Type*} [DecidableEq B] (Core Prev : Finset B) : Finset B :=
  Core \ Prev

theorem newCore_subset {B : Type*} [DecidableEq B] (Core Prev : Finset B) :
    newCore Core Prev ⊆ Core :=
  Finset.sdiff_subset

theorem newCore_disjoint {B : Type*} [DecidableEq B] (Core Prev : Finset B) :
    Disjoint (newCore Core Prev) Prev :=
  Finset.sdiff_disjoint

/-
Simpler pairwise-disjointness: if `Prev j` contains `Cores i` for all `i < j`
    (under some linear order), then residual pieces are pairwise disjoint.
-/
theorem newCores_disjoint_of_cumulative
    {B ι : Type*} [DecidableEq B] [DecidableEq ι] [LinearOrder ι]
    (Cores : ι → Finset B) (Prev : ι → Finset B)
    (Idx : Finset ι)
    (hCum : ∀ i ∈ Idx, ∀ j ∈ Idx, i < j → Cores i ⊆ Prev j) :
    ∀ i ∈ Idx, ∀ j ∈ Idx, i ≠ j →
      Disjoint (newCore (Cores i) (Prev i)) (newCore (Cores j) (Prev j)) := by
  intro i hi j hj hij; cases lt_or_gt_of_ne hij <;> simp_all +decide [ Finset.disjoint_left, newCore ] ;
  · exact fun x hx₁ hx₂ hx₃ => hCum i hi j hj ‹_› hx₁;
  · grind +ring