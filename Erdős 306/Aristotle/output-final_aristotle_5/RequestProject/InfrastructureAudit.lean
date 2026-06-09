import RequestProject.BucketCore
import RequestProject.BucketContainer
import RequestProject.BucketFingerprint
import RequestProject.BucketExposure
import RequestProject.BucketBudget
import RequestProject.BipartiteCycles
import RequestProject.RankOneRigidity

/-!
# InfrastructureAudit: dependency sanity check and bridge lemmas

This file audits and lightly bridges the existing finite-combinatorial
infrastructure without modifying any existing files.

No sorry, no `True := trivial`, no new axioms.
-/

namespace RequestProject.InfrastructureAudit

/-! ## Task 1 — Dependency sanity check

We verify that the main exported theorems from every imported file are
available by stating harmless `example` declarations that simply reference
them. Each block documents which file supplies the theorem.
-/

-- BucketCore
example := @bucketCollisionUpper_le_mul_mass
example := @bucketIncidenceMass_eq_sum_degrees
example := @bucketIncidenceMass_le_card_mul
example := @bucketCollisionUpper_le
example := @cheap_plus_expensive_eq_cross
example := @deficit_cross_pairs
example := @cheapCross_le_two_mul_collision
example := @marked_dual_large_sieve

-- BucketContainer
example := @generatedBuckets_card_le
example := @highMultiplicity_card_mul_choose_le
example := @highMultiplicityContainer_card_bound_from_sum
example := @container_bound_from_marked_dual_large_sieve
example := @container_card_numeric_bound

-- BucketFingerprint
example := @incidenceMass_eq_sum_contributions
example := @exists_vertex_above_average
example := @capturedMass_ge_sum_contributions
example := @greedy_fingerprint

-- BucketExposure
example := @generatedBuckets_eq_bucketNeighbourhood
example := @vertexBucketDegree_eq_vertexContribution
example := @highMultiplicityContainer_eq
example := @fingerprint_exists
example := @bucketNeighbourhood_card_le
example := @bucketNeighbourhood_card_le_mul
example := @container_card_bound_from_gen
example := @container_card_bound_rM
example := @first_level_exposure
example := @exposure_output_exists

-- BucketBudget
example := @incidenceMass_mono_buckets
example := @incidenceMass_mono_vertices
example := @incidenceMass_eq_bucketIncidenceMass
example := @incidenceMass_le_card_mul_degree
example := @sum_incidenceMass_disjoint_le
example := @budget_bound_mass
example := @budget_bound_combined
example := @newCore_subset
example := @newCore_disjoint
example := @newCores_disjoint_of_cumulative

-- BipartiteCycles
example := @ordered_double_counting
example := @common_neighbour_mass_lower_bound

-- RankOneRigidity
example := @rankOne_decomposition_of_mixed_zero
example := @mixed_zero_of_rankOne_decomposition

/-! ## Task 2 — Bridge: exposure richness → common-neighbour mass

This is a restatement of `common_neighbour_mass_lower_bound` using
variable names that match the exposure language:

* `fingerprint` plays the role of `X` (the "left" side),
* `captured` plays the role of `Y` (the "right" side),
* `richness` plays the role of the minimum degree threshold `h`.

The theorem says: if every element of `captured` has at least `richness`
neighbours in `fingerprint`, then the ordered common-neighbour mass is
at least `captured.card * (richness * (richness - 1))`.
-/
theorem exposure_richness_to_commonNeighbourMass
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (Adj : A → B → Prop) [DecidableRel Adj]
    (fingerprint : Finset A) (captured : Finset B) (richness : ℕ)
    (hrich : ∀ y ∈ captured, richness ≤ degreeRight Adj fingerprint y) :
    captured.card * (richness * (richness - 1)) ≤
      ∑ x ∈ fingerprint,
        ∑ x' ∈ fingerprint.filter (fun x' => x' ≠ x),
          commonNeighboursRight Adj captured x x' :=
  common_neighbour_mass_lower_bound Adj fingerprint captured richness hrich

/-! ## Task 3 — Bridge: repeated exposure → round budget

This is a restatement of `budget_bound_combined` in the language of
repeated exposure rounds. Each round `i` generates a core `Cores i`
carrying at least `m` incidence mass; cores are pairwise disjoint
subsets of `AllBuckets`; every vertex has bucket degree at most `M`.
The conclusion is the multiplicative inequality
`Idx.card * m ≤ Uset.card * M`, which bounds the number of rounds
without invoking division.
-/
theorem repeated_exposure_round_budget
    {U B ι : Type*} [DecidableEq U] [DecidableEq B] [DecidableEq ι]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (AllBuckets : Finset B)
    (Idx : Finset ι) (Cores : ι → Finset B) (m M : ℕ)
    (hSub : ∀ i ∈ Idx, Cores i ⊆ AllBuckets)
    (hDisj : ∀ i ∈ Idx, ∀ j ∈ Idx, i ≠ j →
      Disjoint (Cores i) (Cores j))
    (hMin : ∀ i ∈ Idx, m ≤ incidenceMass Inc Uset (Cores i))
    (hDeg : ∀ u ∈ Uset,
      (AllBuckets.filter (fun b => Inc u b)).card ≤ M) :
    Idx.card * m ≤ Uset.card * M :=
  budget_bound_combined Inc Uset AllBuckets Idx Cores m M
    hSub hDisj hMin hDeg

/-! ## Task 4 — Rank-one usability aliases

These provide names closer to the paper language
("zero rectangle defect" ↔ "rank-one decomposition").
-/

/-- If every mixed second difference of `a` vanishes (i.e. the rectangle
defect is zero), then `a` decomposes as `α x + β y`. -/
theorem zero_rectangle_defect_implies_rankOne
    {X Y : Type*}
    (a : X → Y → ℤ) (x₀ : X) (y₀ : Y)
    (h : mixed_second_zero a) :
    let alpha : X → ℤ := fun x => a x y₀
    let beta  : Y → ℤ := fun y => a x₀ y - a x₀ y₀
    ∀ x y, a x y = alpha x + beta y :=
  rankOne_decomposition_of_mixed_zero a x₀ y₀ h

/-- If `a` has the form `α x + β y`, then every mixed second difference
vanishes (the rectangle defect is zero). -/
theorem rankOne_implies_zero_rectangle_defect
    {X Y : Type*}
    (alpha : X → ℤ) (beta : Y → ℤ) :
    mixed_second_zero (fun x y => alpha x + beta y) :=
  mixed_zero_of_rankOne_decomposition alpha beta

end RequestProject.InfrastructureAudit

/-!
## Task 5 — Summary

### What this file bridges

1. **Exposure → common-neighbour mass.**
   `exposure_richness_to_commonNeighbourMass` restates the common-neighbour
   mass lower bound (`BipartiteCycles.common_neighbour_mass_lower_bound`)
   with variable names matching the exposure language (fingerprint, captured,
   richness).

2. **Repeated exposure → budget control.**
   `repeated_exposure_round_budget` restates `BucketBudget.budget_bound_combined`
   in the language of exposure rounds, giving `Idx.card * m ≤ Uset.card * M`
   without division.

3. **Zero rectangle defect ↔ rank-one decomposition.**
   `zero_rectangle_defect_implies_rankOne` and
   `rankOne_implies_zero_rectangle_defect` are paper-language aliases for
   `rankOne_decomposition_of_mixed_zero` and
   `mixed_zero_of_rankOne_decomposition`.

### What this file deliberately does NOT prove

- SBEE (the single remaining analytic condition).
- PCER (Peierls collapse energy reduction).
- Shifted Irving-good charging.
- Any analytic estimate (Fourier bounds, Kloosterman sums, etc.).
- The reduced-ambient inverse theorem.
-/
