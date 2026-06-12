import Mathlib
import RequestProject.BucketCore
import RequestProject.BucketContainer
import RequestProject.BucketFingerprint

/-!
# BucketExposure: First-level bucket exposure interface

This file does **not** prove SBEE. It assembles the finite first-level bucket
exposure mechanism used in the SBEE bucket-container argument. The deeper
reduced-ambient inverse problem is intentionally not formalized here.

## Mathematical purpose

Large incidence mass in a bucket core
→ choose a small fingerprint using `greedy_fingerprint`
→ generated bucket core has controlled size using `generatedBuckets_card_le`
→ high-multiplicity container has controlled size using `BucketContainer.lean`.

## Contents

- **Part A**: `ExposureOutput` structure recording the output of one exposure.
- **Part B**: Fingerprint existence restated from `greedy_fingerprint`.
- **Part C**: Generated core size bound via `generatedBuckets_card_le`.
- **Part D**: Captured mass into the generated core equals `capturedMass`.
- **Part E**: Container cardinality wrapper combining size bounds.
- **Part F**: Assembled exposure theorem.
-/

open Finset BigOperators

/-! ## Definitional bridges

`bucketNeighbourhood` from `BucketFingerprint` and `generatedBuckets` from
`BucketContainer` are definitionally equal. Similarly for `vertexContribution`
and `vertexBucketDegree`. We record these as `rfl` lemmas for clarity.
-/

theorem generatedBuckets_eq_bucketNeighbourhood
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (F : Finset U) (Core : Finset B) :
    generatedBuckets Inc F Core = bucketNeighbourhood Inc F Core := rfl

theorem vertexBucketDegree_eq_vertexContribution
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Core : Finset B) (u : U) :
    vertexBucketDegree Inc Core u = vertexContribution Inc u Core := rfl

/-! ## High-multiplicity container (local definition matching user interface) -/

/-- High-multiplicity container: vertices in `Uset` with at least `h` incident
    buckets in `Core`. This is definitionally equal to `highMultiplicityContainerIn`
    from `BucketContainer`. -/
def highMultiplicityContainer
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) (h : ℕ) : Finset U :=
  Uset.filter (fun u => h ≤ (Core.filter (fun b => Inc u b)).card)

theorem highMultiplicityContainer_eq
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) (h : ℕ) :
    highMultiplicityContainer Inc Uset Core h =
      highMultiplicityContainerIn Inc Uset Core h := rfl

/-! ## Part A — Exposure package structure -/

/-- The output of one exposure step: a fingerprint, its generated bucket core,
    and the resulting high-multiplicity container. -/
structure ExposureOutput
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) (r h : ℕ) where
  F : Finset U
  F_subset : F ⊆ Uset
  F_card_le : F.card ≤ r
  Gen : Finset B
  Gen_eq : Gen = bucketNeighbourhood Inc F Core
  Gen_subset : Gen ⊆ Core
  Container : Finset U
  Container_eq :
    Container = highMultiplicityContainer Inc Uset Gen h

/-! ## Part B — Fingerprint existence -/

/-- Restated fingerprint existence: if `r ≤ Uset.card`, there exists
    `F ⊆ Uset` with `F.card ≤ r` capturing at least an `r/|Uset|` fraction
    of the incidence mass. This is exactly `greedy_fingerprint`. -/
theorem fingerprint_exists
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B)
    (r : ℕ) (hr : r ≤ Uset.card) :
    ∃ F : Finset U,
      F ⊆ Uset ∧
      F.card ≤ r ∧
      capturedMass Inc Uset F Core * Uset.card ≥
        incidenceMass Inc Uset Core * r :=
  greedy_fingerprint Inc Uset Core r hr

/-! ## Part C — Generated core size -/

/-- The generated bucket neighbourhood has at most `F.card * M` buckets,
    when every vertex in `Uset` has degree into `Core` at most `M` and `F ⊆ Uset`. -/
theorem bucketNeighbourhood_card_le
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (F : Finset U) (Uset : Finset U) (Core : Finset B) (M : ℕ)
    (hF : F ⊆ Uset)
    (hM : ∀ u ∈ Uset, (Core.filter (fun b => Inc u b)).card ≤ M) :
    (bucketNeighbourhood Inc F Core).card ≤ F.card * M := by
  rw [← generatedBuckets_eq_bucketNeighbourhood]
  exact generatedBuckets_card_le Inc F Core M
    (fun v hv => by rw [vertexBucketDegree]; exact hM v (hF hv))

/-- Corollary: if `F.card ≤ r`, then the generated core has at most `r * M` buckets. -/
theorem bucketNeighbourhood_card_le_mul
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (F : Finset U) (Uset : Finset U) (Core : Finset B) (r M : ℕ)
    (hF : F ⊆ Uset) (hFr : F.card ≤ r)
    (hM : ∀ u ∈ Uset, (Core.filter (fun b => Inc u b)).card ≤ M) :
    (bucketNeighbourhood Inc F Core).card ≤ r * M :=
  le_trans (bucketNeighbourhood_card_le Inc F Uset Core M hF hM)
    (Nat.mul_le_mul_right M hFr)

/-! ## Part D — Captured mass into the generated core -/

/-- The incidence mass into the generated bucket neighbourhood equals
    `capturedMass`, by definition. -/
theorem incidenceMass_bucketNeighbourhood_eq_capturedMass
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset F : Finset U) (Core : Finset B) :
    incidenceMass Inc Uset (bucketNeighbourhood Inc F Core) =
      capturedMass Inc Uset F Core := rfl

/-! ## Part E — Container cardinality wrapper -/

/-- Container bound using the generated core: if the sum-of-choose-2 hypothesis
    holds for the generated core, and `2 ≤ h`, then
    `container.card * (h * (h - 1)) ≤ Gen.card * Gen.card`. -/
theorem container_card_bound_from_gen
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Gen : Finset B) (h : ℕ) (hh : 2 ≤ h)
    (hsum : ∑ v ∈ Uset,
        Nat.choose (vertexBucketDegree Inc Gen v) 2
      ≤ Nat.choose Gen.card 2) :
    (highMultiplicityContainer Inc Uset Gen h).card * (h * (h - 1))
      ≤ Gen.card * Gen.card := by
  rw [highMultiplicityContainer_eq]
  exact container_card_numeric_bound
    (highMultiplicityContainerIn Inc Uset Gen h).card h Gen.card hh
    (highMultiplicityContainer_card_bound_from_sum Inc Uset Gen h hsum)

/-- Combined: if `Gen.card ≤ r * M` and we have the sum-of-choose-2 bound,
    then `container.card * (h * (h-1)) ≤ (r * M) * (r * M)`. -/
theorem container_card_bound_rM
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Gen : Finset B) (r M h : ℕ) (hh : 2 ≤ h)
    (hGen : Gen.card ≤ r * M)
    (hsum : ∑ v ∈ Uset,
        Nat.choose (vertexBucketDegree Inc Gen v) 2
      ≤ Nat.choose Gen.card 2) :
    (highMultiplicityContainer Inc Uset Gen h).card * (h * (h - 1))
      ≤ (r * M) * (r * M) := by
  rw [highMultiplicityContainer_eq]
  apply container_card_numeric_bound _ h (r * M) hh
  exact le_trans
    (highMultiplicityContainer_card_bound_from_sum Inc Uset Gen h hsum)
    (Nat.choose_le_choose 2 hGen)

/-! ## Part F — Assembled exposure theorem -/

/-- **First-level bucket exposure theorem.**

Given:
1. `r ≤ Uset.card` (fingerprint size parameter);
2. vertex degree into `Core` is at most `M`;
3. a sum-of-choose-2 bound for every sub-core (from e.g. `marked_dual_large_sieve`);
4. `2 ≤ h` (multiplicity threshold);

there exists a fingerprint `F` with `F.card ≤ r`, a generated core `Gen`,
and a container `Container`, such that:
- `Gen.card ≤ r * M`;
- captured mass is at least the greedy fraction;
- the high-multiplicity container satisfies the numeric cardinality bound. -/
theorem first_level_exposure
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) (r M h : ℕ)
    (hr : r ≤ Uset.card) (hh : 2 ≤ h)
    (hM : ∀ u ∈ Uset, (Core.filter (fun b => Inc u b)).card ≤ M)
    (hChoose : ∀ Gen : Finset B, Gen ⊆ Core →
      ∑ v ∈ Uset, Nat.choose (vertexBucketDegree Inc Gen v) 2
        ≤ Nat.choose Gen.card 2) :
    ∃ (F : Finset U) (Gen : Finset B) (Container : Finset U),
      F ⊆ Uset ∧
      F.card ≤ r ∧
      Gen = bucketNeighbourhood Inc F Core ∧
      Gen ⊆ Core ∧
      Gen.card ≤ r * M ∧
      Container = highMultiplicityContainer Inc Uset Gen h ∧
      capturedMass Inc Uset F Core * Uset.card ≥
        incidenceMass Inc Uset Core * r ∧
      Container.card * (h * (h - 1)) ≤ (r * M) * (r * M) := by
  obtain ⟨F, hFsub, hFcard, hFmass⟩ := greedy_fingerprint Inc Uset Core r hr
  let Gen := bucketNeighbourhood Inc F Core
  let Container := highMultiplicityContainer Inc Uset Gen h
  refine ⟨F, Gen, Container, hFsub, hFcard, rfl,
    bucketNeighbourhood_subset_core Inc F Core, ?_, rfl, hFmass, ?_⟩
  · exact bucketNeighbourhood_card_le_mul Inc F Uset Core r M hFsub hFcard hM
  · exact container_card_bound_rM Inc Uset Gen r M h hh
      (bucketNeighbourhood_card_le_mul Inc F Uset Core r M hFsub hFcard hM)
      (hChoose Gen (bucketNeighbourhood_subset_core Inc F Core))

/-- Variant of the assembled theorem that also produces an `ExposureOutput`. -/
theorem exposure_output_exists
    {U B : Type*} [DecidableEq U] [DecidableEq B]
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) (r M h : ℕ)
    (hr : r ≤ Uset.card)
    (hM : ∀ u ∈ Uset, (Core.filter (fun b => Inc u b)).card ≤ M) :
    ∃ (eo : ExposureOutput Inc Uset Core r h),
      eo.Gen.card ≤ r * M ∧
      capturedMass Inc Uset eo.F Core * Uset.card ≥
        incidenceMass Inc Uset Core * r := by
  obtain ⟨F, hFsub, hFcard, hFmass⟩ := greedy_fingerprint Inc Uset Core r hr
  exact ⟨{
    F := F
    F_subset := hFsub
    F_card_le := hFcard
    Gen := bucketNeighbourhood Inc F Core
    Gen_eq := rfl
    Gen_subset := bucketNeighbourhood_subset_core Inc F Core
    Container := highMultiplicityContainer Inc Uset (bucketNeighbourhood Inc F Core) h
    Container_eq := rfl
  },
  bucketNeighbourhood_card_le_mul Inc F Uset Core r M hFsub hFcard hM,
  hFmass⟩
