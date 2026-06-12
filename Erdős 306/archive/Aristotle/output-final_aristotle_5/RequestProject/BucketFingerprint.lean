import Mathlib
import RequestProject.BucketCore
import RequestProject.BucketContainer

/-!
# BucketFingerprint: Finite fingerprint-exposure lemmas for bipartite incidence graphs

This file formalizes the fingerprint-exposure component of the SBEE
bucket-container argument.  **It does not prove SBEE.**

## Mathematical context

The intended mathematical use is:

> A saturated bucket core has many incidences.  A small fingerprint should
> generate a bucket neighbourhood capturing a positive fraction of those
> incidences.  Combined with `BucketContainer.lean`, this produces a small
> high-multiplicity container for peeling.

## Contents

- **Part A** — Definitions of `incidenceMass`, `bucketNeighbourhood`,
  `capturedMass`, and basic monotonicity lemmas.
- **Part B** — One-step averaging lemma: there exists a vertex whose
  neighbourhood captures at least 1/|Uset| of the incidence mass.
- **Part C** — Greedy fingerprint lemma (deterministic, weak constants).
- **Part D** — Random-fingerprint existence (comments only; probabilistic
  averaging over subsets is not attempted).
-/

open Finset BigOperators

/-! ## Part A — Definitions -/

section Defs

variable {U B : Type*} [DecidableEq U] [DecidableEq B]

/-- The incidence mass of a vertex set `Uset` into a bucket set `Core`:
    `I(Uset, Core) = ∑_{b ∈ Core} |{u ∈ Uset : Inc u b}|`. -/
def incidenceMass
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) : ℕ :=
  ∑ b ∈ Core, (Uset.filter (fun u => Inc u b)).card

/-- The bucket neighbourhood of a fingerprint `F` in `Core`:
    all buckets in `Core` incident to at least one vertex in `F`. -/
def bucketNeighbourhood
    (Inc : U → B → Prop) [DecidableRel Inc]
    (F : Finset U) (Core : Finset B) : Finset B :=
  Core.filter (fun b => ∃ u ∈ F, Inc u b)

/-- The captured incidence mass: `incidenceMass Inc Uset (bucketNeighbourhood Inc F Core)`. -/
def capturedMass
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset F : Finset U) (Core : Finset B) : ℕ :=
  incidenceMass Inc Uset (bucketNeighbourhood Inc F Core)

/-- Helper: the contribution of a single vertex u to the incidence mass,
    counted from the "other side": the number of buckets in Core incident to u. -/
def vertexContribution
    (Inc : U → B → Prop) [DecidableRel Inc]
    (u : U) (Core : Finset B) : ℕ :=
  (Core.filter (fun b => Inc u b)).card

end Defs

/-! ### Monotonicity lemmas -/

section Monotonicity

variable {U B : Type*} [DecidableEq U] [DecidableEq B]

omit [DecidableEq U] [DecidableEq B] in
/-- The bucket neighbourhood of F in Core is a subset of Core. -/
theorem bucketNeighbourhood_subset_core
    (Inc : U → B → Prop) [DecidableRel Inc]
    (F : Finset U) (Core : Finset B) :
    bucketNeighbourhood Inc F Core ⊆ Core :=
  filter_subset _ _

omit [DecidableEq U] [DecidableEq B] in
/-- Captured mass is at most the total incidence mass. -/
theorem capturedMass_le_incidenceMass
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset F : Finset U) (Core : Finset B) :
    capturedMass Inc Uset F Core ≤ incidenceMass Inc Uset Core := by
  unfold capturedMass incidenceMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (bucketNeighbourhood_subset_core Inc F Core)
    (fun _ _ _ => Nat.zero_le _)

omit [DecidableEq U] [DecidableEq B] in
/-- If F₁ ⊆ F₂, then bucketNeighbourhood Inc F₁ Core ⊆ bucketNeighbourhood Inc F₂ Core. -/
theorem bucketNeighbourhood_mono
    (Inc : U → B → Prop) [DecidableRel Inc]
    (F₁ F₂ : Finset U) (Core : Finset B) (h : F₁ ⊆ F₂) :
    bucketNeighbourhood Inc F₁ Core ⊆ bucketNeighbourhood Inc F₂ Core := by
  intro b hb
  simp only [bucketNeighbourhood, mem_filter] at hb ⊢
  exact ⟨hb.1, hb.2.elim fun u hu => ⟨u, ⟨h hu.1, hu.2⟩⟩⟩

end Monotonicity

/-! ## Part B — One-step averaging lemma -/

section Averaging

variable {U B : Type*} [DecidableEq U] [DecidableEq B]

omit [DecidableEq U] [DecidableEq B] in
/-- The incidence mass equals the sum of vertex contributions (double counting). -/
theorem incidenceMass_eq_sum_contributions
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B) :
    incidenceMass Inc Uset Core =
      ∑ u ∈ Uset, vertexContribution Inc u Core := by
  unfold incidenceMass vertexContribution;
  simp +decide only [card_filter];
  exact Finset.sum_comm

/-
**One-step averaging lemma.**
If `Uset` is nonempty, there exists `u ∈ Uset` such that
`Uset.card * |{b ∈ Core : Inc u b}| ≥ incidenceMass Inc Uset Core`.
-/
omit [DecidableEq U] [DecidableEq B] in
theorem exists_vertex_above_average
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B)
    (hU : 0 < Uset.card) :
    ∃ u ∈ Uset, Uset.card * (Core.filter (fun b => Inc u b)).card
      ≥ incidenceMass Inc Uset Core := by
  obtain ⟨ u, hu ⟩ := Finset.exists_max_image Uset ( fun u ↦ ( { b ∈ Core | Inc u b } ).card ) ⟨ Classical.choose ( Finset.card_pos.mp hU ), Classical.choose_spec ( Finset.card_pos.mp hU ) ⟩;
  exact ⟨ u, hu.1, by rw [ incidenceMass_eq_sum_contributions ] ; exact le_trans ( Finset.sum_le_sum hu.2 ) ( by simp +decide ) ⟩

end Averaging

/-! ## Part C — Greedy fingerprint lemma -/

section Greedy

variable {U B : Type*} [DecidableEq U] [DecidableEq B]

/-
When `F ⊆ Uset`, the captured mass is at least the sum of vertex contributions
    of the fingerprint vertices.  This is because every bucket incident to some
    `u ∈ F` lies in `bucketNeighbourhood Inc F Core`, and its Uset-filter has
    cardinality ≥ its F-filter (since `F ⊆ Uset`).
-/
omit [DecidableEq U] [DecidableEq B] in
theorem capturedMass_ge_sum_contributions
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset F : Finset U) (Core : Finset B) (hF : F ⊆ Uset) :
    capturedMass Inc Uset F Core ≥
      ∑ u ∈ F, vertexContribution Inc u Core := by
  have h_captured_ge_sum : (∑ b ∈ bucketNeighbourhood Inc F Core, (F.filter (fun u => Inc u b)).card) ≥ (∑ u ∈ F, vertexContribution Inc u Core) := by
    simp +decide [ vertexContribution, bucketNeighbourhood ];
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_filter_of_ne ] ; aesop;
  refine' le_trans h_captured_ge_sum _;
  exact Finset.sum_le_sum fun b hb => Finset.card_mono <| Finset.filter_subset_filter _ hF

/-
Top-r averaging: from a finite set of natural numbers summing to `S`,
    one can always select at most `r` elements whose sum times `|S|`
    is at least `(total sum) * r`. This requires `r ≤ |S|`.
-/
theorem exists_subset_sum_ge
    {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (r : ℕ) (hr : r ≤ S.card) :
    ∃ T : Finset α,
      T ⊆ S ∧
      T.card ≤ r ∧
      (∑ x ∈ T, f x) * S.card ≥ (∑ x ∈ S, f x) * r := by
  induction' r with r ih generalizing S f;
  · exact ⟨ ∅, Finset.empty_subset _, by norm_num ⟩;
  · -- By the pigeonhole principle, there exists an element $x \in S$ such that $f(x) \cdot \#S \geq \sum_{y \in S} f(y)$.
    obtain ⟨x, hx⟩ : ∃ x ∈ S, f x * S.card ≥ ∑ y ∈ S, f y := by
      have := Finset.exists_max_image S f ( Finset.card_pos.mp ( pos_of_gt hr ) );
      exact ⟨ this.choose, this.choose_spec.1, by rw [mul_comm]; exact le_trans (Finset.sum_le_sum fun x hx => this.choose_spec.2 x hx) (by simp) ⟩;
    rcases ih ( S.erase x ) ( fun y => f y ) ( by rw [ Finset.card_erase_of_mem hx.1 ] ; omega ) with ⟨ T, hT₁, hT₂, hT₃ ⟩ ; use Insert.insert x T ; simp_all +decide [ Finset.subset_iff ];
    rw [ Finset.sum_insert ];
    · rw [ Finset.card_insert_of_notMem ( fun h => hT₁ h |>.1 rfl ) ];
      rcases n : #S with ( _ | _ | n ) <;> simp_all +decide [];
      rw [ ← Finset.sum_erase_add _ _ hx.1 ] at * ; nlinarith;
    · exact fun h => hT₁ h |>.1 rfl

/-
**Greedy fingerprint lemma.**
For any `r ≤ Uset.card`, there exists `F ⊆ Uset` with `F.card ≤ r` such that
`capturedMass Inc Uset F Core * Uset.card ≥ incidenceMass Inc Uset Core * r`.

Informally: a fingerprint of size `r` captures at least an `r / |Uset|` fraction
of the total incidence mass.

Note: the hypothesis `r ≤ Uset.card` is necessary; the conclusion is false
when `r > Uset.card` and `incidenceMass > 0`.
-/
omit [DecidableEq B] in
theorem greedy_fingerprint
    (Inc : U → B → Prop) [DecidableRel Inc]
    (Uset : Finset U) (Core : Finset B)
    (r : ℕ) (hr : r ≤ Uset.card) :
    ∃ F : Finset U,
      F ⊆ Uset ∧
      F.card ≤ r ∧
      capturedMass Inc Uset F Core * Uset.card ≥
        incidenceMass Inc Uset Core * r := by
  have := exists_subset_sum_ge Uset ( fun u => vertexContribution Inc u Core ) r hr;
  exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, by simpa only [ incidenceMass_eq_sum_contributions ] using this.choose_spec.2.2.trans ( Nat.mul_le_mul_right _ ( capturedMass_ge_sum_contributions Inc Uset this.choose Core this.choose_spec.1 ) ) ⟩

end Greedy

/-! ## Part D — Random-fingerprint existence (not formalized)

A probabilistic version of Part C would assert: if every bucket in `Core`
has at least `k` neighbours in `Uset`, then there exists `F ⊆ Uset` with
`F.card ≤ 2 * Uset.card / k` such that
`capturedMass Inc Uset F Core ≥ incidenceMass Inc Uset Core / C`
for some absolute constant `C`.

The standard proof uses the probabilistic method: sample each vertex
independently with probability `p = 1/k`, then the expected number of
covered buckets is `|Core| * (1 - (1-p)^k) ≥ |Core| * (1 - 1/e)`,
and a first-moment argument gives the existence claim.

Formalizing this in Lean/Mathlib would require:
- A model of independent Bernoulli sampling on finite sets.
- Linearity of expectation over indicator random variables.
- The bound `(1 - 1/k)^k ≤ 1/e` (or a weaker rational bound).
- A first-moment / Markov argument to extract an existential witness.

None of this infrastructure is readily available in Mathlib at present,
so we do not attempt this formalization.  The deterministic greedy lemma
from Part C provides a weaker but fully verified alternative.
-/