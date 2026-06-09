import Mathlib
import RequestProject.BucketCore
import RequestProject.BucketContainer
import RequestProject.BipartiteCycles

/-!
# TwoCoreBookkeeping: Finite incidence bookkeeping for the ambient-sensitive FIE route

This file formalizes three finite incidence-counting results that support the
paper-side statement:

> Persistent second saturation ⟹ dense two-core bucket-pair graph
> and many seed common-neighbours.

## Contents

* **Goal 1** (`newBucket_capacity_mul_le`): One-core new-bucket capacity bound.
  If each pair of a new bucket `n` and a core bucket `c` is incident to at most one
  vertex, then the number of high-degree vertices incident to `n` times the threshold
  `h` is at most `|Core|`.

* **Goal 2** (`twoCore_edges_lower_mul`): Two-core edge lower bound.
  Under pairwise uniqueness across two cores, the product graph has at least
  `|Γ| · h₀ · h₁` edges.

* **Goal 3** (`highDeg_generatedCore_le_seedNeighbours`): Generated core gives
  many seed neighbours. If `v` has degree ≥ `h` into the generated core and
  each seed shares at most one bucket with `v`, then `v` has ≥ `h` seed neighbours.

No SBEE, Fourier positivity, or analytic number theory is used.
-/

open Finset BigOperators

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-! ## Goal 1: One-core new-bucket capacity -/

/-- High-degree container: vertices in `U` with at least `h` incidences into `Core`. -/
def highDegInto
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (h : ℕ) : Finset V :=
  U.filter (fun v => h ≤ (Core.filter (fun c => Inc v c)).card)

/-
**Goal 1.** For a new bucket `n ∉ Core`, if each core bucket `c` is
incident to at most one vertex in `U` that is also incident to `n`, then
the number of high-degree vertices incident to `n` times `h` is at most `|Core|`.

Proof sketch: Let `S = (highDegInto …).filter (Inc · n)`. Each `v ∈ S` contributes
≥ `h` incidences into `Core`, so `|S| · h ≤ ∑_{v ∈ S} |Core ∩ Inc(v)|`.
Swapping the sum, each `c ∈ Core` contributes at most 1 (by uniqueness), so the
total is ≤ `|Core|`.

Note: the hypothesis `n ∉ Core` turns out to be unnecessary for this proof;
the uniqueness hypothesis alone suffices.
-/
theorem newBucket_capacity_mul_le
    {V B : Type*} [DecidableEq V] [DecidableEq B]
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (n : B) (h : ℕ)
    (_hn : n ∉ Core)
    (huniq : ∀ c ∈ Core, ∀ v₁ ∈ U, ∀ v₂ ∈ U,
      Inc v₁ n → Inc v₁ c → Inc v₂ n → Inc v₂ c → v₁ = v₂) :
    ((highDegInto Inc U Core h).filter (fun v => Inc v n)).card * h ≤ Core.card := by
  have h_sum : ∑ v ∈ {v ∈ highDegInto Inc U Core h | Inc v n}, (Core.filter (fun c => Inc v c)).card ≤ ∑ c ∈ Core, ∑ v ∈ {v ∈ highDegInto Inc U Core h | Inc v n}, if Inc v c then 1 else 0 := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  have h_sum_le_core : ∑ v ∈ {v ∈ highDegInto Inc U Core h | Inc v n}, (Core.filter (fun c => Inc v c)).card ≥ (highDegInto Inc U Core h |>.filter (fun v => Inc v n)).card * h := by
    exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 );
  refine' le_trans h_sum_le_core ( h_sum.trans _ );
  refine' le_trans ( Finset.sum_le_sum fun c hc => show ∑ v ∈ Finset.filter ( fun v => Inc v n ) ( highDegInto Inc U Core h ), ( if Inc v c then 1 else 0 ) ≤ 1 from _ ) _ <;> simp +decide [ Finset.sum_ite ];
  exact Finset.card_le_one.mpr fun x hx y hy => huniq c hc x ( Finset.mem_filter.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) |>.1 ) y ( Finset.mem_filter.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hy |>.1 ) |>.1 ) |>.1 ) ( Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp ( Finset.mem_filter.mp hy |>.1 ) |>.2 ) ( Finset.mem_filter.mp hy |>.2 )

/-! ## Goal 2: Two-core edge lower bound -/

/-- The set of bucket pairs `(c₀, c₁) ∈ Core₀ × Core₁` realized by some vertex in `Γ`. -/
def twoCoreEdges
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Core₀ Core₁ : Finset B) : Finset (B × B) :=
  (Core₀.product Core₁).filter
    (fun bc => ∃ v ∈ Γ, Inc v bc.1 ∧ Inc v bc.2)

/-
**Goal 2.** Under pairwise uniqueness across two cores, the product graph
has at least `|Γ| · h₀ · h₁` edges.

Proof sketch: Each `v ∈ Γ` contributes ≥ `h₀ · h₁` pairs. By the uniqueness
hypothesis, distinct vertices contribute disjoint pair sets, so the union has
cardinality ≥ `|Γ| · h₀ · h₁`.
-/
theorem twoCore_edges_lower_mul
    {V B : Type*} [DecidableEq V] [DecidableEq B]
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Core₀ Core₁ : Finset B) (h₀ h₁ : ℕ)
    (hdeg₀ : ∀ v ∈ Γ, h₀ ≤ (Core₀.filter (fun c => Inc v c)).card)
    (hdeg₁ : ∀ v ∈ Γ, h₁ ≤ (Core₁.filter (fun c => Inc v c)).card)
    (huniq : ∀ c₀ ∈ Core₀, ∀ c₁ ∈ Core₁, ∀ v₁ ∈ Γ, ∀ v₂ ∈ Γ,
      Inc v₁ c₀ → Inc v₁ c₁ → Inc v₂ c₀ → Inc v₂ c₁ → v₁ = v₂) :
    Γ.card * h₀ * h₁ ≤ (twoCoreEdges Inc Γ Core₀ Core₁).card := by
  refine' le_trans _ ( Finset.card_le_card _ );
  convert Finset.card_biUnion_le.trans' _;
  rw [ Finset.card_biUnion ];
  any_goals exact Γ;
  rotate_left;
  infer_instance;
  use fun v => (Core₀.filter (fun c => Inc v c)).product (Core₁.filter (fun c => Inc v c));
  · rw [ Finset.card_biUnion ];
    · simp +decide [ mul_assoc, Finset.card_product ];
      exact le_trans ( by simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ) ( Finset.sum_le_sum fun x hx => Nat.mul_le_mul ( hdeg₀ x hx ) ( hdeg₁ x hx ) );
    · intro v hv w hw hvw; simp_all +decide [ Finset.disjoint_left ] ;
      exact fun a b ha ha' hb hb' ha'' hb'' => hvw <| huniq a ha b hb v hv w hw ha' hb' ha'' hb'';
  · simp +contextual [ Finset.subset_iff, twoCoreEdges ];
    exact fun a b x hx ha ha' hb hb' => ⟨ x, hx, ha', hb' ⟩;
  · intro v hv w hw hvw; simp_all +decide [ Finset.disjoint_left ] ;
    exact fun a b ha ha' hb hb' ha'' hb'' => hvw <| huniq a ha b hb v hv w hw ha' hb' ha'' hb''

/-! ## Goal 3: Generated core gives many seed neighbours -/

/-- The seed-neighbour set: vertices in `F` sharing a bucket with `v`. -/
def seedNeighbours
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Buckets : Finset B) (F : Finset V) (v : V) : Finset V :=
  F.filter (fun f => ∃ b ∈ Buckets, Inc v b ∧ Inc f b)

/-
**Goal 3.** If `v` has degree ≥ `h` into the generated core and each seed
shares at most one bucket with `v`, then `v` has ≥ `h` seed neighbours.

Proof sketch: Each generated-core bucket incident to `v` has a witness seed.
The uniqueness hypothesis ensures distinct buckets map to distinct seeds,
so the number of seed neighbours is ≥ the number of incident generated-core
buckets, which is ≥ `h`.
-/
theorem highDeg_generatedCore_le_seedNeighbours
    {V B : Type*} [DecidableEq V] [DecidableEq B]
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Buckets : Finset B) (F : Finset V) (v : V) (h : ℕ)
    (hdeg : h ≤ ((generatedBuckets Inc F Buckets).filter (fun b => Inc v b)).card)
    (huniq : ∀ f ∈ F, ∀ b₁ ∈ Buckets, ∀ b₂ ∈ Buckets,
      Inc v b₁ → Inc f b₁ → Inc v b₂ → Inc f b₂ → b₁ = b₂) :
    h ≤ (seedNeighbours Inc Buckets F v).card := by
  refine' le_trans hdeg ( Finset.card_le_card _ |> le_trans <| _ );
  exact Finset.biUnion ( seedNeighbours Inc Buckets F v ) fun f => Finset.filter ( fun b => Inc v b ∧ Inc f b ) Buckets;
  · intro b hb; simp_all +decide [ generatedBuckets, seedNeighbours ] ;
    exact ⟨ _, ⟨ hb.1.2.choose_spec.1, b, hb.1.1, hb.2, hb.1.2.choose_spec.2 ⟩, hb.1.2.choose_spec.2 ⟩;
  · refine' le_trans ( Finset.card_biUnion_le ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show #_ ≤ 1 from _ ) _ <;> simp +decide [ Finset.card_le_one ];
    exact fun a ha ha' ha'' b hb hb' hb'' => huniq x ( Finset.mem_filter.mp hx |>.1 ) a ha b hb ha' ha'' hb' hb''