import Mathlib

/-!
# BucketCore: Finite bucket-incidence lemmas for SBEE

This file does **not** prove SBEE.  It formalizes finite bucket-incidence
lemmas intended for the SBEE bucket-container proof.  The lemmas correspond
to the scratch proof sections:

- bucket occupancy and collision bounds (Part A);
- non-saturated deficit counting (Part B);
- marked dual large-sieve double counting (Part C).

Part D (fingerprint lemma) is not attempted here because a nontrivial
deterministic fingerprint bound requires a separate greedy-cover / averaging
formalization that goes beyond simple finite counting.
-/

open Finset BigOperators

/-! ## Part A – Basic bucket definitions -/

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-- The number of vertices in Γ incident to bucket b. -/
def bucketOccupancy (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (b : B) : ℕ :=
  (Γ.filter (fun v => Inc v b)).card

/-- Upper bound on bucket collisions: ∑_b C(ω(b), 2). -/
def bucketCollisionUpper (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B) : ℕ :=
  ∑ b ∈ Buckets, Nat.choose (bucketOccupancy Inc Γ b) 2

/-- Total incidence mass: ∑_b ω(b). -/
def bucketIncidenceMass (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B) : ℕ :=
  ∑ b ∈ Buckets, bucketOccupancy Inc Γ b

/-! ### Lemma A1: Nat.choose k 2 ≤ k * D when k ≤ D -/

lemma choose_two_le_mul_of_le {k D : ℕ} (hk : k ≤ D) :
    Nat.choose k 2 ≤ k * D := by
  rw [Nat.choose_two_right]
  exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left k (by omega))

/-! ### Lemma A1': collision ≤ D * mass -/

omit [DecidableEq V] [DecidableEq B] in
lemma bucketCollisionUpper_le_mul_mass (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B) (D : ℕ)
    (hD : ∀ b ∈ Buckets, bucketOccupancy Inc Γ b ≤ D) :
    bucketCollisionUpper Inc Γ Buckets ≤ D * bucketIncidenceMass Inc Γ Buckets := by
  unfold bucketCollisionUpper bucketIncidenceMass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b hb => by
    calc Nat.choose (bucketOccupancy Inc Γ b) 2
        ≤ bucketOccupancy Inc Γ b * D := choose_two_le_mul_of_le (hD b hb)
      _ = D * bucketOccupancy Inc Γ b := mul_comm _ _

/-! ### Lemma A2: mass ≤ |Γ| * M  (double counting) -/

omit [DecidableEq V] [DecidableEq B] in
/-- Double-counting identity: ∑_b ω(Γ,b) = ∑_{v∈Γ} deg(v). -/
lemma bucketIncidenceMass_eq_sum_degrees (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B) :
    bucketIncidenceMass Inc Γ Buckets =
      ∑ v ∈ Γ, (Buckets.filter (fun b => Inc v b)).card := by
  unfold bucketIncidenceMass bucketOccupancy
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

omit [DecidableEq V] [DecidableEq B] in
lemma bucketIncidenceMass_le_card_mul (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B) (M : ℕ)
    (hM : ∀ v ∈ Γ, (Buckets.filter (fun b => Inc v b)).card ≤ M) :
    bucketIncidenceMass Inc Γ Buckets ≤ Γ.card * M := by
  rw [bucketIncidenceMass_eq_sum_degrees]
  calc ∑ v ∈ Γ, (Buckets.filter (fun b => Inc v b)).card
      ≤ ∑ v ∈ Γ, M := Finset.sum_le_sum hM
    _ = Γ.card * M := by rw [Finset.sum_const, smul_eq_mul]

/-! ### Lemma A3: collision ≤ D * |Γ| * M -/

omit [DecidableEq V] [DecidableEq B] in
lemma bucketCollisionUpper_le (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B) (D M : ℕ)
    (hD : ∀ b ∈ Buckets, bucketOccupancy Inc Γ b ≤ D)
    (hM : ∀ v ∈ Γ, (Buckets.filter (fun b => Inc v b)).card ≤ M) :
    bucketCollisionUpper Inc Γ Buckets ≤ D * Γ.card * M := by
  calc bucketCollisionUpper Inc Γ Buckets
      ≤ D * bucketIncidenceMass Inc Γ Buckets :=
        bucketCollisionUpper_le_mul_mass Inc Γ Buckets D hD
    _ ≤ D * (Γ.card * M) :=
        Nat.mul_le_mul_left D (bucketIncidenceMass_le_card_mul Inc Γ Buckets M hM)
    _ = D * Γ.card * M := by ring

/-! ## Part B – Non-saturated cheap-pair deficit -/

variable {α : Type*} [DecidableEq α]

/-- Count of ordered cross-label pairs in Γ. -/
def crossPairCount (Γ : Finset V) (label : V → α) : ℕ :=
  ((Γ ×ˢ Γ).filter (fun vw => vw.1 ≠ vw.2 ∧ label vw.1 ≠ label vw.2)).card

/-- Count of ordered cheap cross-label pairs in Γ. -/
def cheapCrossPairCount (Γ : Finset V) (label : V → α)
    (Cheap : V → V → Prop) [DecidableRel Cheap] : ℕ :=
  ((Γ ×ˢ Γ).filter
    (fun vw => vw.1 ≠ vw.2 ∧ label vw.1 ≠ label vw.2 ∧ Cheap vw.1 vw.2)).card

/-- Count of ordered non-cheap cross-label pairs in Γ. -/
def expensiveCrossPairCount (Γ : Finset V) (label : V → α)
    (Cheap : V → V → Prop) [DecidableRel Cheap] : ℕ :=
  ((Γ ×ˢ Γ).filter
    (fun vw => vw.1 ≠ vw.2 ∧ label vw.1 ≠ label vw.2 ∧ ¬Cheap vw.1 vw.2)).card

/-
Cheap + expensive = total cross pairs.
-/
lemma cheap_plus_expensive_eq_cross (Γ : Finset V) (label : V → α)
    (Cheap : V → V → Prop) [DecidableRel Cheap] :
    cheapCrossPairCount Γ label Cheap + expensiveCrossPairCount Γ label Cheap =
      crossPairCount Γ label := by
  unfold cheapCrossPairCount expensiveCrossPairCount crossPairCount;
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with x ; by_cases h : Cheap x.1 x.2 <;> aesop;
  · exact Finset.disjoint_filter.mpr ( by aesop )

/-- Deficit: if crossPairCount ≥ P and cheapCrossPairCount ≤ C,
    then expensiveCrossPairCount ≥ P - C. -/
lemma deficit_cross_pairs (Γ : Finset V) (label : V → α)
    (Cheap : V → V → Prop) [DecidableRel Cheap]
    (P C : ℕ) (hP : crossPairCount Γ label ≥ P)
    (hC : cheapCrossPairCount Γ label Cheap ≤ C) :
    expensiveCrossPairCount Γ label Cheap ≥ P - C := by
  have := cheap_plus_expensive_eq_cross Γ label Cheap
  omega

/-
Cheap cross-label pairs are bounded by the sum of off-diagonal incidence
    counts over all buckets.  Under the bucket representation condition,
    this gives cheapCrossPairCount ≤ 2 * bucketCollisionUpper.
-/
omit [DecidableEq B] in
lemma cheapCross_le_two_mul_collision
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Buckets : Finset B)
    (label : V → α)
    (Cheap : V → V → Prop) [DecidableRel Cheap]
    (hcheap : ∀ v ∈ Γ, ∀ w ∈ Γ, v ≠ w → label v ≠ label w →
      Cheap v w → ∃ b ∈ Buckets, Inc v b ∧ Inc w b) :
    cheapCrossPairCount Γ label Cheap ≤
      2 * bucketCollisionUpper Inc Γ Buckets := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.biUnion Buckets fun b => Finset.offDiag ( Finset.filter ( fun v => Inc v b ) Γ );
  · grind +revert;
  · refine' le_trans ( Finset.card_biUnion_le ) _;
    simp +decide [ bucketCollisionUpper, Finset.offDiag_card ];
    rw [ Finset.mul_sum _ _ _ ] ; gcongr ; simp +decide [ bucketOccupancy ] ; ring_nf;
    induction' ( # ( { v ∈ Γ | Inc v ‹_› } ) ) with n ih <;> simp +decide [ Nat.choose ] at * ; nlinarith

/-! ## Part C – Marked dual large-sieve double counting -/

section PartC

variable {P T B' : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq B']

/-- Bucket multiplicity: #{n ∈ 𝓑 : MarkedCongruence p t n}. -/
def bucketMultiplicity
    (MC : P → T → B' → Prop) [∀ p t, DecidablePred (MC p t)]
    (𝓑 : Finset B') (p : P) (t : T) : ℕ :=
  (𝓑.filter (fun n => MC p t n)).card

/-- Auxiliary: 2 * choose k 2 = k * (k - 1). -/
lemma two_mul_choose_two (k : ℕ) : 2 * Nat.choose k 2 = k * (k - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)

/-
**Marked dual large sieve.**

Under diagonal uniqueness (for each n ∈ 𝓑 and p ∈ Ps, at most one
t ∈ Ts satisfies MC p t n) and off-diagonal uniqueness (for distinct
n, n' ∈ 𝓑, at most one (p,t) ∈ Ps × Ts satisfies MC p t n ∧ MC p t n'),
we have  ∑_{p ∈ Ps} ∑_{t ∈ Ts} C(d(p,t), 2) ≤ C(|𝓑|, 2).

Proof idea: The LHS counts unordered pairs {n₁, n₂} ⊆ 𝓑 ∩ MC(p,t).
Off-diagonal uniqueness makes these pair sets disjoint across distinct
(p,t), so the total ≤ C(|𝓑|, 2).
-/
omit [DecidableEq P] [DecidableEq T] in
lemma marked_dual_large_sieve
    (MC : P → T → B' → Prop)
    [∀ p t, DecidablePred (MC p t)]
    (Ps : Finset P) (Ts : Finset T) (𝓑 : Finset B')
    (_hdiag : ∀ n ∈ 𝓑, ∀ p ∈ Ps, ∀ t₁ ∈ Ts, ∀ t₂ ∈ Ts,
      MC p t₁ n → MC p t₂ n → t₁ = t₂)
    (hoffdiag : ∀ n₁ ∈ 𝓑, ∀ n₂ ∈ 𝓑, n₁ ≠ n₂ →
      ∀ p₁ ∈ Ps, ∀ t₁ ∈ Ts, ∀ p₂ ∈ Ps, ∀ t₂ ∈ Ts,
      MC p₁ t₁ n₁ → MC p₁ t₁ n₂ →
      MC p₂ t₂ n₁ → MC p₂ t₂ n₂ →
      (p₁, t₁) = (p₂, t₂)) :
    ∑ p ∈ Ps, ∑ t ∈ Ts, Nat.choose (bucketMultiplicity MC 𝓑 p t) 2
      ≤ Nat.choose 𝓑.card 2 := by
  -- By Lemma 2, we know that $\sum_{p \in Ps} \sum_{t \in Ts} d(p, t) (d(p, t) - 1) \leq |𝓑| (|𝓑| - 1)$.
  have h_sum : ∑ p ∈ Ps, ∑ t ∈ Ts, (bucketMultiplicity MC 𝓑 p t) * ((bucketMultiplicity MC 𝓑 p t) - 1) ≤ (𝓑.card) * (𝓑.card - 1) := by
    -- The left-hand side counts the number of ordered pairs $(n_1, n_2)$ where $n_1 \neq n_2$ and both $n_1$ and $n_2$ satisfy $MC p t$ for some $p \in Ps$ and $t \in Ts$.
    have h_lhs : ∑ p ∈ Ps, ∑ t ∈ Ts, (bucketMultiplicity MC 𝓑 p t) * ((bucketMultiplicity MC 𝓑 p t) - 1) = Finset.card (Finset.biUnion (Ps ×ˢ Ts) (fun (p, t) => (𝓑.filter (MC p t ·)).offDiag)) := by
      rw [ Finset.card_biUnion ];
      · rw [ Finset.sum_product ];
        simp +decide [ bucketMultiplicity, Finset.offDiag_card ];
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ Nat.mul_sub_left_distrib, Nat.mul_one ] ;
      · intros x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
        grind +ring;
    rw [ h_lhs ];
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.offDiag 𝓑;
    · simp +contextual [ Finset.subset_iff ];
    · simp +decide [ mul_tsub, Finset.offDiag_card ];
  convert Nat.div_le_div_right h_sum using 1;
  any_goals exact Nat.choose_two_right ( #𝓑 );
  rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; rw [ Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun t ht => Nat.choose_two_right _ ] ; ring;
  rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun j hj => by rw [ Nat.div_mul_cancel ] ; exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ;

end PartC

/-! ## Part D – Fingerprint lemma

A nontrivial deterministic fingerprint bound (e.g., a greedy set-cover
statement guaranteeing a small hitting set F ⊆ Uset with every bucket
in Core incident to some vertex in F) requires a formalization of the
iterated-greedy / probabilistic-method covering argument.  This is not
attempted in this file.

A useful target would be: for a bipartite incidence with every bucket
having at least k neighbours, there exists F ⊆ Uset with
|F| ≤ ⌈|Uset| * ln(|Core|) / k⌉ covering all of Core.  Proving this
requires logarithms, probabilistic estimates, or a careful greedy
induction, all beyond simple finite counting.
-/