import Mathlib
import RequestProject.BucketCore

/-!
# BucketContainer: Deterministic container-size bounds from a generated bucket core

This file does **not** prove SBEE.  It formalizes the deterministic
container-size consequence of a generated bucket core.

## Mathematical context

The key mathematical use is: if a fingerprint `F` has size about `W/D`
and each fingerprint vertex has about `M = W/D` buckets, then its generated
bucket core has size about `M²`.  The marked dual large-sieve bound
(`marked_dual_large_sieve` from `BucketCore`) then implies that vertices
incident to at least `h ≈ M / polylog` generated buckets lie in a container
of size about `M² polylog`.

## Contents

- **Part A**: Generated bucket core and union bound on its size.
- **Part B**: High-multiplicity container and abstract counting lemma.
- **Part C**: Specialization discussion for `marked_dual_large_sieve`.
- **Part D**: Numeric corollary bounding container size by `K²`.
-/

open Finset BigOperators

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-! ## Part A – Generated bucket core -/

/-- The generated bucket core: all buckets in `Buckets` incident to some vertex in `F`. -/
def generatedBuckets
    (Inc : V → B → Prop) [DecidableRel Inc]
    (F : Finset V) (Buckets : Finset B) : Finset B :=
  Buckets.filter (fun b => ∃ v ∈ F, Inc v b)

/-- Vertex bucket degree into a given bucket set. -/
def vertexBucketDegree
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Buckets : Finset B) (v : V) : ℕ :=
  (Buckets.filter (fun b => Inc v b)).card

/-
Union bound: the generated bucket core has at most `|F| * M` buckets,
when every vertex in `F` has bucket degree at most `M`.
-/
omit [DecidableEq V] in
theorem generatedBuckets_card_le
    (Inc : V → B → Prop) [DecidableRel Inc]
    (F : Finset V) (Buckets : Finset B) (M : ℕ)
    (hM : ∀ v ∈ F, vertexBucketDegree Inc Buckets v ≤ M) :
    (generatedBuckets Inc F Buckets).card ≤ F.card * M := by
  refine' le_trans _ ( Finset.sum_le_card_nsmul _ _ _ fun x hx => hM x hx );
  convert Finset.card_biUnion_le;
  ext b; simp [generatedBuckets];
  · grind +splitImp;
  · infer_instance

/-! ## Part B – High-multiplicity container -/

/-- The high-multiplicity container: all vertices in `U` with bucket degree
at least `h` into `Core`. -/
def highMultiplicityContainerIn
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (h : ℕ) : Finset V :=
  U.filter (fun v => h ≤ vertexBucketDegree Inc Core v)

/-
Monotonicity of `Nat.choose · 2`: if every vertex in `U` has bucket degree
at least `h`, then `|U| * C(h,2) ≤ ∑_{v ∈ U} C(deg(v), 2)`.
-/
omit [DecidableEq V] [DecidableEq B] in
theorem highMultiplicity_card_mul_choose_le
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (h : ℕ)
    (hU : ∀ v ∈ U, h ≤ vertexBucketDegree Inc Core v) :
    U.card * Nat.choose h 2 ≤
      ∑ v ∈ U, Nat.choose (vertexBucketDegree Inc Core v) 2 := by
  exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun v hv => Nat.choose_le_choose _ ( hU v hv ) )

/-
Abstract high-multiplicity container bound: if the sum of `C(deg(v), 2)`
is bounded by `C(|Core|, 2)`, then `|container| * C(h,2) ≤ C(|Core|,2)`.
-/
omit [DecidableEq V] [DecidableEq B] in
theorem highMultiplicityContainer_card_bound_from_sum
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (h : ℕ)
    (hsum : ∑ v ∈ U, Nat.choose (vertexBucketDegree Inc Core v) 2
              ≤ Nat.choose Core.card 2) :
    (highMultiplicityContainerIn Inc U Core h).card * Nat.choose h 2
      ≤ Nat.choose Core.card 2 := by
  refine' le_trans _ ( hsum.trans _ );
  · have hsum_le : ∑ v ∈ highMultiplicityContainerIn Inc U Core h, (vertexBucketDegree Inc Core v).choose 2 ≥ (highMultiplicityContainerIn Inc U Core h).card * (Nat.choose h 2) := by
      exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => Nat.choose_le_choose _ <| Finset.mem_filter.mp hx |>.2 );
    exact hsum_le.trans ( Finset.sum_le_sum_of_subset ( Finset.filter_subset _ _ ) );
  · rfl

/-! ## Part C – Specialization to `marked_dual_large_sieve`

The theorem `marked_dual_large_sieve` from `BucketCore` gives, under
off-diagonal uniqueness:

  `∑ p ∈ Ps, ∑ t ∈ Ts, Nat.choose (bucketMultiplicity MC 𝓑 p t) 2 ≤ Nat.choose 𝓑.card 2`

To connect this with Part B, one identifies:
- `V := P × T`  (the vertex type)
- `B := B'`     (the bucket type)
- `Inc := fun (v : P × T) (b : B') => MC v.1 v.2 b`
- `Core := 𝓑`
- `U := Ps.product Ts`

Under this identification, `vertexBucketDegree Inc 𝓑 (p, t) = bucketMultiplicity MC 𝓑 p t`,
and the sum `∑ v ∈ U, C(deg(v), 2)` equals `∑ p ∈ Ps, ∑ t ∈ Ts, C(d(p,t), 2)`.

Therefore, `highMultiplicityContainer_card_bound_from_sum` applied with
the `marked_dual_large_sieve` bound as input yields:

  `|{(p,t) ∈ Ps × Ts : h ≤ d_Core(p,t)}| * C(h,2) ≤ C(|𝓑|, 2)`

We formalize this specialization below.
-/

section Specialization

variable {P T B' : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq B']

/-
Key identity: `vertexBucketDegree` for product vertices equals `bucketMultiplicity`.
-/
omit [DecidableEq P] [DecidableEq T] [DecidableEq B'] in
lemma vertexBucketDegree_eq_bucketMultiplicity
    (MC : P → T → B' → Prop) [∀ p t, DecidablePred (MC p t)]
    (𝓑 : Finset B') (p : P) (t : T) :
    vertexBucketDegree (fun (v : P × T) (b : B') => MC v.1 v.2 b) 𝓑 (p, t) =
      bucketMultiplicity MC 𝓑 p t := by
  rfl

/-
The specialized container bound from `marked_dual_large_sieve`.
-/
omit [DecidableEq P] [DecidableEq T] in
theorem container_bound_from_marked_dual_large_sieve
    (MC : P → T → B' → Prop)
    [∀ p t, DecidablePred (MC p t)]
    (Ps : Finset P) (Ts : Finset T) (𝓑 : Finset B') (h : ℕ)
    (_hdiag : ∀ n ∈ 𝓑, ∀ p ∈ Ps, ∀ t₁ ∈ Ts, ∀ t₂ ∈ Ts,
      MC p t₁ n → MC p t₂ n → t₁ = t₂)
    (hoffdiag : ∀ n₁ ∈ 𝓑, ∀ n₂ ∈ 𝓑, n₁ ≠ n₂ →
      ∀ p₁ ∈ Ps, ∀ t₁ ∈ Ts, ∀ p₂ ∈ Ps, ∀ t₂ ∈ Ts,
      MC p₁ t₁ n₁ → MC p₁ t₁ n₂ →
      MC p₂ t₂ n₁ → MC p₂ t₂ n₂ →
      (p₁, t₁) = (p₂, t₂)) :
    (highMultiplicityContainerIn
      (fun (v : P × T) (b : B') => MC v.1 v.2 b)
      (Ps.product Ts) 𝓑 h).card * Nat.choose h 2
      ≤ Nat.choose 𝓑.card 2 := by
  apply highMultiplicityContainer_card_bound_from_sum;
  convert marked_dual_large_sieve MC Ps Ts 𝓑 _hdiag hoffdiag using 1;
  erw [ Finset.sum_product ] ; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ vertexBucketDegree_eq_bucketMultiplicity ] ;

end Specialization

/-! ## Part D – Numeric corollary -/

/-
If `C(n,2) ≤ C(K,2)` then `n*(n-1) ≤ K*(K-1)` (and hence `n*(n-1) ≤ K*K`).
-/
lemma choose_two_le_implies_mul_le {n K : ℕ}
    (h : Nat.choose n 2 ≤ Nat.choose K 2) :
    n * (n - 1) ≤ K * (K - 1) := by
  grind +suggestions

/-
Container size numeric bound: if `container.card * C(h,2) ≤ C(K,2)` and `2 ≤ h`,
then `container.card * (h * (h-1)) ≤ K * K`.
-/
theorem container_card_numeric_bound
    (container_card h K : ℕ) (hh : 2 ≤ h)
    (hbound : container_card * Nat.choose h 2 ≤ Nat.choose K 2) :
    container_card * (h * (h - 1)) ≤ K * K := by
  rcases h with ( _ | _ | h ) <;> rcases K with ( _ | _ | K ) <;> simp_all +decide [ Nat.choose_two_right ];
  · grind;
  · cases hbound <;> nlinarith [ Nat.mul_le_mul_left h ( Nat.succ_le_succ ( Nat.succ_pos h ) ) ];
  · nlinarith [ Nat.div_mul_cancel ( show 2 ∣ ( h + 1 + 1 ) * ( h + 1 ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ), Nat.div_mul_le_self ( ( K + 1 + 1 ) * ( K + 1 ) ) 2 ]