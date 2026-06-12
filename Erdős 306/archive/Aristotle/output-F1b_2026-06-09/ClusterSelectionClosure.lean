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

/-! ## F1b: Discharge cluster-size and regime hypotheses -/

/-! ### Part A: Cluster-size bound -/

/-
In an interval [X, 2X] with 0 < p and X ≤ p, at most 2 integers in any Finset
    that are pairwise congruent modulo p can fit.
-/
theorem interval_mod_card_le_two
    (S : Finset ℤ) (X p : ℤ) (hp : 0 < p) (hXp : X ≤ p)
    (hS : ∀ a ∈ S, X ≤ a ∧ a ≤ 2 * X)
    (hcong : ∀ a ∈ S, ∀ b ∈ S, p ∣ (a - b)) :
    S.card ≤ 2 := by
      -- Assume S.card ≥ 3. Take 3 distinct elements a, b, c ∈ S with a < b < c.
      by_contra h_contra
      obtain ⟨a, b, c, haS, hbS, hcS, habc⟩ : ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a < b ∧ b < c := by
        obtain ⟨s, hs⟩ : ∃ s : Fin 3 → ℤ, (∀ i, s i ∈ S) ∧ StrictMono s := by
          exact ⟨ fun i => S.orderEmbOfFin rfl ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => by simp +decide, by simp +decide [ StrictMono ] ⟩;
        exact ⟨ s 0, s 1, s 2, hs.1 0, hs.1 1, hs.1 2, hs.2 ( by decide ), hs.2 ( by decide ) ⟩;
      exact absurd ( hcong b hbS a haS ) ( by rintro ⟨ k, hk ⟩ ; nlinarith [ show k = 0 by nlinarith [ hS a haS, hS b hbS, hS c hcS ] ] )

/-
Cancellation: if p divides both q₁*x - c and q₂*x - c, and IsCoprime x p,
    then p divides q₁ - q₂.
-/
theorem dvd_sub_of_dvd_mul_sub
    (q₁ q₂ x c p : ℤ)
    (h1 : p ∣ (q₁ * x - c)) (h2 : p ∣ (q₂ * x - c))
    (hcop : IsCoprime x p) :
    p ∣ (q₁ - q₂) := by
      convert hcop.symm.dvd_of_dvd_mul_left _ using 1 ; ring;
      convert dvd_sub h1 h2 using 1 ; ring

/-
If 0 < |x| < p (with p prime), q ∈ F lies in [X, 2X], and X ≤ p, then
    at most 2 elements of F satisfy p ∣ (q*x - c).
-/
theorem congruence_fiber_card_le_two
    (F : Finset ℤ) (x c p X : ℤ)
    (hp : Prime p) (hpp : 0 < p) (hxp : (|x| : ℤ) < p) (hx_ne : x ≠ 0)
    (hF : ∀ q ∈ F, X ≤ q ∧ q ≤ 2 * X) (hXp : X ≤ p) :
    (F.filter (fun q => (p : ℤ) ∣ (q * x - c))).card ≤ 2 := by
      -- Since $p$ is prime and $|x| < p$, $x$ is coprime to $p$.
      have hx_coprime_p : IsCoprime x p := by
        refine' IsCoprime.symm _;
        exact hp.coprime_iff_not_dvd.mpr fun h => by have := Int.le_of_dvd ( abs_pos.mpr hx_ne ) ( by simpa using h ) ; linarith [ abs_nonneg x ] ;
      have h_pairwise_cong : ∀ q₁ ∈ F.filter (fun q => p ∣ q * x - c), ∀ q₂ ∈ F.filter (fun q => p ∣ q * x - c), p ∣ (q₁ - q₂) := by
        exact fun q₁ hq₁ q₂ hq₂ => dvd_sub_of_dvd_mul_sub q₁ q₂ x c p ( by aesop ) ( by aesop ) hx_coprime_p;
      apply interval_mod_card_le_two (F.filter (fun q => p ∣ q * x - c)) X p hpp hXp (fun q hq => hF q (by aesop)) h_pairwise_cong

/-
The cardinality of `(Finset.Icc (-M) M).erase 0` is at most `2 * M.toNat`
    for `M ≥ 0`.
-/
theorem card_Icc_erase_zero_le (M : ℤ) (hM : 0 ≤ M) :
    ((Finset.Icc (-M) M).erase 0).card ≤ 2 * M.toNat := by
      cases M <;> simp_all +decide [ Int.toNat_of_nonneg ] ; linarith

/-
The anchored cluster is contained in a biUnion over short witness values.
-/
theorem cluster_subset_biUnion
    (Short : ℤ → Prop) (F : Finset ℤ) (p q0 x0 Mτ : ℤ)
    (hShort : ∀ x, Short x → 0 < |x| ∧ |x| ≤ Mτ) :
    anchoredCluster Short F p q0 x0 ⊆
      ((Finset.Icc (-Mτ) Mτ).erase 0).biUnion
        (fun x => F.filter (fun q => (p : ℤ) ∣ (q * x - q0 * x0))) := by
          intro q hq; contrapose! hq; simp_all +decide [anchoredCluster] ;
          exact fun hq' x hx y hy hxy => hq x ( hShort x hx |>.1 ) ( neg_le_of_abs_le ( hShort x hx |>.2 ) ) ( le_of_abs_le ( hShort x hx |>.2 ) ) hq' ( hxy.symm ▸ dvd_mul_right _ _ )

/-
Main cluster-size bound: each anchored cluster has at most 4*Mτ.toNat elements
    under the given arithmetic hypotheses.
-/
theorem cluster_card_bound
    (Short : ℤ → Prop) (F : Finset ℤ) (p q0 x0 X Mτ : ℤ)
    (hMτ_pos : 0 < Mτ) (hMτX : Mτ < X) (hXp : X ≤ p)
    (hp : Prime p)
    (hF : ∀ q ∈ F, X ≤ q ∧ q ≤ 2 * X)
    (hShort : ∀ x, Short x → 0 < |x| ∧ |x| ≤ Mτ) :
    (anchoredCluster Short F p q0 x0).card ≤ 4 * Mτ.toNat := by
      refine le_trans ( Finset.card_le_card ( cluster_subset_biUnion Short F p q0 x0 Mτ hShort ) ) ?_;
      refine' le_trans ( Finset.card_biUnion_le ) _;
      refine' le_trans ( Finset.sum_le_sum fun x hx => congruence_fiber_card_le_two F x ( q0 * x0 ) p X hp ( by linarith ) _ _ hF hXp ) _;
      · grind;
      · aesop;
      · norm_num +zetaDelta at *;
        linarith [ card_Icc_erase_zero_le Mτ hMτ_pos.le ]

/-! ### Part A': Cluster-size bound lifted to the family -/

/-
The cluster-size bound holds for every cluster in the anchored family.
-/
theorem family_cluster_card_bound
    (Short : ℤ → Prop) (F P X0 : Finset ℤ) (q0 X Mτ : ℤ)
    (hMτ_pos : 0 < Mτ) (hMτX : Mτ < X)
    (hP : ∀ p ∈ P, X ≤ p ∧ Prime p)
    (hF : ∀ q ∈ F, X ≤ q ∧ q ≤ 2 * X)
    (hShort : ∀ x, Short x → 0 < |x| ∧ |x| ≤ Mτ) :
    ∀ C ∈ anchoredClusterFamily Short F P X0 q0,
      (F ∩ C).card ≤ 4 * Mτ.toNat := by
        intros C hC
        obtain ⟨p, x0, hp, hx0, rfl⟩ : ∃ p ∈ P, ∃ x0 ∈ X0, C = anchoredCluster Short F p q0 x0 := by
          unfold anchoredClusterFamily at hC; aesop;
        convert cluster_card_bound Short F p q0 hp X Mτ _ _ _ _ _ _ using 1;
        any_goals tauto;
        · rw [ inter_anchoredCluster_eq ];
        · exact hP p x0 |>.1;
        · exact hP p x0 |>.2

/-! ### Part B: Nat.choose upper bound -/

/-
`Nat.choose n k ≤ n ^ k` for all `n` and `k`.
-/
theorem choose_le_pow (n k : ℕ) : Nat.choose n k ≤ n ^ k := by
  exact?

/-- If `a * b * L^k < Nat.choose n k`, then `a * b * Nat.choose L k < Nat.choose n k`.
    This lets us replace the abstract regime hypothesis with a simpler power bound. -/
theorem regime_of_pow_lt_choose (n L k a b : ℕ)
    (h : a * b * L ^ k < Nat.choose n k) :
    a * b * Nat.choose L k < Nat.choose n k := by
  calc a * b * Nat.choose L k
      ≤ a * b * L ^ k := Nat.mul_le_mul_left _ (choose_le_pow L k)
    _ < Nat.choose n k := h

/-! ### Part C: Unconditional corollary -/

/-- **Unconditional good-tuple theorem**: given arithmetic hypotheses on
    F, P, X0, Mτ, X (no separate cluster-size `hL` or abstract regime
    hypothesis needed). The regime condition is reduced to a raw `ℕ`
    power inequality. -/
theorem good_kSubset_exists_unconditional
    (Short : ℤ → Prop) (F P X0 : Finset ℤ) (q0 X Mτ : ℤ) (k : ℕ)
    (hMτ_pos : 0 < Mτ) (hMτX : Mτ < X)
    (hP : ∀ p ∈ P, X ≤ p ∧ Prime p)
    (hF : ∀ q ∈ F, X ≤ q ∧ q ≤ 2 * X)
    (hShort : ∀ x, Short x → 0 < |x| ∧ |x| ≤ Mτ)
    (hregime : P.card * X0.card * (4 * Mτ.toNat) ^ k < Nat.choose F.card k) :
    hasAnchoredGoodKSubset Short F P X0 q0 k := by
  apply good_kSubset_exists_of_size' Short F P X0 q0 k (4 * Mτ.toNat)
  · exact family_cluster_card_bound Short F P X0 q0 X Mτ hMτ_pos hMτX hP hF hShort
  · exact regime_of_pow_lt_choose F.card (4 * Mτ.toNat) k P.card X0.card hregime

end