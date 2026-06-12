/-
  AnchoredDeterminantRank.lean

  Determinant obstruction for reference-anchored primitive concentration
  in the Erdős 306 conditional proof.

  **⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
  This file is part of the rational-collision / CRT-lattice component,
  which is sorry-free algebra/combinatorics but is **disconnected** from
  the main theorem `erdos_306`. The top result of this component,
  `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
  assumes the shell bound as a hypothesis.

  Two anchored hits for the same p, q₀, qᵢ satisfy:
    qᵢ xᵢ - q₀ x₀ = p yᵢ   and   qᵢ zᵢ - q₀ z₀ = p wᵢ
  Cross-multiplying and subtracting gives:
    qᵢ (xᵢ z₀ - zᵢ x₀) = p (yᵢ z₀ - wᵢ x₀)
  so if p is coprime to qᵢ, then p ∣ (xᵢ z₀ - zᵢ x₀),
  and if additionally |xᵢ z₀ - zᵢ x₀| < |p|, then xᵢ z₀ = zᵢ x₀.
-/
import Mathlib
import RequestProject.AnchoredCRTLattice

/-! ## Goal 1: Two-hit structure -/

/-- Two anchored cluster witnesses sharing the same ambient parameters p, q₀, q₁, …, q₄. -/
structure TwoAnchoredHits where
  p : ℤ
  q0 : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  z0 : ℤ
  z1 : ℤ
  z2 : ℤ
  z3 : ℤ
  z4 : ℤ
  y1 : ℤ
  y2 : ℤ
  y3 : ℤ
  y4 : ℤ
  w1 : ℤ
  w2 : ℤ
  w3 : ℤ
  w4 : ℤ
  hx1 : q1 * x1 - q0 * x0 = p * y1
  hx2 : q2 * x2 - q0 * x0 = p * y2
  hx3 : q3 * x3 - q0 * x0 = p * y3
  hx4 : q4 * x4 - q0 * x0 = p * y4
  hz1 : q1 * z1 - q0 * z0 = p * w1
  hz2 : q2 * z2 - q0 * z0 = p * w2
  hz3 : q3 * z3 - q0 * z0 = p * w3
  hz4 : q4 * z4 - q0 * z0 = p * w4

/-! ## Goal 2: Determinant identities -/

/-- The reference determinant: xᵢ z₀ - zᵢ x₀. -/
def detRef (xi zi x0 z0 : ℤ) : ℤ := xi * z0 - zi * x0

/-- The y-determinant: yᵢ z₀ - wᵢ x₀. -/
def detY (yi wi x0 z0 : ℤ) : ℤ := yi * z0 - wi * x0

theorem det_identity_1 (W : TwoAnchoredHits) :
    W.q1 * detRef W.x1 W.z1 W.x0 W.z0 =
      W.p * detY W.y1 W.w1 W.x0 W.z0 := by
  unfold detRef detY; linear_combination W.z0 * W.hx1 - W.x0 * W.hz1

theorem det_identity_2 (W : TwoAnchoredHits) :
    W.q2 * detRef W.x2 W.z2 W.x0 W.z0 =
      W.p * detY W.y2 W.w2 W.x0 W.z0 := by
  unfold detRef detY; linear_combination W.z0 * W.hx2 - W.x0 * W.hz2

theorem det_identity_3 (W : TwoAnchoredHits) :
    W.q3 * detRef W.x3 W.z3 W.x0 W.z0 =
      W.p * detY W.y3 W.w3 W.x0 W.z0 := by
  unfold detRef detY; linear_combination W.z0 * W.hx3 - W.x0 * W.hz3

theorem det_identity_4 (W : TwoAnchoredHits) :
    W.q4 * detRef W.x4 W.z4 W.x0 W.z0 =
      W.p * detY W.y4 W.w4 W.x0 W.z0 := by
  unfold detRef detY; linear_combination W.z0 * W.hx4 - W.x0 * W.hz4

/-! ## Goal 3: Determinant divisibility -/

theorem det_dvd_1 (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q1) :
    W.p ∣ detRef W.x1 W.z1 W.x0 W.z0 := by
  have h := det_identity_1 W
  have hdvd : W.p ∣ W.q1 * detRef W.x1 W.z1 W.x0 W.z0 :=
    ⟨detY W.y1 W.w1 W.x0 W.z0, h⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem det_dvd_2 (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q2) :
    W.p ∣ detRef W.x2 W.z2 W.x0 W.z0 := by
  have h := det_identity_2 W
  have hdvd : W.p ∣ W.q2 * detRef W.x2 W.z2 W.x0 W.z0 :=
    ⟨detY W.y2 W.w2 W.x0 W.z0, h⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem det_dvd_3 (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q3) :
    W.p ∣ detRef W.x3 W.z3 W.x0 W.z0 := by
  have h := det_identity_3 W
  have hdvd : W.p ∣ W.q3 * detRef W.x3 W.z3 W.x0 W.z0 :=
    ⟨detY W.y3 W.w3 W.x0 W.z0, h⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem det_dvd_4 (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q4) :
    W.p ∣ detRef W.x4 W.z4 W.x0 W.z0 := by
  have h := det_identity_4 W
  have hdvd : W.p ∣ W.q4 * detRef W.x4 W.z4 W.x0 W.z0 :=
    ⟨detY W.y4 W.w4 W.x0 W.z0, h⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

/-! ## Goal 4: Small determinant vanishing -/

/-- If `p ∣ d` and `|d| < |p|`, then `d = 0`. -/
theorem eq_zero_of_dvd_of_abs_lt
    {p d : ℤ} (_hp : 0 < |p|) (hdvd : p ∣ d) (hlt : |d| < |p|) :
    d = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  simp only [Int.abs_eq_natAbs] at hlt
  exact_mod_cast hlt

theorem det_eq_zero_of_small_1
    (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q1)
    (hsmall : |detRef W.x1 W.z1 W.x0 W.z0| < |W.p|) :
    detRef W.x1 W.z1 W.x0 W.z0 = 0 :=
  eq_zero_of_dvd_of_abs_lt (by linarith [abs_nonneg (detRef W.x1 W.z1 W.x0 W.z0)]) (det_dvd_1 W hcop) hsmall

theorem det_eq_zero_of_small_2
    (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q2)
    (hsmall : |detRef W.x2 W.z2 W.x0 W.z0| < |W.p|) :
    detRef W.x2 W.z2 W.x0 W.z0 = 0 :=
  eq_zero_of_dvd_of_abs_lt (by linarith [abs_nonneg (detRef W.x2 W.z2 W.x0 W.z0)]) (det_dvd_2 W hcop) hsmall

theorem det_eq_zero_of_small_3
    (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q3)
    (hsmall : |detRef W.x3 W.z3 W.x0 W.z0| < |W.p|) :
    detRef W.x3 W.z3 W.x0 W.z0 = 0 :=
  eq_zero_of_dvd_of_abs_lt (by linarith [abs_nonneg (detRef W.x3 W.z3 W.x0 W.z0)]) (det_dvd_3 W hcop) hsmall

theorem det_eq_zero_of_small_4
    (W : TwoAnchoredHits)
    (hcop : IsCoprime W.p W.q4)
    (hsmall : |detRef W.x4 W.z4 W.x0 W.z0| < |W.p|) :
    detRef W.x4 W.z4 W.x0 W.z0 = 0 :=
  eq_zero_of_dvd_of_abs_lt (by linarith [abs_nonneg (detRef W.x4 W.z4 W.x0 W.z0)]) (det_dvd_4 W hcop) hsmall

/-! ## Goal 5: Projective proportionality -/

/-- Two five-coordinate vectors are projectively proportional:
    xᵢ z₀ = zᵢ x₀ for all i. -/
def SameRefProjective
    (x0 x1 x2 x3 x4 z0 z1 z2 z3 z4 : ℤ) : Prop :=
  x1 * z0 = z1 * x0 ∧
  x2 * z0 = z2 * x0 ∧
  x3 * z0 = z3 * x0 ∧
  x4 * z0 = z4 * x0

theorem detRef_eq_zero_iff (xi zi x0 z0 : ℤ) :
    detRef xi zi x0 z0 = 0 ↔ xi * z0 = zi * x0 := by
  unfold detRef; constructor <;> intro h <;> linarith

/-- In a sufficiently small box, two short hits for the same residual prime
    are projectively proportional. -/
theorem sameRefProjective_of_small_dets
    (W : TwoAnchoredHits)
    (hcop1 : IsCoprime W.p W.q1)
    (hcop2 : IsCoprime W.p W.q2)
    (hcop3 : IsCoprime W.p W.q3)
    (hcop4 : IsCoprime W.p W.q4)
    (hs1 : |detRef W.x1 W.z1 W.x0 W.z0| < |W.p|)
    (hs2 : |detRef W.x2 W.z2 W.x0 W.z0| < |W.p|)
    (hs3 : |detRef W.x3 W.z3 W.x0 W.z0| < |W.p|)
    (hs4 : |detRef W.x4 W.z4 W.x0 W.z0| < |W.p|) :
    SameRefProjective W.x0 W.x1 W.x2 W.x3 W.x4
      W.z0 W.z1 W.z2 W.z3 W.z4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (detRef_eq_zero_iff _ _ _ _).mp (det_eq_zero_of_small_1 W hcop1 hs1)
  · exact (detRef_eq_zero_iff _ _ _ _).mp (det_eq_zero_of_small_2 W hcop2 hs2)
  · exact (detRef_eq_zero_iff _ _ _ _).mp (det_eq_zero_of_small_3 W hcop3 hs3)
  · exact (detRef_eq_zero_iff _ _ _ _).mp (det_eq_zero_of_small_4 W hcop4 hs4)

/-! ## Goal 6: Factorable relation from one anchored witness -/

/-- The pairwise elimination identity:
    qᵢ xᵢ yⱼ - qⱼ xⱼ yᵢ + q₀ x₀ (yᵢ - yⱼ) = 0. -/
def FactorableAnchoredRelation
    (q0 qi qj x0 xi xj yi yj : ℤ) : Prop :=
  qi * xi * yj - qj * xj * yi + q0 * x0 * (yi - yj) = 0

/-- The factorable relation follows from any two anchored equations
    qᵢ xᵢ - q₀ x₀ = p yᵢ and qⱼ xⱼ - q₀ x₀ = p yⱼ. -/
theorem factorable_of_two_anchored_eqs
    {q0 qi qj x0 xi xj yi yj p : ℤ}
    (hi : qi * xi - q0 * x0 = p * yi)
    (hj : qj * xj - q0 * x0 = p * yj) :
    FactorableAnchoredRelation q0 qi qj x0 xi xj yi yj := by
  unfold FactorableAnchoredRelation
  linear_combination yj * hi - yi * hj

theorem factorable_12 (W : AnchoredClusterWitness) :
    FactorableAnchoredRelation W.q0 W.q1 W.q2 W.x0 W.x1 W.x2 W.y1 W.y2 :=
  factorable_of_two_anchored_eqs W.h1 W.h2

theorem factorable_13 (W : AnchoredClusterWitness) :
    FactorableAnchoredRelation W.q0 W.q1 W.q3 W.x0 W.x1 W.x3 W.y1 W.y3 :=
  factorable_of_two_anchored_eqs W.h1 W.h3

theorem factorable_14 (W : AnchoredClusterWitness) :
    FactorableAnchoredRelation W.q0 W.q1 W.q4 W.x0 W.x1 W.x4 W.y1 W.y4 :=
  factorable_of_two_anchored_eqs W.h1 W.h4

theorem factorable_23 (W : AnchoredClusterWitness) :
    FactorableAnchoredRelation W.q0 W.q2 W.q3 W.x0 W.x2 W.x3 W.y2 W.y3 :=
  factorable_of_two_anchored_eqs W.h2 W.h3

theorem factorable_24 (W : AnchoredClusterWitness) :
    FactorableAnchoredRelation W.q0 W.q2 W.q4 W.x0 W.x2 W.x4 W.y2 W.y4 :=
  factorable_of_two_anchored_eqs W.h2 W.h4

theorem factorable_34 (W : AnchoredClusterWitness) :
    FactorableAnchoredRelation W.q0 W.q3 W.q4 W.x0 W.x3 W.x4 W.y3 W.y4 :=
  factorable_of_two_anchored_eqs W.h3 W.h4

/-! ## Goal 7: Anchored factorable shell -/

/-- An anchored factorable shell bundles all six pairwise factorable relations
    derived from an anchored cluster witness. -/
structure AnchoredFactorableShell where
  q0 : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  y1 : ℤ
  y2 : ℤ
  y3 : ℤ
  y4 : ℤ
  rel12 : FactorableAnchoredRelation q0 q1 q2 x0 x1 x2 y1 y2
  rel13 : FactorableAnchoredRelation q0 q1 q3 x0 x1 x3 y1 y3
  rel14 : FactorableAnchoredRelation q0 q1 q4 x0 x1 x4 y1 y4
  rel23 : FactorableAnchoredRelation q0 q2 q3 x0 x2 x3 y2 y3
  rel24 : FactorableAnchoredRelation q0 q2 q4 x0 x2 x4 y2 y4
  rel34 : FactorableAnchoredRelation q0 q3 q4 x0 x3 x4 y3 y4

/-- Every `AnchoredClusterWitness` produces an `AnchoredFactorableShell`. -/
def anchoredFactorableShell_of_witness (W : AnchoredClusterWitness) :
    AnchoredFactorableShell where
  q0 := W.q0; q1 := W.q1; q2 := W.q2; q3 := W.q3; q4 := W.q4
  x0 := W.x0; x1 := W.x1; x2 := W.x2; x3 := W.x3; x4 := W.x4
  y1 := W.y1; y2 := W.y2; y3 := W.y3; y4 := W.y4
  rel12 := factorable_12 W
  rel13 := factorable_13 W
  rel14 := factorable_14 W
  rel23 := factorable_23 W
  rel24 := factorable_24 W
  rel34 := factorable_34 W
