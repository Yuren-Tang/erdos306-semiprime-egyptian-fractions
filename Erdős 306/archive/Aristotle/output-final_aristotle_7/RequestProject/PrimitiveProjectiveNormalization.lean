/-
  PrimitiveProjectiveNormalization.lean

  Fixed-p fibre cleanup for the Erdős 306 conditional proof.

  After AnchoredDeterminantRank.lean establishes that two anchored hits with
  the same residual prime are projectively proportional (x_i z_0 = z_i x_0),
  this file proves:

    projectively proportional + primitive ⟹ equal up to sign.

  This removes fixed-p multiplicity from the weighted anchored primitive
  inverse theorem.
-/
import Mathlib
import RequestProject.AnchoredDeterminantRank

/-! ## Goal 1: Five-coordinate primitive predicate and Bézout certificate -/

/-- A five-coordinate integer vector is primitive: no integer d with |d| > 1
    divides all five coordinates. -/
def PrimitiveFiveRay (x0 x1 x2 x3 x4 : Int) : Prop :=
  ∀ d : Int, 1 < |d| →
    (d ∣ x0 ∧ d ∣ x1 ∧ d ∣ x2 ∧ d ∣ x3 ∧ d ∣ x4) → False

/-- A Bézout certificate for a five-coordinate vector: there exist integer
    coefficients summing to 1. -/
def BezoutFive (x0 x1 x2 x3 x4 : Int) : Prop :=
  ∃ c0 c1 c2 c3 c4 : Int,
    c0 * x0 + c1 * x1 + c2 * x2 + c3 * x3 + c4 * x4 = 1

/-! ## Goal 2: Projective proportionality gives divisibility -/

theorem x0_dvd_z0_of_sameRefProjective_of_bezout
    {x0 x1 x2 x3 x4 z0 z1 z2 z3 z4 : ℤ}
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hbez : BezoutFive x0 x1 x2 x3 x4) :
    x0 ∣ z0 := by
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ : ∃ c0 c1 c2 c3 c4 : ℤ, c0 * x0 + c1 * x1 + c2 * x2 + c3 * x3 + c4 * x4 = 1 := hbez;
  use c0 * z0 + c1 * z1 + c2 * z2 + c3 * z3 + c4 * z4;
  linear_combination -hc * z0 + hproj.1 * c1 + hproj.2.1 * c2 + hproj.2.2.1 * c3 + hproj.2.2.2 * c4

/-
SameRefProjective is symmetric in the two rays (up to reordering).
-/
theorem sameRefProjective_symm
    {x0 x1 x2 x3 x4 z0 z1 z2 z3 z4 : ℤ}
    (h : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4) :
    SameRefProjective z0 z1 z2 z3 z4 x0 x1 x2 x3 x4 := by
  cases h;
  exact ⟨ by linarith, by linarith, by linarith, by linarith ⟩

theorem z0_dvd_x0_of_sameRefProjective_of_bezout
    {x0 x1 x2 x3 x4 z0 z1 z2 z3 z4 : ℤ}
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hbez : BezoutFive z0 z1 z2 z3 z4) :
    z0 ∣ x0 :=
  x0_dvd_z0_of_sameRefProjective_of_bezout (sameRefProjective_symm hproj) hbez

/-! ## Goal 3: Mutual divisibility gives sign equality -/

theorem eq_or_neg_of_mutual_dvd
    {a b : Int} (_ha : a ≠ 0) (_hb : b ≠ 0)
    (hab : a ∣ b) (hba : b ∣ a) :
    b = a ∨ b = -a := by
  exact Int.natAbs_eq_natAbs_iff.mp ( Nat.dvd_antisymm ( Int.natAbs_dvd_natAbs.mpr hab ) ( Int.natAbs_dvd_natAbs.mpr hba ) ▸ rfl )

/-! ## Goal 4: Main normalization theorem -/

/-
Helper: if x0 ≠ 0 and x_i * z0 = z_i * x0 and z0 = s * x0 for some sign s,
    then z_i = s * x_i.
-/
theorem coord_eq_of_proj_and_sign
    {x0 xi z0 zi s : ℤ} (hx0 : x0 ≠ 0)
    (hproj : xi * z0 = zi * x0)
    (hsign : z0 = s * x0) :
    zi = s * xi := by
  exact mul_left_cancel₀ hx0 ( by subst hsign; linarith )

/-
Two projectively proportional primitive rays with nonzero reference
    coordinates agree up to global sign.
-/
theorem sameRefProjective_eq_or_neg_of_bezout
    {x0 x1 x2 x3 x4 z0 z1 z2 z3 z4 : ℤ}
    (hx0 : x0 ≠ 0) (hz0 : z0 ≠ 0)
    (hproj : SameRefProjective x0 x1 x2 x3 x4 z0 z1 z2 z3 z4)
    (hbezx : BezoutFive x0 x1 x2 x3 x4)
    (hbezz : BezoutFive z0 z1 z2 z3 z4) :
    (z0 = x0 ∧ z1 = x1 ∧ z2 = x2 ∧ z3 = x3 ∧ z4 = x4)
    ∨
    (z0 = -x0 ∧ z1 = -x1 ∧ z2 = -x2 ∧ z3 = -x3 ∧ z4 = -x4) := by
  have hz0_eq : z0 = x0 ∨ z0 = -x0 := by
    apply eq_or_neg_of_mutual_dvd hx0 hz0 (x0_dvd_z0_of_sameRefProjective_of_bezout hproj hbezx) (z0_dvd_x0_of_sameRefProjective_of_bezout hproj hbezz);
  rcases hz0_eq with ( rfl | rfl ) <;> simp_all +decide [ SameRefProjective ];
  exact Or.inr ⟨ mul_left_cancel₀ hx0 <| by linarith, mul_left_cancel₀ hx0 <| by linarith, mul_left_cancel₀ hx0 <| by linarith, mul_left_cancel₀ hx0 <| by linarith ⟩

/-! ## Goal 5: Primitive predicate version (optional) -/

-- bezoutFive_of_primitiveFiveRay is API-heavy; we skip it and use BezoutFive
-- hypotheses directly. The Bezout version (Goal 4) suffices for the paper-side
-- argument, since primitive integer vectors admit such certificates by standard
-- number theory.

/-! ## Goal 6: Connection to determinant rank -/

/-
If two anchored hits produce projective proportionality (via small
    determinants), and both rays have Bézout certificates and nonzero reference
    coordinates, then the two rays are equal up to sign.
-/
theorem normalized_of_small_dets
    (W : TwoAnchoredHits)
    (hcop1 : IsCoprime W.p W.q1)
    (hcop2 : IsCoprime W.p W.q2)
    (hcop3 : IsCoprime W.p W.q3)
    (hcop4 : IsCoprime W.p W.q4)
    (hs1 : |detRef W.x1 W.z1 W.x0 W.z0| < |W.p|)
    (hs2 : |detRef W.x2 W.z2 W.x0 W.z0| < |W.p|)
    (hs3 : |detRef W.x3 W.z3 W.x0 W.z0| < |W.p|)
    (hs4 : |detRef W.x4 W.z4 W.x0 W.z0| < |W.p|)
    (hx0 : W.x0 ≠ 0) (hz0 : W.z0 ≠ 0)
    (hbezx : BezoutFive W.x0 W.x1 W.x2 W.x3 W.x4)
    (hbezz : BezoutFive W.z0 W.z1 W.z2 W.z3 W.z4) :
    (W.z0 = W.x0 ∧ W.z1 = W.x1 ∧ W.z2 = W.x2 ∧ W.z3 = W.x3 ∧ W.z4 = W.x4)
    ∨
    (W.z0 = -W.x0 ∧ W.z1 = -W.x1 ∧ W.z2 = -W.x2 ∧ W.z3 = -W.x3 ∧ W.z4 = -W.x4) := by
  apply sameRefProjective_eq_or_neg_of_bezout hx0 hz0 (sameRefProjective_of_small_dets W hcop1 hcop2 hcop3 hcop4 hs1 hs2 hs3 hs4) hbezx hbezz