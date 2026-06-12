/-
  SplitStarCorrelation.lean

  Split-star interpretation of six-variable CRT interval hits and the exact
  factorable ternary relations they produce, for the Erdős 306 conditional proof.

  **⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
  This file is part of the rational-collision / CRT-lattice component,
  which is sorry-free algebra/combinatorics but is **disconnected** from
  the main theorem `erdos_306`. The top result of this component,
  `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
  assumes the shell bound as a hypothesis.

  Paper-side meaning:
    six-variable CRT hit ⟺ split anchored star ⟹ three factorable ternary relations

  Also exposes the exact correlation object  ∑_p A₀₄(p) B₁₂₃(p).
-/
import Mathlib
import RequestProject.ResidualPrimeShellCRT

/-! ## Goal 1: Split-star structure and predicates -/

/-- A split anchored star bundles all coordinates and the four defining equations:
      p * aᵢ = qᵢ * xᵢ - q₄ * x₄   (i = 1,2,3)
      p * y₄ = q₄ * z₄ - q₀ * x₀
    The "split" refers to z₄ being a free variable; the original anchored ray
    is the diagonal subcase z₄ = x₄. -/
structure SplitAnchoredStar where
  p : ℤ
  q0 : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  x0 : ℤ
  x4 : ℤ
  z4 : ℤ
  y4 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  h1 : p * a1 = q1 * x1 - q4 * x4
  h2 : p * a2 = q2 * x2 - q4 * x4
  h3 : p * a3 = q3 * x3 - q4 * x4
  h4 : p * y4 = q4 * z4 - q0 * x0

/-- Predicate version of the split anchored star. -/
def IsSplitAnchoredStar
    (p q0 q1 q2 q3 q4 x0 x4 z4 y4 a1 a2 a3 x1 x2 x3 : ℤ) : Prop :=
  p * a1 = q1 * x1 - q4 * x4 ∧
  p * a2 = q2 * x2 - q4 * x4 ∧
  p * a3 = q3 * x3 - q4 * x4 ∧
  p * y4 = q4 * z4 - q0 * x0

theorem isSplitAnchoredStar_of_splitAnchoredStar (S : SplitAnchoredStar) :
    IsSplitAnchoredStar S.p S.q0 S.q1 S.q2 S.q3 S.q4
      S.x0 S.x4 S.z4 S.y4 S.a1 S.a2 S.a3 S.x1 S.x2 S.x3 :=
  ⟨S.h1, S.h2, S.h3, S.h4⟩

/-! ## Goal 2: Reconstruct split star from six-variable divisibility -/

/-- From six-variable divisibility data, reconstruct a `SplitAnchoredStar` by setting
    xᵢ = (p * aᵢ + q₄ * x₄) / qᵢ  and  z₄ = (p * y₄ + q₀ * x₀) / q₄. -/
theorem splitAnchoredStar_of_sixVarDivisibility
    {p q0 q1 q2 q3 q4 : ℤ}
    (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) (hq3 : q3 ≠ 0) (hq4 : q4 ≠ 0)
    (D : SixVarCRTData)
    (hdiv : SixVarDivisibility p q0 q1 q2 q3 q4 D) :
    ∃ S : SplitAnchoredStar,
      S.p = p ∧ S.q0 = q0 ∧ S.q1 = q1 ∧ S.q2 = q2 ∧ S.q3 = q3 ∧ S.q4 = q4 ∧
      S.x0 = D.x0 ∧ S.x4 = D.x4 ∧ S.y4 = D.y4 ∧
      S.a1 = D.a1 ∧ S.a2 = D.a2 ∧ S.a3 = D.a3 ∧
      S.x1 = (p * D.a1 + q4 * D.x4) / q1 ∧
      S.x2 = (p * D.a2 + q4 * D.x4) / q2 ∧
      S.x3 = (p * D.a3 + q4 * D.x4) / q3 ∧
      S.z4 = (p * D.y4 + q0 * D.x0) / q4 := by
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩, ⟨k4, hk4⟩⟩ := hdiv
  have heq1 : p * D.a1 = q1 * ((p * D.a1 + q4 * D.x4) / q1) - q4 * D.x4 := by
    rw [hk1, Int.mul_ediv_cancel_left _ hq1]; linarith
  have heq2 : p * D.a2 = q2 * ((p * D.a2 + q4 * D.x4) / q2) - q4 * D.x4 := by
    rw [hk2, Int.mul_ediv_cancel_left _ hq2]; linarith
  have heq3 : p * D.a3 = q3 * ((p * D.a3 + q4 * D.x4) / q3) - q4 * D.x4 := by
    rw [hk3, Int.mul_ediv_cancel_left _ hq3]; linarith
  have heq4 : p * D.y4 = q4 * ((p * D.y4 + q0 * D.x0) / q4) - q0 * D.x0 := by
    rw [hk4, Int.mul_ediv_cancel_left _ hq4]; linarith
  exact ⟨⟨p, q0, q1, q2, q3, q4, D.x0, D.x4,
    (p * D.y4 + q0 * D.x0) / q4, D.y4, D.a1, D.a2, D.a3,
    (p * D.a1 + q4 * D.x4) / q1,
    (p * D.a2 + q4 * D.x4) / q2,
    (p * D.a3 + q4 * D.x4) / q3,
    heq1, heq2, heq3, heq4⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Goal 3: Split star gives six-variable divisibility -/

/-- A split anchored star directly yields six-variable divisibility. -/
theorem sixVarDivisibility_of_splitAnchoredStar
    (S : SplitAnchoredStar) :
    SixVarDivisibility S.p S.q0 S.q1 S.q2 S.q3 S.q4
      ⟨S.x0, S.x4, S.y4, S.a1, S.a2, S.a3⟩ := by
  simp only [SixVarDivisibility]
  exact ⟨⟨S.x1, by linarith [S.h1]⟩,
         ⟨S.x2, by linarith [S.h2]⟩,
         ⟨S.x3, by linarith [S.h3]⟩,
         ⟨S.z4, by linarith [S.h4]⟩⟩

/-! ## Goal 4: Diagonal bridge to anchored hits -/

/-- An `AnchoredCRTProductHit` gives a `SplitAnchoredStar` with z₄ = x₄. -/
def splitAnchoredStar_of_anchoredCRTProductHit
    (H : AnchoredCRTProductHit) : SplitAnchoredStar where
  p := H.p
  q0 := H.q0
  q1 := H.q1
  q2 := H.q2
  q3 := H.q3
  q4 := H.q4
  x0 := H.x0
  x4 := H.x4
  z4 := H.x4
  y4 := H.y4
  a1 := H.a1
  a2 := H.a2
  a3 := H.a3
  x1 := H.x1
  x2 := H.x2
  x3 := H.x3
  h1 := by linarith [H.h1]
  h2 := by linarith [H.h2]
  h3 := by linarith [H.h3]
  h4 := by linarith [H.h4]

/-- The split star coming from an anchored hit has z₄ = x₄. -/
theorem splitAnchoredStar_of_anchoredCRTProductHit_diagonal
    (H : AnchoredCRTProductHit) :
    (splitAnchoredStar_of_anchoredCRTProductHit H).z4 =
    (splitAnchoredStar_of_anchoredCRTProductHit H).x4 := rfl

/-- Conversely, a split star with z₄ = x₄ yields an `AnchoredCRTProductHit`. -/
def anchoredCRTProductHit_of_splitAnchoredStar_diagonal
    (S : SplitAnchoredStar) (hdiag : S.z4 = S.x4) :
    AnchoredCRTProductHit where
  p := S.p
  q0 := S.q0
  q1 := S.q1
  q2 := S.q2
  q3 := S.q3
  q4 := S.q4
  x0 := S.x0
  x4 := S.x4
  x1 := S.x1
  x2 := S.x2
  x3 := S.x3
  y4 := S.y4
  a1 := S.a1
  a2 := S.a2
  a3 := S.a3
  h1 := by linarith [S.h1]
  h2 := by linarith [S.h2]
  h3 := by linarith [S.h3]
  h4 := by rw [← hdiag]; linarith [S.h4]

/-- A split star with z₄ = x₄ satisfies the anchored lattice equations. -/
theorem inAnchoredCRTLattice_of_splitStar_diagonal
    (S : SplitAnchoredStar) (hdiag : S.z4 = S.x4) :
    InAnchoredCRTLattice S.p S.q0 S.q1 S.q2 S.q3 S.q4
      S.x0 S.x4 S.x1 S.x2 S.x3 S.y4 S.a1 S.a2 S.a3 :=
  ⟨by linarith [S.h1], by linarith [S.h2], by linarith [S.h3],
   by rw [← hdiag]; linarith [S.h4]⟩

/-! ## Goal 5: Factorable ternary relations -/

/-- The factorable ternary relation arising from eliminating p between
    the i-th ray equation and the anchor equation:
      qᵢ * (xᵢ * y₄) + q₀ * (x₀ * aᵢ) - q₄ * (x₄ * y₄ + z₄ * aᵢ) = 0 -/
def SplitFactorableRelation
    (q0 q4 qi x0 x4 z4 y4 ai xi : ℤ) : Prop :=
  qi * (xi * y4) + q0 * (x0 * ai) - q4 * (x4 * y4 + z4 * ai) = 0

/-- Helper: the factorable relation follows from the linear combination y₄·hᵢ − aᵢ·h₄. -/
private theorem factorable_of_star_eqs
    {p q0 q4 qi x0 x4 z4 y4 ai xi : ℤ}
    (hi : p * ai = qi * xi - q4 * x4)
    (h4 : p * y4 = q4 * z4 - q0 * x0) :
    qi * (xi * y4) + q0 * (x0 * ai) - q4 * (x4 * y4 + z4 * ai) = 0 := by
  have e1 : p * ai * y4 = (qi * xi - q4 * x4) * y4 := by rw [hi]
  have e2 : p * y4 * ai = (q4 * z4 - q0 * x0) * ai := by rw [h4]
  have : p * ai * y4 = p * y4 * ai := by ring
  nlinarith

/-- The factorable ternary relation for index 1, derived from
    y₄ · h₁ − a₁ · h₄. -/
theorem splitFactorableRelation_of_splitStar_1
    (S : SplitAnchoredStar) :
    SplitFactorableRelation S.q0 S.q4 S.q1 S.x0 S.x4 S.z4 S.y4 S.a1 S.x1 := by
  exact factorable_of_star_eqs S.h1 S.h4

/-- The factorable ternary relation for index 2. -/
theorem splitFactorableRelation_of_splitStar_2
    (S : SplitAnchoredStar) :
    SplitFactorableRelation S.q0 S.q4 S.q2 S.x0 S.x4 S.z4 S.y4 S.a2 S.x2 := by
  exact factorable_of_star_eqs S.h2 S.h4

/-- The factorable ternary relation for index 3. -/
theorem splitFactorableRelation_of_splitStar_3
    (S : SplitAnchoredStar) :
    SplitFactorableRelation S.q0 S.q4 S.q3 S.x0 S.x4 S.z4 S.y4 S.a3 S.x3 := by
  exact factorable_of_star_eqs S.h3 S.h4

/-- Package of all three factorable ternary relations from a split star. -/
structure SplitFactorableShell (S : SplitAnchoredStar) : Prop where
  rel1 : SplitFactorableRelation S.q0 S.q4 S.q1 S.x0 S.x4 S.z4 S.y4 S.a1 S.x1
  rel2 : SplitFactorableRelation S.q0 S.q4 S.q2 S.x0 S.x4 S.z4 S.y4 S.a2 S.x2
  rel3 : SplitFactorableRelation S.q0 S.q4 S.q3 S.x0 S.x4 S.z4 S.y4 S.a3 S.x3

/-- A split anchored star yields all three factorable ternary relations. -/
theorem splitFactorableShell_of_splitStar (S : SplitAnchoredStar) :
    SplitFactorableShell S :=
  ⟨splitFactorableRelation_of_splitStar_1 S,
   splitFactorableRelation_of_splitStar_2 S,
   splitFactorableRelation_of_splitStar_3 S⟩

/-! ## Goal 6: Representation functions and correlation statement -/

/-- A₀₄(p) counts pairs (x₀, y₄) ∈ X0 × Y4 satisfying
    q₄ ∣ p * y₄ + q₀ * x₀. -/
noncomputable def A04 (q0 q4 p : ℤ) (X0 Y4 : Finset ℤ) : ℕ :=
  ((X0 ×ˢ Y4).filter (fun xy => q4 ∣ p * xy.2 + q0 * xy.1)).card

/-- B₁₂₃(p) counts quadruples (x₄, a₁, a₂, a₃) ∈ X4 × A1 × A2 × A3 satisfying
    the three congruences qᵢ ∣ p * aᵢ + q₄ * x₄. -/
noncomputable def B123 (q1 q2 q3 q4 p : ℤ)
    (X4 A1 A2 A3 : Finset ℤ) : ℕ :=
  ((X4 ×ˢ (A1 ×ˢ (A2 ×ˢ A3))).filter (fun t =>
    let x4 := t.1
    let a1 := t.2.1
    let a2 := t.2.2.1
    let a3 := t.2.2.2
    q1 ∣ p * a1 + q4 * x4 ∧
    q2 ∣ p * a2 + q4 * x4 ∧
    q3 ∣ p * a3 + q4 * x4)).card

/-- The split correlation sum: ∑_{p ∈ P} A₀₄(p) · B₁₂₃(p). -/
noncomputable def SplitCorrelation
    (q0 q1 q2 q3 q4 : ℤ)
    (P X0 Y4 X4 A1 A2 A3 : Finset ℤ) : ℕ :=
  ∑ p ∈ P, A04 q0 q4 p X0 Y4 * B123 q1 q2 q3 q4 p X4 A1 A2 A3

/-- The "flat" set of seven-tuples (p, x₀, y₄, x₄, a₁, a₂, a₃) satisfying
    all four divisibility conditions. -/
noncomputable def SplitCorrelationSet
    (q0 q1 q2 q3 q4 : ℤ)
    (P X0 Y4 X4 A1 A2 A3 : Finset ℤ) : Finset (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  (P ×ˢ (X0 ×ˢ (Y4 ×ˢ (X4 ×ˢ (A1 ×ˢ (A2 ×ˢ A3)))))).filter (fun t =>
    let p := t.1
    let x0 := t.2.1
    let y4 := t.2.2.1
    let x4 := t.2.2.2.1
    let a1 := t.2.2.2.2.1
    let a2 := t.2.2.2.2.2.1
    let a3 := t.2.2.2.2.2.2
    q4 ∣ p * y4 + q0 * x0 ∧
    q1 ∣ p * a1 + q4 * x4 ∧
    q2 ∣ p * a2 + q4 * x4 ∧
    q3 ∣ p * a3 + q4 * x4)

/-
The correlation sum equals the cardinality of the flat set of seven-tuples.
-/
theorem splitCorrelation_eq_card
    (q0 q1 q2 q3 q4 : ℤ)
    (P X0 Y4 X4 A1 A2 A3 : Finset ℤ) :
    SplitCorrelation q0 q1 q2 q3 q4 P X0 Y4 X4 A1 A2 A3 =
    (SplitCorrelationSet q0 q1 q2 q3 q4 P X0 Y4 X4 A1 A2 A3).card := by
  unfold SplitCorrelation SplitCorrelationSet;
  simp +decide only [A04, Finset.card_filter, B123];
  simp +decide only [Finset.sum_product, Finset.sum_mul _ _ _];
  refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun z hz => _;
  split_ifs <;> simp +decide [ * ]

/-! ## Goal 7 (Optional): Anchor-side collision determinant -/

/-
If two pairs satisfy the anchor congruence mod q₄ and q₀, q₄ are coprime,
    then q₄ divides the collision determinant x * y' - x' * y.
-/
theorem q4_dvd_anchor_collision_det
    {q0 q4 p x y x' y' : ℤ}
    (hc : IsCoprime q0 q4)
    (h1 : q4 ∣ p * y + q0 * x)
    (h2 : q4 ∣ p * y' + q0 * x') :
    q4 ∣ x * y' - x' * y := by
  obtain ⟨ a, ha ⟩ := h1;
  obtain ⟨ b, hb ⟩ := h2;
  obtain ⟨ u, v, h ⟩ := hc;
  exact ⟨ u * ( a * y' - b * y ) + v * ( x * y' - x' * y ), by linear_combination -h * ( x * y' - x' * y ) + ha * u * y' - hb * u * y ⟩

/-
If |det| < |q₄| and q₄ divides det, then det = 0.
-/
theorem anchor_collision_det_zero_of_small
    {q4 : ℤ} {det : ℤ}
    (hdvd : q4 ∣ det)
    (_hq4 : q4 ≠ 0)
    (hsmall : |det| < |q4|) :
    det = 0 := by
  exact by_contra fun h => hsmall.not_ge <| Int.le_of_dvd ( abs_pos.mpr h ) <| by simpa using hdvd;