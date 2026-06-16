/-
  AnchoredCRTLattice.lean

  Reference-anchored algebraic interface for reciprocal clusters
  in the Erdős 306 conditional proof.

  **⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
  This file is part of the rational-collision / CRT-lattice component,
  which is sorry-free algebra/combinatorics but is **disconnected** from
  the main theorem `erdos_306`. The top result of this component,
  `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
  assumes the shell bound as a hypothesis.

  The full anchored equations are:
    q_i x_i - q_0 x_0 = p y_i   (1 ≤ i ≤ 4)
  After using q_4 as base and setting a_i = y_i - y_4, these become:
    q_i x_i - q_4 x_4 = p a_i   (1 ≤ i ≤ 3)
  together with the reference-anchor equation:
    q_4 x_4 - q_0 x_0 = p y_4.

  Generic single-equation lemmas (`baseDivides_of_latticeEq`,
  `xi_eq_div_of_latticeEq`, `latticeEq_smul`, etc.) are imported from
  `CRTLatticeCore.lean` via `ValidCRTLattice.lean`.
-/
import Mathlib
import RequestProject.ValidCRTLattice

/-! ## Goal 1: Anchored cluster witness -/

/-- An anchored cluster witness bundles the original five-seed equations
    q_i x_i - q_0 x_0 = p y_i  (1 ≤ i ≤ 4). -/
structure AnchoredClusterWitness where
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
  y1 : ℤ
  y2 : ℤ
  y3 : ℤ
  y4 : ℤ
  h1 : q1 * x1 - q0 * x0 = p * y1
  h2 : q2 * x2 - q0 * x0 = p * y2
  h3 : q3 * x3 - q0 * x0 = p * y3
  h4 : q4 * x4 - q0 * x0 = p * y4

/-- Base difference a_1 = y_1 - y_4. -/
def aa1 (W : AnchoredClusterWitness) : ℤ := W.y1 - W.y4

/-- Base difference a_2 = y_2 - y_4. -/
def aa2 (W : AnchoredClusterWitness) : ℤ := W.y2 - W.y4

/-- Base difference a_3 = y_3 - y_4. -/
def aa3 (W : AnchoredClusterWitness) : ℤ := W.y3 - W.y4

/-- The first anchored base-difference equation. -/
theorem anchored_base_diff_1 (W : AnchoredClusterWitness) :
    W.q1 * W.x1 - W.q4 * W.x4 = W.p * aa1 W := by
  unfold aa1; linarith [W.h1, W.h4]

/-- The second anchored base-difference equation. -/
theorem anchored_base_diff_2 (W : AnchoredClusterWitness) :
    W.q2 * W.x2 - W.q4 * W.x4 = W.p * aa2 W := by
  unfold aa2; linarith [W.h2, W.h4]

/-- The third anchored base-difference equation. -/
theorem anchored_base_diff_3 (W : AnchoredClusterWitness) :
    W.q3 * W.x3 - W.q4 * W.x4 = W.p * aa3 W := by
  unfold aa3; linarith [W.h3, W.h4]

/-! ## Goal 2: Anchored normalized lattice -/

/-- An anchored CRT product hit bundles the three normalized equations
    plus the reference-anchor equation. -/
structure AnchoredCRTProductHit where
  p : ℤ
  q0 : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  x0 : ℤ
  x4 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  y4 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  h1 : q1 * x1 - q4 * x4 = p * a1
  h2 : q2 * x2 - q4 * x4 = p * a2
  h3 : q3 * x3 - q4 * x4 = p * a3
  h4 : q4 * x4 - q0 * x0 = p * y4

/-- Predicate version of the anchored CRT lattice:
    the three normalized equations plus the anchor equation. -/
def InAnchoredCRTLattice
    (p q0 q1 q2 q3 q4 x0 x4 x1 x2 x3 y4 a1 a2 a3 : ℤ) : Prop :=
  q1 * x1 - q4 * x4 = p * a1 ∧
  q2 * x2 - q4 * x4 = p * a2 ∧
  q3 * x3 - q4 * x4 = p * a3 ∧
  q4 * x4 - q0 * x0 = p * y4

theorem inAnchoredCRTLattice_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit) :
    InAnchoredCRTLattice V.p V.q0 V.q1 V.q2 V.q3 V.q4
      V.x0 V.x4 V.x1 V.x2 V.x3 V.y4 V.a1 V.a2 V.a3 :=
  ⟨V.h1, V.h2, V.h3, V.h4⟩

def anchoredCRTProductHit_of_inAnchoredCRTLattice
    {p q0 q1 q2 q3 q4 x0 x4 x1 x2 x3 y4 a1 a2 a3 : ℤ}
    (h : InAnchoredCRTLattice p q0 q1 q2 q3 q4 x0 x4 x1 x2 x3 y4 a1 a2 a3) :
    AnchoredCRTProductHit where
  p := p; q0 := q0; q1 := q1; q2 := q2; q3 := q3; q4 := q4
  x0 := x0; x4 := x4; x1 := x1; x2 := x2; x3 := x3
  y4 := y4; a1 := a1; a2 := a2; a3 := a3
  h1 := h.1; h2 := h.2.1; h3 := h.2.2.1; h4 := h.2.2.2

/-! ## Goal 3: Bidirectional bridge -/

/-- An `AnchoredClusterWitness` produces an `AnchoredCRTProductHit`
    using the base differences a_i = y_i - y_4. -/
def anchoredCRTProductHit_of_anchoredClusterWitness
    (W : AnchoredClusterWitness) : AnchoredCRTProductHit where
  p := W.p; q0 := W.q0; q1 := W.q1; q2 := W.q2; q3 := W.q3; q4 := W.q4
  x0 := W.x0; x4 := W.x4; x1 := W.x1; x2 := W.x2; x3 := W.x3
  y4 := W.y4; a1 := aa1 W; a2 := aa2 W; a3 := aa3 W
  h1 := anchored_base_diff_1 W
  h2 := anchored_base_diff_2 W
  h3 := anchored_base_diff_3 W
  h4 := W.h4

/-- Conversely, an `AnchoredCRTProductHit` produces an `AnchoredClusterWitness`
    by setting y_i = a_i + y_4 (1 ≤ i ≤ 3). -/
def anchoredClusterWitness_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit) : AnchoredClusterWitness where
  p := V.p; q0 := V.q0; q1 := V.q1; q2 := V.q2; q3 := V.q3; q4 := V.q4
  x0 := V.x0; x1 := V.x1; x2 := V.x2; x3 := V.x3; x4 := V.x4
  y1 := V.a1 + V.y4; y2 := V.a2 + V.y4; y3 := V.a3 + V.y4; y4 := V.y4
  h1 := by linarith [V.h1, V.h4]
  h2 := by linarith [V.h2, V.h4]
  h3 := by linarith [V.h3, V.h4]
  h4 := V.h4

/-! ## Goal 4: Anchored implies unanchored valid hit -/

/-- An anchored CRT product hit gives the existing unanchored
    `ValidCRTProductHit` by forgetting q0, x0, y4, h4. -/
def validCRTProductHit_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit) : ValidCRTProductHit where
  p := V.p; q1 := V.q1; q2 := V.q2; q3 := V.q3; q4 := V.q4
  x4 := V.x4; x1 := V.x1; x2 := V.x2; x3 := V.x3
  a1 := V.a1; a2 := V.a2; a3 := V.a3
  h1 := V.h1; h2 := V.h2; h3 := V.h3

/-! ## Goal 5: Local CRT congruences including the anchor -/

/-- The anchor-equation divisibility: q_4 ∣ p y_4 + q_0 x_0. -/
theorem anchorDivides_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit) :
    BaseDivides V.q4 V.p V.y4 V.q0 V.x0 :=
  baseDivides_of_latticeEq V.h4

/-- The anchor local residue: if y_4 has inverse inv4 modulo q_4,
    then p ≡ x_0 * (-q_0 * inv4) [ZMOD q_4]. -/
theorem anchor_local_residue
    {q4 q0 p x4 x0 y4 inv4 : ℤ}
    (hinv : InvModWitness y4 q4 inv4)
    (h4 : q4 * x4 - q0 * x0 = p * y4) :
    p ≡ x0 * (-q0 * inv4) [ZMOD q4] :=
  local_residue_of_baseDivides hinv (baseDivides_of_latticeEq h4)

/-- Predicate for the four anchored CRT residues (three from the unanchored
    lattice plus the anchor residue). Uses a name distinct from the structure
    `AnchoredCRTProductHit`. -/
def AnchoredCRTResidues
    (q0 q1 q2 q3 q4 p x0 x4 a1 a2 a3 y4
      inv1 inv2 inv3 inv4 : ℤ) : Prop :=
  InvModWitness a1 q1 inv1 ∧
  InvModWitness a2 q2 inv2 ∧
  InvModWitness a3 q3 inv3 ∧
  InvModWitness y4 q4 inv4 ∧
  p ≡ x4 * (-q4 * inv1) [ZMOD q1] ∧
  p ≡ x4 * (-q4 * inv2) [ZMOD q2] ∧
  p ≡ x4 * (-q4 * inv3) [ZMOD q3] ∧
  p ≡ x0 * (-q0 * inv4) [ZMOD q4]

/-- An anchored CRT product hit plus inverse witnesses for a1, a2, a3, y4
    gives all four local congruences. -/
theorem anchoredCRTResidues_of_anchoredCRTProductHit
    (V : AnchoredCRTProductHit)
    (inv1 inv2 inv3 inv4 : ℤ)
    (hInv1 : InvModWitness V.a1 V.q1 inv1)
    (hInv2 : InvModWitness V.a2 V.q2 inv2)
    (hInv3 : InvModWitness V.a3 V.q3 inv3)
    (hInv4 : InvModWitness V.y4 V.q4 inv4) :
    AnchoredCRTResidues V.q0 V.q1 V.q2 V.q3 V.q4 V.p V.x0 V.x4
      V.a1 V.a2 V.a3 V.y4 inv1 inv2 inv3 inv4 := by
  refine ⟨hInv1, hInv2, hInv3, hInv4, ?_, ?_, ?_, ?_⟩
  · exact local_residue_of_baseDivides hInv1 (baseDivides_of_latticeEq V.h1)
  · exact local_residue_of_baseDivides hInv2 (baseDivides_of_latticeEq V.h2)
  · exact local_residue_of_baseDivides hInv3 (baseDivides_of_latticeEq V.h3)
  · exact anchor_local_residue hInv4 V.h4

/-! ## Goal 6: Homogeneous scaling

Uses the generic `latticeEq_smul` from `CRTLatticeCore`. -/

/-- The anchored lattice is homogeneous in all short variables:
    scaling by λ preserves membership. -/
theorem inAnchoredCRTLattice_smul
    {p q0 q1 q2 q3 q4 x0 x4 x1 x2 x3 y4 a1 a2 a3 lam : ℤ}
    (h : InAnchoredCRTLattice p q0 q1 q2 q3 q4
          x0 x4 x1 x2 x3 y4 a1 a2 a3) :
    InAnchoredCRTLattice p q0 q1 q2 q3 q4
      (lam * x0) (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * y4) (lam * a1) (lam * a2) (lam * a3) :=
  ⟨latticeEq_smul h.1, latticeEq_smul h.2.1,
   latticeEq_smul h.2.2.1, latticeEq_smul h.2.2.2⟩

/-- Scaling an `AnchoredCRTProductHit` by λ produces a new anchored hit. -/
def anchoredCRTProductHit_smul (V : AnchoredCRTProductHit) (lam : ℤ) :
    AnchoredCRTProductHit where
  p := V.p; q0 := V.q0; q1 := V.q1; q2 := V.q2; q3 := V.q3; q4 := V.q4
  x0 := lam * V.x0; x4 := lam * V.x4
  x1 := lam * V.x1; x2 := lam * V.x2; x3 := lam * V.x3
  y4 := lam * V.y4; a1 := lam * V.a1; a2 := lam * V.a2; a3 := lam * V.a3
  h1 := latticeEq_smul V.h1
  h2 := latticeEq_smul V.h2
  h3 := latticeEq_smul V.h3
  h4 := latticeEq_smul V.h4

/-! ## Goal 7: Primitive anchored ray -/

/-- A primitive anchored CRT ray: no integer with |d| > 1 divides all nine
    short coordinates simultaneously. -/
def PrimitiveAnchoredCRTRay
    (x0 x4 x1 x2 x3 y4 a1 a2 a3 : ℤ) : Prop :=
  ∀ d : ℤ, 1 < |d| →
    (d ∣ x0 ∧ d ∣ x4 ∧ d ∣ x1 ∧ d ∣ x2 ∧ d ∣ x3 ∧
     d ∣ y4 ∧ d ∣ a1 ∧ d ∣ a2 ∧ d ∣ a3) → False

/-- Scaling by |lam| > 1 destroys primitivity of a nonzero anchored ray. -/
theorem not_primitiveAnchored_of_smul
    {x0 x4 x1 x2 x3 y4 a1 a2 a3 lam : ℤ}
    (hlam : 1 < |lam|)
    (_hne : ¬(x0 = 0 ∧ x4 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧
             y4 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0)) :
    ¬ PrimitiveAnchoredCRTRay
      (lam * x0) (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * y4) (lam * a1) (lam * a2) (lam * a3) := by
  intro hprim
  apply hprim lam hlam
  exact ⟨⟨x0, rfl⟩, ⟨x4, rfl⟩, ⟨x1, rfl⟩, ⟨x2, rfl⟩, ⟨x3, rfl⟩,
         ⟨y4, rfl⟩, ⟨a1, rfl⟩, ⟨a2, rfl⟩, ⟨a3, rfl⟩⟩

/-- If a scaled anchored ray is primitive, then |lam| ≤ 1. -/
theorem abs_lam_le_one_of_primitiveAnchored_smul
    {x0 x4 x1 x2 x3 y4 a1 a2 a3 lam : ℤ}
    (hne : ¬(x0 = 0 ∧ x4 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧
             y4 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0))
    (hprim : PrimitiveAnchoredCRTRay
      (lam * x0) (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * y4) (lam * a1) (lam * a2) (lam * a3)) :
    |lam| ≤ 1 := by
  by_contra h
  push_neg at h
  exact not_primitiveAnchored_of_smul h hne hprim

/-! ## Goal 8: Optional zero diagnostics

Uses the generic `dvd_of_latticeEq` and `xi_eq_div_of_latticeEq` from `CRTLatticeCore`. -/

/-- Divisibility from the anchor equation: q_4 ∣ p * y_4 + q_0 * x_0. -/
theorem dvd_of_anchorHit
    (V : AnchoredCRTProductHit) :
    V.q4 ∣ V.p * V.y4 + V.q0 * V.x0 :=
  dvd_of_latticeEq V.h4

/-- Projection from the anchor equation. -/
theorem x4_eq_div_of_anchor
    {q4 q0 x4 x0 p y4 : ℤ}
    (hq4 : q4 ≠ 0)
    (h4 : q4 * x4 - q0 * x0 = p * y4) :
    x4 = (p * y4 + q0 * x0) / q4 ∧ q4 ∣ (p * y4 + q0 * x0) :=
  xi_eq_div_of_latticeEq hq4 h4

/-- Divisibility from the i-th anchored equation: q_i ∣ p * a_i + q_4 * x_4. -/
theorem dvd_of_anchoredHit_1 (V : AnchoredCRTProductHit) :
    V.q1 ∣ V.p * V.a1 + V.q4 * V.x4 :=
  dvd_of_latticeEq V.h1

theorem dvd_of_anchoredHit_2 (V : AnchoredCRTProductHit) :
    V.q2 ∣ V.p * V.a2 + V.q4 * V.x4 :=
  dvd_of_latticeEq V.h2

theorem dvd_of_anchoredHit_3 (V : AnchoredCRTProductHit) :
    V.q3 ∣ V.p * V.a3 + V.q4 * V.x4 :=
  dvd_of_latticeEq V.h3

/-- Projection from the i-th anchored equation. -/
theorem xi_eq_div_of_anchoredLattice
    {qi q4 xi x4 p ai : ℤ}
    (hqi : qi ≠ 0)
    (hlat : qi * xi - q4 * x4 = p * ai) :
    xi = (p * ai + q4 * x4) / qi ∧ qi ∣ (p * ai + q4 * x4) :=
  xi_eq_div_of_latticeEq hqi hlat
