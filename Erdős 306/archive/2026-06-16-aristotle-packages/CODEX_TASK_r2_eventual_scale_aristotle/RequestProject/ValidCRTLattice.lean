/-
  ValidCRTLattice.lean

  Valid quotient hits and homogeneous lattice/ray structure
  for the Erdős 306 conditional proof.

  **⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
  This file is part of the rational-collision / CRT-lattice component,
  which is sorry-free algebra/combinatorics but is **disconnected** from
  the main theorem `erdos_306`. The top result of this component,
  `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
  assumes the shell bound as a hypothesis.

  A bare CRT product hit is only a necessary condition for a cluster witness.
  The actual cluster witness also requires the quotient variables
    x_i = (p a_i + q_4 x_4) / q_i
  to be nonzero integers. Algebraically, this means the variables lie in the
  homogeneous lattice
    q_i x_i - q_4 x_4 = p a_i   (1 ≤ i ≤ 3).

  Generic single-equation lemmas (`baseDivides_of_latticeEq`,
  `xi_eq_div_of_latticeEq`, `latticeEq_smul`, etc.) are imported from
  `CRTLatticeCore.lean` via `ReciprocalCRTProduct.lean`.
-/
import Mathlib
import RequestProject.ReciprocalCRTProduct

/-! ## Goal 1: Valid CRT hit structure -/

/-- A valid CRT product hit bundles the quotient data: four moduli, a prime,
    four short variables, and three base differences, satisfying the
    homogeneous lattice equations. -/
structure ValidCRTProductHit where
  p : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  x4 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  h1 : q1 * x1 - q4 * x4 = p * a1
  h2 : q2 * x2 - q4 * x4 = p * a2
  h3 : q3 * x3 - q4 * x4 = p * a3

/-- Predicate version of `ValidCRTProductHit`. -/
def IsValidCRTProductHit
    (p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 : ℤ) : Prop :=
  q1 * x1 - q4 * x4 = p * a1 ∧
  q2 * x2 - q4 * x4 = p * a2 ∧
  q3 * x3 - q4 * x4 = p * a3

theorem isValidCRTProductHit_of_struct (V : ValidCRTProductHit) :
    IsValidCRTProductHit V.p V.q1 V.q2 V.q3 V.q4 V.x4 V.x1 V.x2 V.x3
      V.a1 V.a2 V.a3 :=
  ⟨V.h1, V.h2, V.h3⟩

def validCRTProductHit_of_pred
    {p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 : ℤ}
    (h : IsValidCRTProductHit p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3) :
    ValidCRTProductHit where
  p := p; q1 := q1; q2 := q2; q3 := q3; q4 := q4
  x4 := x4; x1 := x1; x2 := x2; x3 := x3
  a1 := a1; a2 := a2; a3 := a3
  h1 := h.1; h2 := h.2.1; h3 := h.2.2

/-! ## Goal 2: Bridge from/to FourSeedLineWitness -/

/-- A `FourSeedLineWitness` produces a `ValidCRTProductHit` using
    the base differences `a_i = y_i - y_4`. -/
def validCRTProductHit_of_fourSeedLineWitness
    (W : FourSeedLineWitness) : ValidCRTProductHit where
  p := W.p; q1 := W.q1; q2 := W.q2; q3 := W.q3; q4 := W.q4
  x4 := W.x4; x1 := W.x1; x2 := W.x2; x3 := W.x3
  a1 := a1 W; a2 := a2 W; a3 := a3 W
  h1 := base_diff_1 W
  h2 := base_diff_2 W
  h3 := base_diff_3 W

/-- Conversely, a `ValidCRTProductHit` produces a `FourSeedLineWitness`
    by setting `y_4 = 0`, `c = q_4 x_4`, `y_i = a_i`. -/
def fourSeedLineWitness_of_validCRTProductHit
    (V : ValidCRTProductHit) : FourSeedLineWitness where
  p := V.p; c := V.q4 * V.x4
  q1 := V.q1; q2 := V.q2; q3 := V.q3; q4 := V.q4
  x1 := V.x1; x2 := V.x2; x3 := V.x3; x4 := V.x4
  y1 := V.a1; y2 := V.a2; y3 := V.a3; y4 := 0
  h1 := by linarith [V.h1]
  h2 := by linarith [V.h2]
  h3 := by linarith [V.h3]
  h4 := by ring

/-! ## Goal 3: Valid hit implies bare CRT hit under inverse witnesses -/

theorem crtProductHit_of_validCRTProductHit
    (V : ValidCRTProductHit)
    (inv1 inv2 inv3 : ℤ)
    (hInv1 : InvModWitness V.a1 V.q1 inv1)
    (hInv2 : InvModWitness V.a2 V.q2 inv2)
    (hInv3 : InvModWitness V.a3 V.q3 inv3) :
    CRTProductHit V.q1 V.q2 V.q3 V.q4 V.p V.x4
      V.a1 V.a2 V.a3 inv1 inv2 inv3 :=
  ⟨hInv1, hInv2, hInv3,
   local_residue_of_baseDivides hInv1 (baseDivides_of_latticeEq V.h1),
   local_residue_of_baseDivides hInv2 (baseDivides_of_latticeEq V.h2),
   local_residue_of_baseDivides hInv3 (baseDivides_of_latticeEq V.h3)⟩

/-! ## Goal 4: Homogeneous lattice predicate -/

/-- The homogeneous CRT lattice: `q_i x_i - q_4 x_4 = p a_i` for `i = 1,2,3`. -/
def InCRTLattice
    (p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 : ℤ) : Prop :=
  q1 * x1 - q4 * x4 = p * a1 ∧
  q2 * x2 - q4 * x4 = p * a2 ∧
  q3 * x3 - q4 * x4 = p * a3

theorem inCRTLattice_of_validCRTProductHit (V : ValidCRTProductHit) :
    InCRTLattice V.p V.q1 V.q2 V.q3 V.q4 V.x4 V.x1 V.x2 V.x3
      V.a1 V.a2 V.a3 :=
  ⟨V.h1, V.h2, V.h3⟩

def validCRTProductHit_of_inCRTLattice
    {p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 : ℤ}
    (h : InCRTLattice p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3) :
    ValidCRTProductHit where
  p := p; q1 := q1; q2 := q2; q3 := q3; q4 := q4
  x4 := x4; x1 := x1; x2 := x2; x3 := x3
  a1 := a1; a2 := a2; a3 := a3
  h1 := h.1; h2 := h.2.1; h3 := h.2.2

/-! ## Goal 5: Scaling/ray property

Uses the generic `latticeEq_smul` from `CRTLatticeCore`. -/

theorem inCRTLattice_smul
    {p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3 lam : ℤ}
    (h : InCRTLattice p q1 q2 q3 q4 x4 x1 x2 x3 a1 a2 a3) :
    InCRTLattice p q1 q2 q3 q4
      (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * a1) (lam * a2) (lam * a3) :=
  ⟨latticeEq_smul h.1, latticeEq_smul h.2.1, latticeEq_smul h.2.2⟩

/-- Scaling a `ValidCRTProductHit` by `lam` produces a new valid hit. -/
def validCRTProductHit_smul (V : ValidCRTProductHit) (lam : ℤ) :
    ValidCRTProductHit where
  p := V.p; q1 := V.q1; q2 := V.q2; q3 := V.q3; q4 := V.q4
  x4 := lam * V.x4; x1 := lam * V.x1; x2 := lam * V.x2; x3 := lam * V.x3
  a1 := lam * V.a1; a2 := lam * V.a2; a3 := lam * V.a3
  h1 := latticeEq_smul V.h1
  h2 := latticeEq_smul V.h2
  h3 := latticeEq_smul V.h3

/-! ## Goal 6: Zero-coordinate diagnostics

Uses the generic `dvd_of_latticeEq` and `xi_eq_div_of_latticeEq` from `CRTLatticeCore`. -/

/-- Divisibility: `q_i ∣ p * a_i + q_4 * x_4` from a valid hit. -/
theorem dvd_of_validHit_1 (V : ValidCRTProductHit) :
    V.q1 ∣ V.p * V.a1 + V.q4 * V.x4 :=
  dvd_of_latticeEq V.h1

theorem dvd_of_validHit_2 (V : ValidCRTProductHit) :
    V.q2 ∣ V.p * V.a2 + V.q4 * V.x4 :=
  dvd_of_latticeEq V.h2

theorem dvd_of_validHit_3 (V : ValidCRTProductHit) :
    V.q3 ∣ V.p * V.a3 + V.q4 * V.x4 :=
  dvd_of_latticeEq V.h3

/-- If `p = q4`, `a_i = -x4`, and `q_i ≠ 0`, then `x_i = 0`. -/
theorem xi_eq_zero_of_p_eq_q4
    {p q1 q4 x1 x4 a1 : ℤ}
    (hq1_ne : q1 ≠ 0)
    (hp : p = q4)
    (ha : a1 = -x4)
    (hlat : q1 * x1 - q4 * x4 = p * a1) :
    x1 = 0 :=
  x_eq_zero_of_latticeEq_special hq1_ne hp ha hlat

/-- General projection: `x_i` is determined by the lattice equation, and
    `q_i ∣ p * a_i + q_4 * x_4`. -/
theorem xi_eq_div_of_lattice
    {qi q4 xi x4 p ai : ℤ}
    (hqi : qi ≠ 0)
    (hlat : qi * xi - q4 * x4 = p * ai) :
    xi = (p * ai + q4 * x4) / qi ∧ qi ∣ (p * ai + q4 * x4) :=
  xi_eq_div_of_latticeEq hqi hlat

/-! ## Goal 7: Primitive-ray predicate (optional) -/

/-- A CRT ray is primitive if no integer with `|d| > 1` divides all seven
    short coordinates simultaneously. -/
def PrimitiveCRTRay (x4 x1 x2 x3 a1 a2 a3 : ℤ) : Prop :=
  ∀ d : ℤ, 1 < |d| →
    (d ∣ x4 ∧ d ∣ x1 ∧ d ∣ x2 ∧ d ∣ x3 ∧
     d ∣ a1 ∧ d ∣ a2 ∧ d ∣ a3) → False

/-- Scaling by `|lam| > 1` makes a nonzero ray non-primitive. -/
theorem not_primitive_of_smul
    {x4 x1 x2 x3 a1 a2 a3 lam : ℤ}
    (hlam : 1 < |lam|)
    (_hne : ¬(x4 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧
             a1 = 0 ∧ a2 = 0 ∧ a3 = 0)) :
    ¬ PrimitiveCRTRay (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * a1) (lam * a2) (lam * a3) := by
  intro hprim
  apply hprim lam hlam
  exact ⟨⟨x4, rfl⟩, ⟨x1, rfl⟩, ⟨x2, rfl⟩, ⟨x3, rfl⟩,
         ⟨a1, rfl⟩, ⟨a2, rfl⟩, ⟨a3, rfl⟩⟩

/-- If a primitive ray is scaled and remains primitive, then `|lam| ≤ 1`. -/
theorem abs_lam_le_one_of_primitive_smul
    {x4 x1 x2 x3 a1 a2 a3 lam : ℤ}
    (hne : ¬(x4 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧
             a1 = 0 ∧ a2 = 0 ∧ a3 = 0))
    (hprim : PrimitiveCRTRay (lam * x4) (lam * x1) (lam * x2) (lam * x3)
      (lam * a1) (lam * a2) (lam * a3)) :
    |lam| ≤ 1 := by
  by_contra h
  push_neg at h
  exact not_primitive_of_smul h hne hprim
