/-
  ReciprocalCRTProduct.lean

  Algebraic reduction: four seed points on one reciprocal-cluster line
  imply CRT product congruences for p.

  Part of the Erdős 306 conditional proof formalization.

  **⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
  This file is part of the rational-collision / CRT-lattice component,
  which is sorry-free algebra/combinatorics but is **disconnected** from
  the main theorem `erdos_306`. The top result of this component,
  `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
  assumes the shell bound as a hypothesis.

  Core definitions (`BaseDivides`, `InvModWitness`, `local_residue_of_baseDivides`,
  `modEq_of_baseDivides`) and generic single-equation lemmas are in
  `CRTLatticeCore.lean`. This file re-exports them transitively.
-/
import Mathlib
import RequestProject.ClusterLineIncidence
import RequestProject.CRTLatticeCore

/-! ## Goal 1: Four-seed line witness and base differences -/

structure FourSeedLineWitness where
  p : ℤ
  c : ℤ
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  x1 : ℤ
  x2 : ℤ
  x3 : ℤ
  x4 : ℤ
  y1 : ℤ
  y2 : ℤ
  y3 : ℤ
  y4 : ℤ
  h1 : q1 * x1 = p * y1 + c
  h2 : q2 * x2 = p * y2 + c
  h3 : q3 * x3 = p * y3 + c
  h4 : q4 * x4 = p * y4 + c

def a1 (W : FourSeedLineWitness) : ℤ := W.y1 - W.y4
def a2 (W : FourSeedLineWitness) : ℤ := W.y2 - W.y4
def a3 (W : FourSeedLineWitness) : ℤ := W.y3 - W.y4

theorem base_diff_1 (W : FourSeedLineWitness) :
    W.q1 * W.x1 - W.q4 * W.x4 = W.p * a1 W := by
  unfold a1; linarith [W.h1, W.h4]

theorem base_diff_2 (W : FourSeedLineWitness) :
    W.q2 * W.x2 - W.q4 * W.x4 = W.p * a2 W := by
  unfold a2; linarith [W.h2, W.h4]

theorem base_diff_3 (W : FourSeedLineWitness) :
    W.q3 * W.x3 - W.q4 * W.x4 = W.p * a3 W := by
  unfold a3; linarith [W.h3, W.h4]

/-! ## Goal 2: Divisibility and modular forms

Core definitions `BaseDivides`, `InvModWitness`, `modEq_of_baseDivides`,
`local_residue_of_baseDivides` are imported from `CRTLatticeCore.lean`. -/

theorem baseDivides_1 (W : FourSeedLineWitness) :
    BaseDivides W.q1 W.p (a1 W) W.q4 W.x4 :=
  baseDivides_of_latticeEq (base_diff_1 W)

theorem baseDivides_2 (W : FourSeedLineWitness) :
    BaseDivides W.q2 W.p (a2 W) W.q4 W.x4 :=
  baseDivides_of_latticeEq (base_diff_2 W)

theorem baseDivides_3 (W : FourSeedLineWitness) :
    BaseDivides W.q3 W.p (a3 W) W.q4 W.x4 :=
  baseDivides_of_latticeEq (base_diff_3 W)

theorem modEq_1 (W : FourSeedLineWitness) :
    (W.p * a1 W + W.q4 * W.x4) ≡ 0 [ZMOD W.q1] :=
  modEq_of_baseDivides (baseDivides_1 W)

theorem modEq_2 (W : FourSeedLineWitness) :
    (W.p * a2 W + W.q4 * W.x4) ≡ 0 [ZMOD W.q2] :=
  modEq_of_baseDivides (baseDivides_2 W)

theorem modEq_3 (W : FourSeedLineWitness) :
    (W.p * a3 W + W.q4 * W.x4) ≡ 0 [ZMOD W.q3] :=
  modEq_of_baseDivides (baseDivides_3 W)

/-! ## Goal 3: Three local CRT congruences from a four-seed witness -/

structure ThreeLocalCRTResidues where
  q1 : ℤ
  q2 : ℤ
  q3 : ℤ
  q4 : ℤ
  p : ℤ
  x4 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  inv1 : ℤ
  inv2 : ℤ
  inv3 : ℤ
  hInv1 : InvModWitness a1 q1 inv1
  hInv2 : InvModWitness a2 q2 inv2
  hInv3 : InvModWitness a3 q3 inv3
  hRes1 : p ≡ x4 * (-q4 * inv1) [ZMOD q1]
  hRes2 : p ≡ x4 * (-q4 * inv2) [ZMOD q2]
  hRes3 : p ≡ x4 * (-q4 * inv3) [ZMOD q3]

noncomputable def threeLocalCRTResidues_of_fourSeedLineWitness
    (W : FourSeedLineWitness)
    (inv1 inv2 inv3 : ℤ)
    (hInv1 : InvModWitness (a1 W) W.q1 inv1)
    (hInv2 : InvModWitness (a2 W) W.q2 inv2)
    (hInv3 : InvModWitness (a3 W) W.q3 inv3) :
    ThreeLocalCRTResidues where
  q1 := W.q1
  q2 := W.q2
  q3 := W.q3
  q4 := W.q4
  p := W.p
  x4 := W.x4
  a1 := a1 W
  a2 := a2 W
  a3 := a3 W
  inv1 := inv1
  inv2 := inv2
  inv3 := inv3
  hInv1 := hInv1
  hInv2 := hInv2
  hInv3 := hInv3
  hRes1 := local_residue_of_baseDivides hInv1 (baseDivides_1 W)
  hRes2 := local_residue_of_baseDivides hInv2 (baseDivides_2 W)
  hRes3 := local_residue_of_baseDivides hInv3 (baseDivides_3 W)

/-! ## Goal 4: Product-set language -/

def CRTProductHit
    (q1 q2 q3 q4 p x a1 a2 a3 inv1 inv2 inv3 : ℤ) : Prop :=
  InvModWitness a1 q1 inv1 ∧
  InvModWitness a2 q2 inv2 ∧
  InvModWitness a3 q3 inv3 ∧
  p ≡ x * (-q4 * inv1) [ZMOD q1] ∧
  p ≡ x * (-q4 * inv2) [ZMOD q2] ∧
  p ≡ x * (-q4 * inv3) [ZMOD q3]

theorem crtProductHit_of_fourSeedLineWitness
    (W : FourSeedLineWitness)
    (inv1 inv2 inv3 : ℤ)
    (hInv1 : InvModWitness (a1 W) W.q1 inv1)
    (hInv2 : InvModWitness (a2 W) W.q2 inv2)
    (hInv3 : InvModWitness (a3 W) W.q3 inv3) :
    CRTProductHit W.q1 W.q2 W.q3 W.q4 W.p W.x4
      (a1 W) (a2 W) (a3 W) inv1 inv2 inv3 :=
  ⟨hInv1, hInv2, hInv3,
   local_residue_of_baseDivides hInv1 (baseDivides_1 W),
   local_residue_of_baseDivides hInv2 (baseDivides_2 W),
   local_residue_of_baseDivides hInv3 (baseDivides_3 W)⟩
