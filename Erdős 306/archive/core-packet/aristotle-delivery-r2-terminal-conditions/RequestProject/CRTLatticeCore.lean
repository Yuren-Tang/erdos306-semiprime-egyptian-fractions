/-
  CRTLatticeCore.lean

  Generic single-equation utilities for CRT lattice computations.

  **⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
  This file is part of the rational-collision / CRT-lattice component,
  which is sorry-free algebra/combinatorics but is **disconnected** from
  the main theorem `erdos_306`. The top result of this component,
  `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
  assumes the shell bound as a hypothesis.

  All three CRT-lattice files (`ReciprocalCRTProduct`, `ValidCRTLattice`,
  `AnchoredCRTLattice`) share the same single-equation pattern:

      q * x - q' * x' = p * a

  From this equation one derives:
  1. Divisibility:  q ∣ (p * a + q' * x')
  2. Modular form:  with an inverse witness for a, p ≡ x * (-q' * ainv) [ZMOD q]
  3. Scaling:       the equation is preserved under uniform scaling by λ
  4. Projection:    x = (p * a + q' * x') / q  when q ≠ 0

  This file collects these generic lemmas so that the three CRT-lattice files
  can instantiate them rather than re-deriving each one.
-/
import Mathlib

/-! ## Core definitions -/

/-- `BaseDivides q p a q' x'` means `q ∣ (p * a + q' * x')`. -/
def BaseDivides (q p a q' x' : ℤ) : Prop :=
  q ∣ p * a + q' * x'

/-- `InvModWitness a q ainv` means `a * ainv ≡ 1 [ZMOD q]`. -/
def InvModWitness (a q ainv : ℤ) : Prop :=
  a * ainv ≡ 1 [ZMOD q]

/-! ## Single-equation derived lemmas -/

/-- From a lattice equation `q * x - q' * x' = p * a`, derive `BaseDivides q p a q' x'`. -/
theorem baseDivides_of_latticeEq {q x p a q' x' : ℤ}
    (h : q * x - q' * x' = p * a) : BaseDivides q p a q' x' :=
  ⟨x, by linarith⟩

/-- From a lattice equation, derive divisibility: `q ∣ (p * a + q' * x')`. -/
theorem dvd_of_latticeEq {q x p a q' x' : ℤ}
    (h : q * x - q' * x' = p * a) : q ∣ p * a + q' * x' :=
  ⟨x, by linarith⟩

/-- From a lattice equation and an inverse witness, derive the local CRT congruence:
    `p ≡ x * (-q' * ainv) [ZMOD q]`. -/
theorem local_residue_of_baseDivides
    {q p a q' x ainv : ℤ}
    (hinv : InvModWitness a q ainv)
    (hdiv : BaseDivides q p a q' x) :
    p ≡ x * (-q' * ainv) [ZMOD q] := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨k, hk⟩ := hdiv
  obtain ⟨m, hm⟩ := hinv.symm.dvd
  exact ⟨-k * ainv + m * p, by linear_combination -hk * ainv + hm * p⟩

/-- Scaling preserves a single lattice equation. -/
theorem latticeEq_smul {q x p a q' x' lam : ℤ}
    (h : q * x - q' * x' = p * a) :
    q * (lam * x) - q' * (lam * x') = p * (lam * a) := by
  linear_combination lam * h

/-- Projection from a lattice equation when q ≠ 0:
    x = (p * a + q' * x') / q  and  q ∣ (p * a + q' * x'). -/
theorem xi_eq_div_of_latticeEq
    {q q' x x' p a : ℤ}
    (hq : q ≠ 0)
    (hlat : q * x - q' * x' = p * a) :
    x = (p * a + q' * x') / q ∧ q ∣ (p * a + q' * x') := by
  constructor
  · have : p * a + q' * x' = q * x := by linarith
    rw [this, Int.mul_ediv_cancel_left _ hq]
  · exact ⟨x, by linarith⟩

/-- If `p = q'`, `a = -x'`, and `q ≠ 0`, then `x = 0`. -/
theorem x_eq_zero_of_latticeEq_special
    {q q' x x' p a : ℤ}
    (hq : q ≠ 0) (hp : p = q') (ha : a = -x')
    (hlat : q * x - q' * x' = p * a) :
    x = 0 := by
  have : q * x = 0 := by subst hp; subst ha; linarith
  exact (mul_eq_zero.mp this).resolve_left hq

/-- Modular form of `BaseDivides`: `(p * a + q' * x') ≡ 0 [ZMOD q]`. -/
theorem modEq_of_baseDivides {q p a q' x' : ℤ}
    (h : BaseDivides q p a q' x') :
    (p * a + q' * x') ≡ 0 [ZMOD q] :=
  Int.modEq_zero_iff_dvd.mpr h
