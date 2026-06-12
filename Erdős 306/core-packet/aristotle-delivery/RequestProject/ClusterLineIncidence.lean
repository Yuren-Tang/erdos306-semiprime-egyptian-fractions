/-
# ClusterLineIncidence

Algebraic bridge from reciprocal-cluster congruences to integer line incidence
and determinant relations.

**⚠️ Route-exploration file — NOT on the critical path of `erdos_306`.**
This file is part of the rational-collision / CRT-lattice component,
which is sorry-free algebra/combinatorics but is **disconnected** from
the main theorem `erdos_306`. The top result of this component,
`ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound`,
assumes the shell bound as a hypothesis.

Paper-side meaning:
  reciprocal cluster through several seeds ⟹ short factorable collinearity relations.

No number theory, primality, or asymptotics are used.
-/
import Mathlib
import RequestProject.AdaptiveClusterSelection

open Int

/-! ## Goal 1: Line incidence predicate -/

/-- Point `(y,z)` lies on the line with slope `p` and intercept `c`. -/
def LiesOnLine (p c y z : Int) : Prop :=
  z = p * y + c

/-- `(y,z)` is a seed point for prime/parameter `q` with bound `M`:
    there exists a nonzero integer `x` with `|x| ≤ M`, `|y| ≤ M`, and `z = q * x`. -/
def SeedPoint (q M y z : Int) : Prop :=
  ∃ x : Int, x ≠ 0 ∧ x.natAbs ≤ M.natAbs ∧ y.natAbs ≤ M.natAbs ∧ z = q * x

/-! ## Goal 2: Congruence-to-line identity -/

/-- If `q * x = p * y + c`, then `(y, q*x)` lies on line `(p, c)`. -/
theorem liesOnLine_of_seed_eq {q x p y c : Int} (h : q * x = p * y + c) :
    LiesOnLine p c y (q * x) := by
  exact h

/-- Converse in the seed-point setting: if `(y,z)` is a seed point for `q` and lies on
    line `(p,c)`, then there exists `x` with `z = q * x` and `q * x = p * y + c`. -/
theorem seed_on_line_witness {q M p c y z : Int}
    (hs : SeedPoint q M y z) (hl : LiesOnLine p c y z) :
    ∃ x : Int, z = q * x ∧ q * x = p * y + c := by
  obtain ⟨x, _, _, _, hzq⟩ := hs
  exact ⟨x, hzq, hzq ▸ hl⟩

/-! ## Goal 3: Three-point collinearity determinant -/

/-- The three-point determinant (twice the signed area). -/
def det3 (y1 z1 y2 z2 y3 z3 : Int) : Int :=
  z1 * (y2 - y3) + z2 * (y3 - y1) + z3 * (y1 - y2)

/-- Three points on the same line have zero determinant. -/
theorem det3_eq_zero_of_same_line
    {p c y1 z1 y2 z2 y3 z3 : Int}
    (h1 : LiesOnLine p c y1 z1)
    (h2 : LiesOnLine p c y2 z2)
    (h3 : LiesOnLine p c y3 z3) :
    det3 y1 z1 y2 z2 y3 z3 = 0 := by
  unfold det3 LiesOnLine at *
  subst h1; subst h2; subst h3
  ring

/-- If three seed points satisfy the line equations `qᵢ * xᵢ = p * yᵢ + c`,
    then the collinearity relation holds. -/
theorem factorable_relation_of_three_seedpoints_on_line
    {p c q1 q2 q3 x1 x2 x3 y1 y2 y3 : Int}
    (h1 : q1 * x1 = p * y1 + c)
    (h2 : q2 * x2 = p * y2 + c)
    (h3 : q3 * x3 = p * y3 + c) :
    q1 * x1 * (y2 - y3)
      + q2 * x2 * (y3 - y1)
      + q3 * x3 * (y1 - y2) = 0 := by
  have := det3_eq_zero_of_same_line
    (liesOnLine_of_seed_eq h1)
    (liesOnLine_of_seed_eq h2)
    (liesOnLine_of_seed_eq h3)
  unfold det3 at this
  linarith

/-! ## Goal 4: Four-point slope equality -/

/-- Four points on the same line satisfy the cross-multiplication relation. -/
theorem four_point_factorable_relation_of_same_line
    {p c q1 q2 q3 q4 x1 x2 x3 x4 y1 y2 y3 y4 : Int}
    (h1 : q1 * x1 = p * y1 + c)
    (h2 : q2 * x2 = p * y2 + c)
    (h3 : q3 * x3 = p * y3 + c)
    (h4 : q4 * x4 = p * y4 + c) :
    (q1 * x1 - q2 * x2) * (y3 - y4)
      = (q3 * x3 - q4 * x4) * (y1 - y2) := by
  -- From the hypotheses: q1*x1 - q2*x2 = p*(y1 - y2) and q3*x3 - q4*x4 = p*(y3 - y4)
  have e12 : q1 * x1 - q2 * x2 = p * (y1 - y2) := by linarith
  have e34 : q3 * x3 - q4 * x4 = p * (y3 - y4) := by linarith
  rw [e12, e34]; ring

/-! ## Goal 5: Paper-language aliases -/

/-- Three seed points lying on a common line. -/
structure SameLineSeedTriple (p c q1 q2 q3 x1 x2 x3 y1 y2 y3 : Int) : Prop where
  on_line1 : q1 * x1 = p * y1 + c
  on_line2 : q2 * x2 = p * y2 + c
  on_line3 : q3 * x3 = p * y3 + c

/-- The factorable three-point collinearity relation. -/
def FactorableThreeRelation (q1 q2 q3 x1 x2 x3 y1 y2 y3 : Int) : Prop :=
  q1 * x1 * (y2 - y3) + q2 * x2 * (y3 - y1) + q3 * x3 * (y1 - y2) = 0

/-- The factorable four-point cross-multiplication relation. -/
def FactorableFourRelation (q1 q2 q3 q4 x1 x2 x3 x4 y1 y2 y3 y4 : Int) : Prop :=
  (q1 * x1 - q2 * x2) * (y3 - y4) = (q3 * x3 - q4 * x4) * (y1 - y2)

/-- Bridge: `SameLineSeedTriple` implies `FactorableThreeRelation`. -/
theorem factorableThreeRelation_of_sameLineSeedTriple
    {p c q1 q2 q3 x1 x2 x3 y1 y2 y3 : Int}
    (h : SameLineSeedTriple p c q1 q2 q3 x1 x2 x3 y1 y2 y3) :
    FactorableThreeRelation q1 q2 q3 x1 x2 x3 y1 y2 y3 :=
  factorable_relation_of_three_seedpoints_on_line h.on_line1 h.on_line2 h.on_line3

/-- Bridge: four seed points on a common line implies `FactorableFourRelation`. -/
theorem factorableFourRelation_of_same_line
    {p c q1 q2 q3 q4 x1 x2 x3 x4 y1 y2 y3 y4 : Int}
    (h1 : q1 * x1 = p * y1 + c)
    (h2 : q2 * x2 = p * y2 + c)
    (h3 : q3 * x3 = p * y3 + c)
    (h4 : q4 * x4 = p * y4 + c) :
    FactorableFourRelation q1 q2 q3 q4 x1 x2 x3 x4 y1 y2 y3 y4 :=
  four_point_factorable_relation_of_same_line h1 h2 h3 h4
