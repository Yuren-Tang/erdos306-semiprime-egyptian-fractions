import RequestProject.R2MinorSupportBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor budget numerics

This leaf isolates the final scalar budget comparison used by the R2 minor
lane.  The analytic lanes naturally produce estimates of the form
`Ablock / sigmaCtrl` and `Aextra / sigmaCtrl`; the final assembly socket wants
their sum to be strictly below the main-term constant divided by `sigmaCtrl`.
-/

/-- The main-term control constant appearing in the R2 final sockets. -/
def r2MinorMainCtrlConstant : ℝ :=
  0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)

/-- Generic scalar budget gate. -/
lemma add_lt_div_of_add_scaled_lt
    {σ Bblock Bextra Ablock Aextra c : ℝ}
    (hσ : 0 < σ)
    (hblock : Bblock ≤ Ablock / σ)
    (hextra : Bextra ≤ Aextra / σ)
    (hscaled : Ablock + Aextra < c) :
    Bblock + Bextra < c / σ := by
  have hsum : Bblock + Bextra ≤ Ablock / σ + Aextra / σ :=
    add_le_add hblock hextra
  have hcollapse : Ablock / σ + Aextra / σ = (Ablock + Aextra) / σ := by
    ring
  rw [hcollapse] at hsum
  exact lt_of_le_of_lt hsum (div_lt_div_of_pos_right hscaled hσ)

/-- R2-shaped scalar budget gate at `sigmaCtrl D.BS`. -/
lemma r2_minor_ctrl_from_scaled_budgets
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (Bblock Bextra Ablock Aextra : ℝ)
    (hσ : 0 < sigmaCtrl D.BS)
    (hblock : Bblock ≤ Ablock / sigmaCtrl D.BS)
    (hextra : Bextra ≤ Aextra / sigmaCtrl D.BS)
    (hscaled : Ablock + Aextra < r2MinorMainCtrlConstant) :
    Bblock + Bextra <
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS := by
  simpa [r2MinorMainCtrlConstant] using
    add_lt_div_of_add_scaled_lt (σ := sigmaCtrl D.BS)
      (Bblock := Bblock) (Bextra := Bextra)
      (Ablock := Ablock) (Aextra := Aextra)
      (c := r2MinorMainCtrlConstant) hσ hblock hextra hscaled

/-- Same scalar gate, using admissibility to obtain `sigmaCtrl > 0`. -/
lemma r2_minor_ctrl_from_scaled_budgets_admissible
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (Bblock Bextra Ablock Aextra : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hblock : Bblock ≤ Ablock / sigmaCtrl D.BS)
    (hextra : Bextra ≤ Aextra / sigmaCtrl D.BS)
    (hscaled : Ablock + Aextra < r2MinorMainCtrlConstant) :
    Bblock + Bextra <
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS :=
  r2_minor_ctrl_from_scaled_budgets D Bblock Bextra Ablock Aextra
    (sigmaCtrl_pos D.BS hadm) hblock hextra hscaled

/-- A convenient form for the G7 block budget plus an extra-minor budget. -/
lemma r2_minor_ctrl_from_g7_block_and_extra
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (Bblock Bextra K η Ctail C Aextra : ℝ)
    (hσ : 0 < sigmaCtrl D.BS)
    (hblock :
      Bblock ≤
        K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) /
          sigmaCtrl D.BS)
    (hextra : Bextra ≤ Aextra / sigmaCtrl D.BS)
    (hscaled :
      K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) + Aextra
        < r2MinorMainCtrlConstant) :
    Bblock + Bextra <
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS := by
  refine r2_minor_ctrl_from_scaled_budgets D Bblock Bextra
    (K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2))) Aextra hσ ?_ hextra
    hscaled
  simpa [mul_div_assoc] using hblock

/-- G7 block plus extra budget, with `sigmaCtrl > 0` supplied by admissibility. -/
lemma r2_minor_ctrl_from_g7_block_and_extra_admissible
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (Bblock Bextra K η Ctail C Aextra : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hblock :
      Bblock ≤
        K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) /
          sigmaCtrl D.BS)
    (hextra : Bextra ≤ Aextra / sigmaCtrl D.BS)
    (hscaled :
      K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) + Aextra
        < r2MinorMainCtrlConstant) :
    Bblock + Bextra <
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS :=
  r2_minor_ctrl_from_g7_block_and_extra D Bblock Bextra K η Ctail C Aextra
    (sigmaCtrl_pos D.BS hadm) hblock hextra hscaled

/-- **K=501 budget gate (pure scalar, no `D` — avoids `isDefEq` blow-up).**
With each of the three component budgets below `c3/2004` (the `A1` term exactly,
`A2` strictly, and the σ-scaled `A3` term), the combined minor budget
`Bm = (A1 + A2)/σ + A3` lies strictly below `c3/(501 σ)`.  Used to discharge the
loose-σ beat (`√σ_E ≤ 501 σ`) without the tight `≤ 3σ²` extra-mass bound. -/
lemma r2_close_budget_501 (σ A1 A2 A3 c3 : ℝ)
    (hσpos : 0 < σ) (hc3pos : 0 < c3)
    (h1 : A1 = c3 / 2004) (h2 : A2 < c3 / 2004) (h3 : A3 * σ ≤ c3 / 2004) :
    (A1 + A2) / σ + A3 < c3 / (501 * σ) := by
  have hσ501 : (0 : ℝ) < 501 * σ := by positivity
  rw [div_add' _ _ _ (ne_of_gt hσpos), div_lt_div_iff₀ hσpos hσ501]
  nlinarith [h1, h2, h3, hσpos, hc3pos, mul_pos hσpos hc3pos]

end CircleMethod

end
