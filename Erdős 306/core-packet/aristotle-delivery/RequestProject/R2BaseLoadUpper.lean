import RequestProject.R2ComponentDisjoint

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 base-load upper socket

This leaf isolates the remaining base-load upper condition into separate
control and gadget reciprocal-load budgets.
-/

/-- If every gadget denominator prime lies outside the block support, the fixed
base load splits exactly into control and gadget reciprocal loads. -/
theorem baseLoad_eq_ctrl_add_gadget_of_R_outside
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS) :
    D.baseLoad =
      R2ConcreteData.recipLoad (ctrlEdges D.BS) +
        R2ConcreteData.recipLoad (gadgetEdges D.R D.S) := by
  exact baseLoad_eq_ctrl_add_gadget_of_disjoint D
    (r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport D hRprime hRout)

/-- Separate control/gadget budgets for the R2 base-load upper condition. -/
structure R2BaseLoadBudget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) where
  Cctrl : ℝ
  Cgadget : ℝ
  hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl
  hgadget : R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget
  hsum : Cctrl + Cgadget < 3 / (2 * (b : ℝ))

/-- Component budgets imply the requested strict base-load upper bound. -/
theorem baseLoad_lt_of_budget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS)
    (B : R2BaseLoadBudget D) :
    D.baseLoad < 3 / (2 * (b : ℝ)) := by
  rw [baseLoad_eq_ctrl_add_gadget_of_R_outside D hRprime hRout]
  exact lt_of_le_of_lt (add_le_add B.hctrl B.hgadget) B.hsum

/-- Analytic socket: the dyadic reciprocal estimate needed to make the control
load eventually small.  Existing dyadic inputs are lower bounds and do not imply
this upper bound. -/
axiom dyadic_control_recipLoad_eventually_small :
  ∀ ε : ℝ, 0 < ε →
    ∃ k0min : ℕ, ∀ BS : BlockSystem, k0min ≤ BS.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS) ≤ ε

/-- Construction-facing wrapper for the dyadic control-load input. -/
theorem exists_k0_controlLoad_lt
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k0min : ℕ, ∀ BS : BlockSystem, k0min ≤ BS.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS) ≤ ε :=
  dyadic_control_recipLoad_eventually_small ε hε

end CircleMethod

