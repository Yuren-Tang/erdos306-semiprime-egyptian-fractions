import RequestProject.R2MinorSupportBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor support pipeline

This file fixes the downstream interface from a classification lane plus two
independent analytic budget lanes to `R2MinorSupportBudgetData`.
-/

/-- Direct constructor for the packaged R2 minor support/budget record. -/
def r2_minorSupportBudget_of_lanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (Bblock Bextra : ℝ)
    (Sblock Sextra :
      MainArcFields D.E W.theta b D.L N → Finset ℕ)
    (hcover : ∀ MA : MainArcFields D.E W.theta b D.L N,
      MA.Sm ⊆ Sblock MA ∪ Sextra MA)
    (hblock : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
        fourierNormWeight D.E W.theta b D.L h ≤ Bblock)
    (hextra : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
        fourierNormWeight D.E W.theta b D.L h ≤ Bextra) :
    R2MinorSupportBudgetData D W N Bblock Bextra where
  Sblock := Sblock
  Sextra := Sextra
  hcover := hcover
  hblock := hblock
  hextra := hextra

/-- Classification lane: a choice of block/extra support sets covering every
minor frequency set supplied by `MainArcFields`. -/
structure R2MinorClassificationData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) where
  Sblock : MainArcFields D.E W.theta b D.L N → Finset ℕ
  Sextra : MainArcFields D.E W.theta b D.L N → Finset ℕ
  hcover : ∀ MA : MainArcFields D.E W.theta b D.L N,
    MA.Sm ⊆ Sblock MA ∪ Sextra MA

/-- Analytic budget lanes for a fixed classification. -/
structure R2MinorBudgetLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C : R2MinorClassificationData D W N)
    (Bblock Bextra : ℝ) where
  hblock : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∑ h ∈ blockMinorPart MA.Sm (C.Sblock MA),
      fourierNormWeight D.E W.theta b D.L h ≤ Bblock
  hextra : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∑ h ∈ extraMinorPart MA.Sm (C.Sblock MA) (C.Sextra MA),
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra

/-- Assemble the support-budget record from an independent classification lane
and analytic budget lanes. -/
def r2_minorSupportBudget_of_classification_and_budgetLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (Bblock Bextra : ℝ)
    (C : R2MinorClassificationData D W N)
    (L : R2MinorBudgetLanes D W N C Bblock Bextra) :
    R2MinorSupportBudgetData D W N Bblock Bextra :=
  r2_minorSupportBudget_of_lanes D W N Bblock Bextra
    C.Sblock C.Sextra C.hcover L.hblock L.hextra

/-- Sanity classification: put every minor frequency into the block lane. -/
def trivialMinorClassificationData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) :
    R2MinorClassificationData D W N where
  Sblock := fun MA => MA.Sm
  Sextra := fun _ => ∅
  hcover := by
    intro MA h hh
    exact Finset.mem_union_left _ hh

end CircleMethod

end
