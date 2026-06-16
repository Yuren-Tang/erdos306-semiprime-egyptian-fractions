import RequestProject.R2MinorCover
import RequestProject.R2AssemblyFields

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor lane

This leaf turns per-frequency gadget sibling witnesses into an extra-minor
norm-sum budget.  It is the extra-minor half of the data needed to build a
`R2MinorSupportBudgetData`.

The mathematical content is entirely supplied by two already-proved results:

* `CircleMethod.gadget_charFun_damp` — the per-gadget sibling damping factor
  (`‖bernoulliCharFun θ (h/(r·s))‖ ≤ √(1 − (8/9)/r²)`);
* `CircleMethod.extra_part_bound` — its sum over the disjointized extra-minor
  part (`∑ ‖bernoulliCharFun …‖ ≤ card • D`).

This file adds the *bridge* step (`hfactor`): from the actual Fourier summand
weight `fourierNormWeight` to the chosen gadget Bernoulli factor, plus the final
cardinality/budget conversion `card · D ≤ Bextra`.

The abstract version `r2_extra_minor_budget_from_gadget_witnesses_abstract`
keeps the per-frequency angle `θextra` free; the concrete version
`r2_extra_minor_budget_from_gadget_witnesses` instantiates it as
`fun h => W.theta (rfun h * sfun h)`, matching the requested shape.
-/

/-- **Abstract extra-minor budget.**  With a free per-frequency angle
`θextra : ℕ → ℝ`, per-frequency gadget sibling witnesses
(`rfun`, `sfun`, `mfun`) and the bridge `hfactor` from the Fourier summand norm
to the gadget Bernoulli factor, the extra-minor norm-sum is bounded by
`Bextra`. -/
theorem r2_extra_minor_budget_from_gadget_witnesses_abstract
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra Dmp : ℝ)
    (rfun sfun : ℕ → ℕ)
    (θextra : ℕ → ℝ)
    (mfun : ℕ → ℤ)
    (hr : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (rfun h))
    (hs : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (sfun h))
    (hrs : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ≠ sfun h)
    (hθlb : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, 1 / 3 ≤ θextra h)
    (hθub : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, θextra h ≤ 2 / 3)
    (hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (sfun h)) = (mfun h : ZMod (sfun h)))
    (hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h)))
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      2 * |mfun h| < (sfun h : ℤ))
    (hDmp : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      Real.sqrt (1 - (8 / 9) / (rfun h : ℝ) ^ 2) ≤ Dmp)
    (hfactor : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h
        ≤ ‖bernoulliCharFun (θextra h) ((h : ℝ) / ((rfun h : ℝ) * (sfun h : ℝ)))‖)
    (hbudget : ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * Dmp ≤ Bextra) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra := by
  classical
  calc ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
          fourierNormWeight D.E W.theta b D.L h
      ≤ ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
          ‖bernoulliCharFun (θextra h)
            ((h : ℝ) / ((rfun h : ℝ) * (sfun h : ℝ)))‖ :=
        Finset.sum_le_sum hfactor
    _ ≤ (extraMinorPart MA.Sm Sblock Sextra).card • Dmp :=
        extra_part_bound MA.Sm Sblock Sextra rfun sfun θextra mfun Dmp
          hr hs hrs hθlb hθub hm_s hm_r hm_small hDmp
    _ = ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * Dmp := by
        rw [nsmul_eq_mul]
    _ ≤ Bextra := hbudget

/-- **Concrete extra-minor budget.**  The same statement with the per-frequency
angle specialised to `θextra h = W.theta (rfun h * sfun h)`, matching the
requested shape exactly. -/
theorem r2_extra_minor_budget_from_gadget_witnesses
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra Dmp : ℝ)
    (rfun sfun : ℕ → ℕ)
    (mfun : ℕ → ℤ)
    (hr : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (rfun h))
    (hs : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (sfun h))
    (hrs : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ≠ sfun h)
    (hθlb : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      1 / 3 ≤ W.theta (rfun h * sfun h))
    (hθub : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      W.theta (rfun h * sfun h) ≤ 2 / 3)
    (hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (sfun h)) = (mfun h : ZMod (sfun h)))
    (hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h)))
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      2 * |mfun h| < (sfun h : ℤ))
    (hDmp : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      Real.sqrt (1 - (8 / 9) / (rfun h : ℝ) ^ 2) ≤ Dmp)
    (hfactor : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h
        ≤ ‖bernoulliCharFun (W.theta (rfun h * sfun h))
            ((h : ℝ) / ((rfun h : ℝ) * (sfun h : ℝ)))‖)
    (hbudget : ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * Dmp ≤ Bextra) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra :=
  r2_extra_minor_budget_from_gadget_witnesses_abstract D W N MA Sblock Sextra
    Bextra Dmp rfun sfun (fun h => W.theta (rfun h * sfun h)) mfun
    hr hs hrs hθlb hθub hm_s hm_r hm_small hDmp hfactor hbudget

/-- **Packaged extra-minor witness data.**  Bundles the gadget witnesses and all
sibling/bridge/budget hypotheses for the extra-minor part, for a fixed concrete
setup and a fixed `MainArcFields` instance. -/
structure R2ExtraMinorWitnessData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra : ℝ) where
  rfun : ℕ → ℕ
  sfun : ℕ → ℕ
  thetaExtra : ℕ → ℝ
  mfun : ℕ → ℤ
  Dmp : ℝ
  hr : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (rfun h)
  hs : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (sfun h)
  hrs : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ≠ sfun h
  hθlb : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, 1 / 3 ≤ thetaExtra h
  hθub : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, thetaExtra h ≤ 2 / 3
  hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (sfun h)) = (mfun h : ZMod (sfun h))
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    2 * |mfun h| < (sfun h : ℤ)
  hDmp : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    Real.sqrt (1 - (8 / 9) / (rfun h : ℝ) ^ 2) ≤ Dmp
  hfactor : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    fourierNormWeight D.E W.theta b D.L h
      ≤ ‖bernoulliCharFun (thetaExtra h)
          ((h : ℝ) / ((rfun h : ℝ) * (sfun h : ℝ)))‖
  hbudget : ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * Dmp ≤ Bextra

/-- The packaged extra-minor witnesses yield the extra-minor norm-sum budget. -/
theorem r2_extra_minor_budget_of_witnessData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ) (Bextra : ℝ)
    (X : R2ExtraMinorWitnessData D W N MA Sblock Sextra Bextra) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra :=
  r2_extra_minor_budget_from_gadget_witnesses_abstract D W N MA Sblock Sextra
    Bextra X.Dmp X.rfun X.sfun X.thetaExtra X.mfun
    X.hr X.hs X.hrs X.hθlb X.hθub X.hm_s X.hm_r X.hm_small X.hDmp X.hfactor
    X.hbudget

end CircleMethod

end
