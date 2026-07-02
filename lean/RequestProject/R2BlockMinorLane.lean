import RequestProject.R2MinorSupportBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 block-minor lane

This file records the block-minor side of the R2 minor budget.  It is meant to
be developed as one coherent lane, not as scattered wrapper lemmas.

The key point is that the final `R2MinorSupportBudgetData` asks for a sum of
`fourierNormWeight`, while the global-control estimates are naturally stated in
`QE`-energy language.  The first lemmas below bridge those two formulations.
-/

/-- Pointwise C2/QE bridge at the constant used by the final minor arc. -/
lemma fourierNormWeight_le_exp_QE
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (hθ_lb : ∀ e ∈ E, (1 / 3 : ℝ) ≤ theta e)
    (hθ_ub : ∀ e ∈ E, theta e ≤ 2 / 3)
    (heL : ∀ e ∈ E, e ∣ L) (he0 : ∀ e ∈ E, 0 < e) (hL : 0 < L)
    (h : ℕ) :
    fourierNormWeight E theta b L h ≤ Real.exp (-(16 / 9 : ℝ) * QE E h) := by
  unfold fourierNormWeight fourierTerm
  rw [norm_mul]
  have hphase :
      ‖Complex.exp
        (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ))).re = 0 := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hre, Real.exp_zero]
  rw [hphase, mul_one]
  have hprod :
      (∏ e ∈ E, ((theta e : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
          + (1 - theta e)))
        = ∏ e ∈ E, bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ)) := by
    refine Finset.prod_congr rfl (fun e he => ?_)
    exact charfactor_eq (theta e) h e L (he0 e he) (heL e he) hL
  rw [hprod]
  have hbound := product_charFun_bound_QE (1 / 3) (by norm_num) (by norm_num)
    E theta hθ_lb (by
      intro e he
      have := hθ_ub e he
      norm_num at this ⊢
      linarith) h
  have hconst : (8 * (1 / 3 : ℝ) * (1 - 1 / 3)) = 16 / 9 := by norm_num
  rw [hconst] at hbound
  simpa [mul_assoc] using hbound

/-- Sum form of the pointwise bridge. -/
lemma sum_fourierNormWeight_le_exp_QE
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (S : Finset ℕ)
    (hθ_lb : ∀ e ∈ E, (1 / 3 : ℝ) ≤ theta e)
    (hθ_ub : ∀ e ∈ E, theta e ≤ 2 / 3)
    (heL : ∀ e ∈ E, e ∣ L) (he0 : ∀ e ∈ E, 0 < e) (hL : 0 < L) :
    ∑ h ∈ S, fourierNormWeight E theta b L h
      ≤ ∑ h ∈ S, Real.exp (-(16 / 9 : ℝ) * QE E h) := by
  exact Finset.sum_le_sum (fun h _ =>
    fourierNormWeight_le_exp_QE E theta b L hθ_lb hθ_ub heL he0 hL h)

/-- Block-minor budget from a `QE`-energy budget over the block part. -/
theorem r2_block_minor_budget_from_exp_QE
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock : Finset ℕ) (Bblock : ℝ)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (hL : 0 < D.L)
    (hExp :
      ∑ h ∈ blockMinorPart MA.Sm Sblock,
        Real.exp (-(16 / 9 : ℝ) * QE D.E h) ≤ Bblock) :
    ∑ h ∈ blockMinorPart MA.Sm Sblock,
      fourierNormWeight D.E W.theta b D.L h ≤ Bblock := by
  exact le_trans
    (sum_fourierNormWeight_le_exp_QE D.E W.theta b D.L
      (blockMinorPart MA.Sm Sblock) W.hlb W.hub heL he0 hL)
    hExp

/-- Block-minor budget from the fiber-tail global-control hypotheses.

This is the target interface for the block lane: the remaining mathematical
work is exactly to provide `hQE`, `hnotmain`, and `hfiber` for the chosen
`Sblock`. -/
theorem r2_block_minor_budget_from_fiber_tail
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock : Finset ℕ) (Bblock : ℝ)
    (C K : ℝ) (Qextra : ℕ → ℝ)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (hL : 0 < D.L)
    (hK : 0 ≤ K)
    (hQE : ∀ h ∈ blockMinorPart MA.Sm Sblock,
      Qctrl D.BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE D.E h)
    (hnotmain : ∀ h ∈ blockMinorPart MA.Sm Sblock,
      (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) ∉ mainArc D.BS C)
    (hfiber : ∀ a : GlobalAssignment D.BS,
      ∑ h ∈ (blockMinorPart MA.Sm Sblock).filter
        (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) = a),
        Real.exp (-(16 / 9 : ℝ) * Qextra h) ≤ K)
    (hbudget :
      K * ∑' a : {a : GlobalAssignment D.BS // a ∉ mainArc D.BS C},
          Real.exp (-(16 / 9 : ℝ) * Qctrl D.BS a.1) ≤ Bblock) :
    ∑ h ∈ blockMinorPart MA.Sm Sblock,
      fourierNormWeight D.E W.theta b D.L h ≤ Bblock := by
  refine r2_block_minor_budget_from_exp_QE D W N MA Sblock Bblock heL he0 hL ?_
  exact le_trans
    (block_part_bound D.BS D.E (16 / 9) C K MA.Sm Sblock Qextra
      (by norm_num) hK hQE hnotmain hfiber)
    hbudget

/-- G7-packaged block-minor budget.

This is the block lane in the same quantifier order as the global-control
partition: after `eps` and the desired loss `η` are fixed, a base scale and a
Gaussian-tail constant are produced.  The caller only has to verify the
block-specific support facts (`hQE`, `hnotmain`, `hfiber`) and choose `Bblock`
large enough for the resulting G7 budget. -/
theorem exists_r2_block_minor_budget_from_fiber_tail_g7
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (MA : MainArcFields D.E W.theta b D.L N)
      (Sblock : Finset ℕ) (Bblock C K : ℝ) (Qextra : ℕ → ℝ),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      1 ≤ C → 0 ≤ K →
      (∀ e ∈ D.E, e ∣ D.L) →
      (∀ e ∈ D.E, 0 < e) → 0 < D.L →
      (∀ h ∈ blockMinorPart MA.Sm Sblock,
        Qctrl D.BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE D.E h) →
      (∀ h ∈ blockMinorPart MA.Sm Sblock,
        (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) ∉ mainArc D.BS C) →
      (∀ a : GlobalAssignment D.BS,
        ∑ h ∈ (blockMinorPart MA.Sm Sblock).filter
          (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) = a),
          Real.exp (-(16 / 9 : ℝ) * Qextra h) ≤ K) →
      K * ((η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl D.BS)
        ≤ Bblock →
      ∑ h ∈ blockMinorPart MA.Sm Sblock,
        fourierNormWeight D.E W.theta b D.L h ≤ Bblock := by
  obtain ⟨k0min, Ctail, hCtail, hgcp⟩ :=
    global_control_partition (16 / 9) (by norm_num) eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N MA Sblock Bblock C K Qextra hk0 hadm hC hK
    heL he0 hL hQE hnotmain hfiber hBblock
  refine r2_block_minor_budget_from_fiber_tail D W N MA Sblock Bblock C K Qextra
    heL he0 hL hK hQE hnotmain hfiber ?_
  exact le_trans
    (mul_le_mul_of_nonneg_left (hgcp D.BS hk0 hadm C hC) hK)
    hBblock

end CircleMethod

end
