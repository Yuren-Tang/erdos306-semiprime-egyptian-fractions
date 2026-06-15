import RequestProject.R2ExtraMinorLane

open Finset BigOperators

noncomputable section

namespace CircleMethod

/-!
# Single-factor control for the R2 extra lane

The extra-minor lane asks for a bridge from the full Fourier summand norm to one
chosen gadget Bernoulli factor.  This file proves that bridge abstractly: every
other Bernoulli factor has norm at most one, so the whole product is bounded by
any selected factor belonging to the edge set.
-/

lemma bernoulliCharFun_norm_le_one (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖bernoulliCharFun θ t‖ ≤ 1 := by
  have hsq : ‖bernoulliCharFun θ t‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq, bernoulliCharFun_normSq]
    have h1θ : 0 ≤ 1 - θ := by linarith
    have hnonneg :
        0 ≤ 4 * θ * (1 - θ) * Real.sin (Real.pi * t) ^ 2 := by positivity
    nlinarith
  nlinarith [sq_nonneg (‖bernoulliCharFun θ t‖ - 1)]

lemma norm_prod_le_norm_of_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (F : α → ℂ) {a : α}
    (ha : a ∈ S) (hF : ∀ x ∈ S, ‖F x‖ ≤ 1) :
    ‖∏ x ∈ S, F x‖ ≤ ‖F a‖ := by
  classical
  have hsplit : (∏ x ∈ S, F x) = F a * ∏ x ∈ S.erase a, F x := by
    have hnot : a ∉ S.erase a := by simp
    rw [← Finset.prod_insert hnot, Finset.insert_erase ha]
  rw [hsplit, norm_mul]
  have hrest : ‖∏ x ∈ S.erase a, F x‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one ?_ ?_
    · intro x hx
      exact norm_nonneg (F x)
    · intro x hx
      exact hF x (Finset.mem_of_mem_erase hx)
  exact mul_le_of_le_one_right (norm_nonneg (F a)) hrest

/-- The full Fourier summand norm is controlled by any Bernoulli factor whose
edge lies in `E`. -/
lemma fourierNormWeight_le_factor_of_mem
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L h e0 : ℕ)
    (he0mem : e0 ∈ E)
    (hθ0 : ∀ e ∈ E, 0 ≤ theta e)
    (hθ1 : ∀ e ∈ E, theta e ≤ 1)
    (heL : ∀ e ∈ E, e ∣ L)
    (hepos : ∀ e ∈ E, 0 < e)
    (hL : 0 < L) :
    fourierNormWeight E theta b L h
      ≤ ‖bernoulliCharFun (theta e0) ((h : ℝ) / (e0 : ℝ))‖ := by
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
    exact charfactor_eq (theta e) h e L (hepos e he) (heL e he) hL
  rw [hprod]
  exact norm_prod_le_norm_of_mem E (fun e => bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ)))
    he0mem (fun e he => bernoulliCharFun_norm_le_one (theta e) ((h : ℝ) / (e : ℝ))
      (hθ0 e he) (hθ1 e he))

/-- Concrete `hfactor` for the extra lane, using the selected gadget edge
`rfun h * sfun h`. -/
lemma r2_extra_hfactor_of_gadget_mem
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D)
    (N : ℤ) (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (rfun sfun : ℕ → ℕ)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (hepos : ∀ e ∈ D.E, 0 < e)
    (hL : 0 < D.L)
    (hmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      rfun h * sfun h ∈ D.E) :
    ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h
        ≤ ‖bernoulliCharFun (W.theta (rfun h * sfun h))
            ((h : ℝ) / ((rfun h : ℝ) * (sfun h : ℝ)))‖ := by
  intro h hh
  have hfactor := fourierNormWeight_le_factor_of_mem D.E W.theta b D.L h
    (rfun h * sfun h) (hmem h hh)
    (fun e he => by
      have hle := W.hlb e he
      norm_num at hle ⊢
      linarith)
    (fun e he => by
      have hle := W.hub e he
      norm_num at hle ⊢
      linarith)
    heL hepos hL
  simpa [Nat.cast_mul] using hfactor

end CircleMethod

end
