import RequestProject.R2FourierFactor

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor multi-gadget interface

The earlier one-gadget extra lane is useful locally, but the terminal R2
argument needs several gadget factors for each extra frequency.  This file
records the correct budget interface without yet choosing the gadgets.
-/

/-- If `A ⊆ E`, all factors have norm at most one, and factors on `A` are
bounded by `D`, then the full product over `E` is bounded by `D ^ |A|`.

This is the finite-product core of the multi-gadget damping argument. -/
lemma norm_prod_le_pow_of_subset_bound {α : Type*} [DecidableEq α]
    (E A : Finset α) (F : α → ℂ) (D : ℝ)
    (hsub : A ⊆ E)
    (hF1 : ∀ e ∈ E, ‖F e‖ ≤ 1)
    (hD0 : 0 ≤ D)
    (hFD : ∀ e ∈ A, ‖F e‖ ≤ D) :
    ‖∏ e ∈ E, F e‖ ≤ D ^ A.card := by
  classical
  rw [norm_prod]
  have hsplit :
      ∏ e ∈ E, ‖F e‖ =
        (∏ e ∈ A, ‖F e‖) * ∏ e ∈ E \ A, ‖F e‖ := by
    rw [← Finset.prod_union]
    · congr
      exact (Finset.union_sdiff_of_subset hsub).symm
    · exact disjoint_sdiff
  rw [hsplit]
  have hA : ∏ e ∈ A, ‖F e‖ ≤ ∏ _e ∈ A, D := by
    exact Finset.prod_le_prod (fun e _ => norm_nonneg (F e)) hFD
  have hrest : ∏ e ∈ E \ A, ‖F e‖ ≤ 1 := by
    refine Finset.prod_le_one ?_ ?_
    · intro e _
      exact norm_nonneg (F e)
    · intro e he
      exact hF1 e (Finset.mem_sdiff.mp he).1
  calc
    (∏ e ∈ A, ‖F e‖) * ∏ e ∈ E \ A, ‖F e‖
        ≤ (∏ _e ∈ A, D) * 1 := by
          exact mul_le_mul hA hrest
            (Finset.prod_nonneg fun e _ => norm_nonneg (F e))
            (Finset.prod_nonneg fun _ _ => hD0)
    _ = D ^ A.card := by simp

/-- The selected gadget edge set for a fixed denominator prime `r` and a set of
block-side primes `G`. -/
def multiGadgetEdges (r : ℕ) (G : Finset ℕ) : Finset ℕ :=
  G.image fun s => r * s

/-- Multiplication by a positive `r` is injective on natural numbers. -/
lemma mul_left_injective_nat {r : ℕ} (hr : 0 < r) :
    Function.Injective fun s : ℕ => r * s := by
  intro s t h
  exact Nat.eq_of_mul_eq_mul_left hr h

/-- Cardinality of the selected gadget edge set. -/
lemma card_multiGadgetEdges (r : ℕ) (G : Finset ℕ) (hr : 0 < r) :
    (multiGadgetEdges r G).card = G.card := by
  unfold multiGadgetEdges
  exact Finset.card_image_of_injective G (mul_left_injective_nat hr)

/-- The full Fourier summand is bounded by the product of the selected gadget
factors.  This is the multi-factor version of
`fourierNormWeight_le_factor_of_mem`. -/
lemma fourierNormWeight_le_multi_gadget_product
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L h r : ℕ) (G : Finset ℕ)
    (hrpos : 0 < r)
    (hGmem : multiGadgetEdges r G ⊆ E)
    (hθ0 : ∀ e ∈ E, 0 ≤ theta e)
    (hθ1 : ∀ e ∈ E, theta e ≤ 1)
    (heL : ∀ e ∈ E, e ∣ L)
    (hepos : ∀ e ∈ E, 0 < e)
    (hL : 0 < L) :
    fourierNormWeight E theta b L h
      ≤ ∏ s ∈ G,
          ‖bernoulliCharFun (theta (r * s))
            ((h : ℝ) / ((r : ℝ) * (s : ℝ)))‖ := by
  classical
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
  have hfull :
      ‖∏ e ∈ E, bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ))‖
        ≤ ∏ e ∈ multiGadgetEdges r G,
            ‖bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ))‖ := by
    rw [norm_prod]
    have hsplit :
        ∏ e ∈ E, ‖bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ))‖ =
          (∏ e ∈ multiGadgetEdges r G,
              ‖bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ))‖) *
            ∏ e ∈ E \ multiGadgetEdges r G,
              ‖bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ))‖ := by
      rw [← Finset.prod_union]
      · congr
        exact (Finset.union_sdiff_of_subset hGmem).symm
      · exact disjoint_sdiff
    rw [hsplit]
    have hrest :
        ∏ e ∈ E \ multiGadgetEdges r G,
          ‖bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ))‖ ≤ 1 := by
      refine Finset.prod_le_one ?_ ?_
      · intro e _
        exact norm_nonneg _
      · intro e he
        exact bernoulliCharFun_norm_le_one (theta e) ((h : ℝ) / (e : ℝ))
          (hθ0 e (Finset.mem_sdiff.mp he).1) (hθ1 e (Finset.mem_sdiff.mp he).1)
    exact mul_le_of_le_one_right
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hrest
  refine le_trans hfull ?_
  unfold multiGadgetEdges
  rw [Finset.prod_image]
  · simp [Nat.cast_mul]
  · intro s hs t ht hst
    exact Nat.eq_of_mul_eq_mul_left hrpos hst

/-- Multi-gadget pointwise damping for one frequency. -/
lemma fourierNormWeight_le_multi_gadget_damp
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L h r : ℕ) (m : ℤ) (G : Finset ℕ)
    (hr : Nat.Prime r)
    (hs : ∀ s ∈ G, Nat.Prime s)
    (hrs : ∀ s ∈ G, r ≠ s)
    (hGmem : multiGadgetEdges r G ⊆ E)
    (hθlb : ∀ s ∈ G, 1 / 3 ≤ theta (r * s))
    (hθub : ∀ s ∈ G, theta (r * s) ≤ 2 / 3)
    (hm_s : ∀ s ∈ G, (h : ZMod s) = (m : ZMod s))
    (hm_r : (h : ZMod r) ≠ (m : ZMod r))
    (hm_small : ∀ s ∈ G, 2 * |m| < (s : ℤ))
    (hθ0 : ∀ e ∈ E, 0 ≤ theta e)
    (hθ1 : ∀ e ∈ E, theta e ≤ 1)
    (heL : ∀ e ∈ E, e ∣ L)
    (hepos : ∀ e ∈ E, 0 < e)
    (hL : 0 < L) :
    fourierNormWeight E theta b L h
      ≤ (Real.sqrt (1 - (8 / 9) / (r : ℝ) ^ 2)) ^ G.card := by
  classical
  refine le_trans
    (fourierNormWeight_le_multi_gadget_product E theta b L h r G
      hr.pos hGmem hθ0 hθ1 heL hepos hL) ?_
  have hprod :
      ∏ s ∈ G,
          ‖bernoulliCharFun (theta (r * s))
            ((h : ℝ) / ((r : ℝ) * (s : ℝ)))‖
        ≤ ∏ _s ∈ G, Real.sqrt (1 - (8 / 9) / (r : ℝ) ^ 2) := by
    refine Finset.prod_le_prod (fun s _ => norm_nonneg _) ?_
    intro s hsG
    exact gadget_charFun_damp r s hr (hs s hsG) (hrs s hsG)
      (theta (r * s)) (hθlb s hsG) (hθub s hsG) h m
      (hm_s s hsG) hm_r (hm_small s hsG)
  simpa using hprod

/-- Multi-gadget extra-minor data after the pointwise product damping has been
proved.  The field `Gset h` is the finite set of block-side gadget primes used
for frequency `h`, while `damp h` is the per-frequency damping base. -/
structure R2ExtraMinorMultiGadgetBoundData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (Bextra : ℝ) where
  rfun : ℕ → ℕ
  Gset : ℕ → Finset ℕ
  mfun : ℕ → ℤ
  damp : ℕ → ℝ
  hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R
  hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S
  hm_s : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    (h : ZMod s) = (mfun h : ZMod s)
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
    2 * |mfun h| < (s : ℤ)
  hfactorMulti : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    fourierNormWeight D.E W.theta b D.L h ≤ damp h ^ (Gset h).card
  hbudget :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra, damp h ^ (Gset h).card ≤ Bextra

/-- Multi-gadget extra data gives the extra-minor norm-sum budget. -/
theorem r2_extra_minor_budget_of_multiGadgetBoundData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ) (Bextra : ℝ)
    (X : R2ExtraMinorMultiGadgetBoundData D W N MA Sblock Sextra Bextra) :
    ∑ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      fourierNormWeight D.E W.theta b D.L h ≤ Bextra := by
  exact le_trans (Finset.sum_le_sum X.hfactorMulti) X.hbudget

end CircleMethod

end
