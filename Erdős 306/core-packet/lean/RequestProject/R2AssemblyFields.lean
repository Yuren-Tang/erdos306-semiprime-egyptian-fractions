import RequestProject.R2ConcreteData
import RequestProject.R2MinorEstimateInterface

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 final assembly field helpers

This leaf collects generic field-level lemmas for the final
`exists_arcConstruction` record.  They are deliberately independent of the
concrete parameter choices.
-/

/-- If every edge divides the period and the reciprocal load is `< 1`, then the
integer period-sum bound required by `ArcConstruction.hbound` follows. -/
lemma period_div_sum_lt_of_recip_sum_lt
    (E : Finset ℕ) (L : ℕ)
    (hL : 0 < L)
    (hepos : ∀ e ∈ E, 0 < e)
    (heL : ∀ e ∈ E, e ∣ L)
    (hload : ∑ e ∈ E, (1 : ℝ) / (e : ℝ) < 1) :
    (∑ e ∈ E, (L / e : ℕ)) < L := by
  have hcast :
      ((∑ e ∈ E, (L / e : ℕ) : ℕ) : ℝ)
        = ∑ e ∈ E, (L : ℝ) / (e : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [Nat.cast_div (heL e he) (by exact_mod_cast (hepos e he).ne')]
  have hfactor :
      (∑ e ∈ E, (L : ℝ) / (e : ℝ))
        = (L : ℝ) * ∑ e ∈ E, (1 : ℝ) / (e : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    field_simp [(by exact_mod_cast (hepos e he).ne' : (e : ℝ) ≠ 0)]
  have hreal :
      ((∑ e ∈ E, (L / e : ℕ) : ℕ) : ℝ) < (L : ℝ) := by
    rw [hcast, hfactor]
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    nlinarith
  exact_mod_cast hreal

/-- The same `hbound` helper in the concrete-data language. -/
lemma r2Concrete_hbound_of_recipLoad_lt_one {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hL : 0 < D.L)
    (hepos : ∀ e ∈ D.E, 0 < e)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (hload : R2ConcreteData.recipLoad D.E < 1) :
    (∑ e ∈ D.E, (D.L / e : ℕ)) < D.L := by
  exact period_div_sum_lt_of_recip_sum_lt D.E D.L hL hepos heL (by
    simpa [R2ConcreteData.recipLoad] using hload)

/-- If the total minor budget is already beaten at `sigmaCtrl`, and
`sigmaE ≤ sigmaCtrl`, then it is beaten at `sigmaE`. -/
lemma hbeat_of_sigma_le_sigmaCtrl
    (c3 sigmaE sigmaCtrl Bm : ℝ)
    (hc3 : 0 < c3)
    (hσE : 0 < sigmaE)
    (hσctrl : 0 < sigmaCtrl)
    (hσle : sigmaE ≤ sigmaCtrl)
    (hBm : Bm < c3 / sigmaCtrl) :
    Bm < c3 / sigmaE := by
  have hdiv : c3 / sigmaCtrl ≤ c3 / sigmaE := by
    rw [div_le_div_iff₀ hσctrl hσE]
    nlinarith
  exact lt_of_lt_of_le hBm hdiv

/-- Additive block/extra minor budgets imply the final `hbeat` once their sum is
strictly below the `sigmaCtrl` budget and `sigmaE ≤ sigmaCtrl`. -/
lemma hbeat_of_block_extra_sigmaCtrl
    (c3 sigmaE sigmaCtrl Bblock Bextra : ℝ)
    (hc3 : 0 < c3)
    (hσE : 0 < sigmaE)
    (hσctrl : 0 < sigmaCtrl)
    (hσle : sigmaE ≤ sigmaCtrl)
    (hminorCtrl : Bblock + Bextra < c3 / sigmaCtrl) :
    Bblock + Bextra < c3 / sigmaE :=
  hbeat_of_sigma_le_sigmaCtrl c3 sigmaE sigmaCtrl (Bblock + Bextra)
    hc3 hσE hσctrl hσle hminorCtrl

/-- The main-arc finite data required by `ArcConstruction`, isolated from the
rest of the construction. -/
structure MainArcFields (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (N : ℤ) where
  SM : Finset ℕ
  Sm : Finset ℕ
  lbl : ℕ → ℤ
  hpart : Finset.range L = SM ∪ Sm
  hdisj : Disjoint SM Sm
  hmaps : ∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N
  hinj : ∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂
  hsurj : ∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m
  hterm : ∀ h ∈ SM, fourierTerm E theta b L h = term_label E theta b (lbl h)

/-- Package the existing main-arc bijection as the exact record fields consumed
by `ArcConstruction`.  The minor arc is the complement of `SM` inside
`Finset.range L`. -/
lemma exists_mainArcFields
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (N : ℤ)
    (hb : 0 < b) (hbL : b ∣ L) (hL : 0 < L)
    (he0 : ∀ e ∈ E, 0 < e) (heL : ∀ e ∈ E, e ∣ L)
    (hN : 0 ≤ N) (hNL : 2 * N + 1 ≤ (L : ℤ)) :
    Nonempty (MainArcFields E theta b L N) := by
  classical
  obtain ⟨SM, lbl, hsub, hmaps, hinj, hsurj, hmod⟩ :=
    exists_mainArc_bijection L N hN hNL
  refine ⟨{
    SM := SM
    Sm := Finset.range L \ SM
    lbl := lbl
    hpart := ?_
    hdisj := ?_
    hmaps := hmaps
    hinj := hinj
    hsurj := hsurj
    hterm := ?_
  }⟩
  · exact (Finset.union_sdiff_of_subset hsub).symm
  · exact Finset.sdiff_disjoint.symm
  · intro h hh
    exact fourierTerm_eq_term_label_of_modL E theta b L h (lbl h)
      hb hbL hL he0 heL (hmod h hh)

end CircleMethod

end
