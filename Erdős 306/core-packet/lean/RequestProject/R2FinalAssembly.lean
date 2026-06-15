import RequestProject.R2AssemblyFields

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 final assembly spine

This file is the local mainline for the endgame.  It does not choose the final
block system or prove the remaining supply estimates; instead it records the
exact data that, once supplied, constructs an `ArcConstruction`.
-/

/-- Hypothesis-heavy final R2 supply package.

The point of this structure is to keep the final `ArcConstruction` assembly
small while the independent numeric and minor-cover tasks fill in the remaining
fields. -/
structure R2FinalSupply (T : Finset ℕ) (b : ℕ) where
  D : R2ConcreteData T b
  W : R2ConcreteData.Weights D
  N : ℤ
  MA : MainArcFields D.E W.theta b D.L N
  Bm : ℝ
  hsemi : ∀ e ∈ D.E, IsSemiprime e
  havoid : ∀ e ∈ D.E, e ∉ T
  hne : D.E.Nonempty
  heL : ∀ e ∈ D.E, e ∣ D.L
  he0 : ∀ e ∈ D.E, 0 < e
  hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ)
  hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ)
  htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
    |(m : ℝ) / (e : ℝ)| ≤ 1 / 10
  hsmall : ∀ m ∈ Finset.Icc (-N) N,
    (∑ e ∈ D.E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10
  hminor : ‖∑ h ∈ MA.Sm, fourierTerm D.E W.theta b D.L h‖ ≤ Bm
  hbeat : Bm < 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) /
    Real.sqrt (sigmaE2 D.E W.theta)

/-- Assemble an `ArcConstruction` from the final supply package. -/
def R2FinalSupply.toArcConstruction {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b) (S : R2FinalSupply T b) : ArcConstruction T b where
  E := S.D.E
  theta := S.W.theta
  L := S.D.L
  N := S.N
  SM := S.MA.SM
  Sm := S.MA.Sm
  lbl := S.MA.lbl
  Bm := S.Bm
  hsemi := S.hsemi
  havoid := S.havoid
  hne := S.hne
  hL := S.D.period_pos (Nat.lt_of_lt_of_le (by norm_num) hb)
  hbL := S.D.base_dvd_period
  heL := S.heL
  he0 := S.he0
  hbound := r2Concrete_hbound_of_recipLoad_window S.D hb
    (S.D.period_pos (Nat.lt_of_lt_of_le (by norm_num) hb)) S.he0 S.heL S.hloadUpper
  hlb := S.W.hlb
  hub := S.W.hub
  hmass := S.W.hmass
  hpart := S.MA.hpart
  hdisj := S.MA.hdisj
  hN := S.hN
  htw := S.htw
  hsmall := S.hsmall
  hmaps := S.MA.hmaps
  hinj := S.MA.hinj
  hsurj := S.MA.hsurj
  hterm := S.MA.hterm
  hminor := S.hminor
  hbeat := S.hbeat

/-- The final assembly theorem in hypothesis-heavy form.  This is the spine that
the remaining construction lemmas should feed. -/
theorem exists_arcConstruction_of_R2FinalSupply
    (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b)
    (S : R2FinalSupply T b) :
    Nonempty (ArcConstruction T b) :=
  ⟨S.toArcConstruction hb⟩

/-- Assemble the final supply package while constructing the main-arc finite
data from the period inequality.  This is the interface expected after the
numeric-field lane returns `0 ≤ N` and `2N+1 ≤ L`. -/
theorem exists_R2FinalSupply_of_mainArcParams
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) (Bm : ℝ)
    (hbpos : 0 < b)
    (hL : 0 < D.L)
    (hbL : b ∣ D.L)
    (hNnonneg : 0 ≤ N)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hsemi : ∀ e ∈ D.E, IsSemiprime e)
    (havoid : ∀ e ∈ D.E, e ∉ T)
    (hne : D.E.Nonempty)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ))
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ D.E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10)
    (hminor : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ‖∑ h ∈ MA.Sm, fourierTerm D.E W.theta b D.L h‖ ≤ Bm)
    (hbeat : Bm < 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) /
      Real.sqrt (sigmaE2 D.E W.theta)) :
    Nonempty (R2FinalSupply T b) := by
  obtain ⟨MA⟩ := exists_mainArcFields D.E W.theta b D.L N
    hbpos hbL hL he0 heL hNnonneg hNL
  exact ⟨{
    D := D
    W := W
    N := N
    MA := MA
    Bm := Bm
    hsemi := hsemi
    havoid := havoid
    hne := hne
    heL := heL
    he0 := he0
    hloadUpper := hloadUpper
    hN := hN
    htw := htw
    hsmall := hsmall
    hminor := hminor MA
    hbeat := hbeat
  }⟩

/-- Direct final assembly from concrete data plus main-arc parameters. -/
theorem exists_arcConstruction_of_mainArcParams
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) (Bm : ℝ)
    (hNnonneg : 0 ≤ N)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hsemi : ∀ e ∈ D.E, IsSemiprime e)
    (havoid : ∀ e ∈ D.E, e ∉ T)
    (hne : D.E.Nonempty)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ))
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ D.E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10)
    (hminor : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ‖∑ h ∈ MA.Sm, fourierTerm D.E W.theta b D.L h‖ ≤ Bm)
    (hbeat : Bm < 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) /
      Real.sqrt (sigmaE2 D.E W.theta)) :
    Nonempty (ArcConstruction T b) := by
  have hbpos : 0 < b := Nat.lt_of_lt_of_le (by norm_num) hb
  have hL : 0 < D.L := D.period_pos hbpos
  obtain ⟨S⟩ := exists_R2FinalSupply_of_mainArcParams D W N Bm
    hbpos hL D.base_dvd_period hNnonneg hNL hsemi havoid hne heL he0 hloadUpper
    hN htw hsmall hminor hbeat
  exact exists_arcConstruction_of_R2FinalSupply T b hb S

/-- Direct final assembly when the minor bound is given as a block/extra sum
beaten at `sigmaCtrl`.  This is the expected endpoint after the minor-cover lane
returns an `hminor` estimate and the concrete construction supplies
`sigmaE <= sigmaCtrl`. -/
theorem exists_arcConstruction_of_blockExtraBudget
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra : ℝ)
    (hNnonneg : 0 ≤ N)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hsemi : ∀ e ∈ D.E, IsSemiprime e)
    (havoid : ∀ e ∈ D.E, e ∉ T)
    (hne : D.E.Nonempty)
    (heL : ∀ e ∈ D.E, e ∣ D.L)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ))
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ D.E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10)
    (hminor : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ‖∑ h ∈ MA.Sm, fourierTerm D.E W.theta b D.L h‖ ≤ Bblock + Bextra)
    (hσctrl : 0 < sigmaCtrl D.BS)
    (hσle : Real.sqrt (sigmaE2 D.E W.theta) ≤ sigmaCtrl D.BS)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  have hσE : 0 < Real.sqrt (sigmaE2 D.E W.theta) :=
    sigmaE_sqrt_pos_of_weights D W hne he0
  have hc3 : 0 < 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) := by
    positivity
  exact exists_arcConstruction_of_mainArcParams hb D W N (Bblock + Bextra)
    hNnonneg hNL hsemi havoid hne heL he0 hloadUpper hN htw hsmall hminor
    (hbeat_of_sigma_le_sigmaCtrl
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2))
      (Real.sqrt (sigmaE2 D.E W.theta)) (sigmaCtrl D.BS) (Bblock + Bextra)
      hc3 hσE hσctrl hσle hminorCtrl)

/-- Same endpoint, but the structural edge fields are generated from the
component hypotheses exposed by `R2ConcreteData`. -/
theorem exists_arcConstruction_of_componentData
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra : ℝ)
    (hNnonneg : 0 ≤ N)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hQsemi : ∀ e ∈ D.Q, IsSemiprime e)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hQavoid : ∀ e ∈ D.Q, e ∉ T)
    (hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T)
    (hQne : D.Q.Nonempty)
    (hQdvd : ∀ e ∈ D.Q, e ∣ D.L)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS)
    (hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ))
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ D.E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10)
    (hminor : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ‖∑ h ∈ MA.Sm, fourierTerm D.E W.theta b D.L h‖ ≤ Bblock + Bextra)
    (hσctrl : 0 < sigmaCtrl D.BS)
    (hσle : Real.sqrt (sigmaE2 D.E W.theta) ≤ sigmaCtrl D.BS)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  have hsemi : ∀ e ∈ D.E, IsSemiprime e :=
    D.semiprime hQsemi hRprime hSprime hlt
  have havoid : ∀ e ∈ D.E, e ∉ T :=
    D.avoid hctrlAvoid hQavoid hgadgetAvoid
  have hne : D.E.Nonempty :=
    D.nonempty_of_massBatch_nonempty hQne
  have heL : ∀ e ∈ D.E, e ∣ D.L :=
    D.dvd_period hQdvd hRdvd hSblock
  have he0 : ∀ e ∈ D.E, 0 < e :=
    D.edges_pos hsemi
  exact exists_arcConstruction_of_blockExtraBudget hb D W N Bblock Bextra
    hNnonneg hNL hsemi havoid hne heL he0 hloadUpper hN htw hsmall hminor
    hσctrl hσle hminorCtrl

/-- Component-data endpoint with the sigma hypotheses generated from the
admissible block system and the explicit light-extra condition. -/
theorem exists_arcConstruction_of_componentData_light
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNnonneg : 0 ≤ N)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hQsemi : ∀ e ∈ D.Q, IsSemiprime e)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hQavoid : ∀ e ∈ D.Q, e ∉ T)
    (hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T)
    (hQne : D.Q.Nonempty)
    (hQdvd : ∀ e ∈ D.Q, e ∣ D.L)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS)
    (hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ))
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ D.E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10)
    (hminor : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ‖∑ h ∈ MA.Sm, fourierTerm D.E W.theta b D.L h‖ ≤ Bblock + Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  exact exists_arcConstruction_of_componentData hb D W N Bblock Bextra
    hNnonneg hNL hQsemi hRprime hSprime hlt hctrlAvoid hQavoid hgadgetAvoid
    hQne hQdvd hRdvd hSblock hloadUpper hN htw hsmall hminor
    (sigmaCtrl_pos D.BS hadm)
    (D.sigma_le_sigmaCtrl_of_light W.theta hextraLight)
    hminorCtrl

end CircleMethod

end
