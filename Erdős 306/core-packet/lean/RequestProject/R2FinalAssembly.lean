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

end CircleMethod

end
