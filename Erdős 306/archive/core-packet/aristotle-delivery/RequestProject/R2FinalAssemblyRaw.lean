import RequestProject.R2FinalAssembly

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# Raw-input R2 final assembly wrappers

This thin leaf sits downstream of `R2FinalAssembly`.  It keeps the already-built
assembly spine stable while exposing endpoints whose hypotheses are closer to
the final parameter-selection lemmas.
-/

/-- Final R2 assembly from raw numeric-window inequalities.

Compared with
`exists_arcConstruction_of_componentData_numeric_minor_window`, this wrapper
does not ask for a prebuilt `MainArcNumericFields` package.  It derives that
package from the raw scale, edge-lower, ratio, and cubic-load hypotheses. -/
theorem exists_arcConstruction_of_componentData_raw_numeric_minor_window
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hedge : ∀ e ∈ D.E, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hρnonneg : 0 ≤ ρ)
    (hratio : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hcard : (D.E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10)
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
    (hloadDisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))
    (hloadLower :
      3 / (2 * (b : ℝ)) ≤ D.baseLoad + R2ConcreteData.recipLoad D.Q)
    (hloadUpper :
      D.baseLoad + R2ConcreteData.recipLoad D.Q < 3 / (b : ℝ))
    (C : ∀ MA : MainArcFields D.E W.theta b D.L N, R2MinorCoverData MA.Sm)
    (hblock : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ blockMinorPart MA.Sm (C MA).Sblock,
        fourierNormWeight D.E W.theta b D.L h ≤ Bblock)
    (hextra : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ extraMinorPart MA.Sm (C MA).Sblock (C MA).Sextra,
        fourierNormWeight D.E W.theta b D.L h ≤ Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  have hsemi : ∀ e ∈ D.E, IsSemiprime e :=
    D.semiprime hQsemi hRprime hSprime hlt
  have he0 : ∀ e ∈ D.E, 0 < e :=
    D.edges_pos hsemi
  let NF : MainArcNumericFields D.E W.theta N :=
    mainArcNumericFields_of D.E W.theta N ρ hNscale he0 hedge
      hρnonneg hratio hcard
  exact exists_arcConstruction_of_componentData_numeric_minor_window hb D W N
    Bblock Bextra hadm NF hNL hQsemi hRprime hSprime hlt hctrlAvoid hQavoid
    hgadgetAvoid hQne hQdvd hRdvd hSblock hloadDisj hloadLower hloadUpper
    C hblock hextra hextraLight hminorCtrl

/-- Variant of the raw final wrapper where the minor cover is supplied as two
families of support sets and a pointwise cover proof, instead of an already
packed `R2MinorCoverData`. -/
theorem exists_arcConstruction_of_componentData_raw_numeric_minor_sets
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hedge : ∀ e ∈ D.E, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ))
    (hρnonneg : 0 ≤ ρ)
    (hratio : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ D.E,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hcard : (D.E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10)
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
    (hloadDisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))
    (hloadLower :
      3 / (2 * (b : ℝ)) ≤ D.baseLoad + R2ConcreteData.recipLoad D.Q)
    (hloadUpper :
      D.baseLoad + R2ConcreteData.recipLoad D.Q < 3 / (b : ℝ))
    (Sblock Sextra : MainArcFields D.E W.theta b D.L N → Finset ℕ)
    (hcover : ∀ MA : MainArcFields D.E W.theta b D.L N,
      MA.Sm ⊆ Sblock MA ∪ Sextra MA)
    (hblock : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ blockMinorPart MA.Sm (Sblock MA),
        fourierNormWeight D.E W.theta b D.L h ≤ Bblock)
    (hextra : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∑ h ∈ extraMinorPart MA.Sm (Sblock MA) (Sextra MA),
        fourierNormWeight D.E W.theta b D.L h ≤ Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  let C : ∀ MA : MainArcFields D.E W.theta b D.L N, R2MinorCoverData MA.Sm :=
    fun MA => { Sblock := Sblock MA, Sextra := Sextra MA, hcover := hcover MA }
  exact exists_arcConstruction_of_componentData_raw_numeric_minor_window hb D W N
    Bblock Bextra ρ hadm hNscale hedge hρnonneg hratio hcard hNL hQsemi
    hRprime hSprime hlt hctrlAvoid hQavoid hgadgetAvoid hQne hQdvd hRdvd
    hSblock hloadDisj hloadLower hloadUpper C hblock hextra
    hextraLight hminorCtrl

end CircleMethod

end
