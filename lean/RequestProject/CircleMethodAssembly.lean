import RequestProject.CircleMethod
import RequestProject.CircleMethodMainTerm

open Complex Finset BigOperators Real

noncomputable section

namespace CircleMethod

/-!
# Phase C — R3 assembly interface (note 35 C5 / note 44 R3)

This file records the `ArcConstruction` interface: the bundle of circle-method
construction data (semiprime edges, weights, period, the main-arc label
bijection, the main-arc smallness conditions, and the **summed-norm** minor-arc
bound) produced by the R2 construction.  It is consumed downstream by
`egyptian_rep_ge3_R2`, which feeds it to the abstract `spectral_existence` cannon
via `CannonBridge.exists_subset_of_fourier_arcs`.

The earlier bespoke positivity glue (`wcount_pos_of_split`,
`exists_pos_weighted_of_construction`) has been retired: the arc-separation
positivity, the finite Fourier identity, and the subset extraction are now all
discharged in one step by the cannon.
-/

/-- **R2 construction interface (note 35 C1 / note 44 R3).**  The data of a
block-aligned circle-method construction for `1/b`: semiprime edges `E` avoiding
`T` with weights in `[1/3,2/3]` and exact mass, a common period `L`, a main-arc
frequency set `SM` bijecting (via `lbl`) to the label window `[-N,N]` with the
CRT/periodicity identity `fourierTerm = term_label`, the main-arc smallness
conditions, and a (summed-norm) minor-arc bound `Bm` strictly beaten by the
Gaussian main term `c₃/σ_E`. -/
structure ArcConstruction (T : Finset ℕ) (b : ℕ) where
  E : Finset ℕ
  theta : ℕ → ℝ
  L : ℕ
  N : ℤ
  SM : Finset ℕ
  Sm : Finset ℕ
  lbl : ℕ → ℤ
  Bm : ℝ
  hsemi : ∀ e ∈ E, IsSemiprime e
  havoid : ∀ e ∈ E, e ∉ T
  hne : E.Nonempty
  hL : 0 < L
  hbL : b ∣ L
  heL : ∀ e ∈ E, e ∣ L
  he0 : ∀ e ∈ E, 0 < e
  hbound : (∑ e ∈ E, (L / e : ℕ)) < L
  hlb : ∀ e ∈ E, 1/3 ≤ theta e
  hub : ∀ e ∈ E, theta e ≤ 2/3
  hmass : (∑ e ∈ E, theta e / (e : ℝ)) = 1 / (b : ℝ)
  hpart : Finset.range L = SM ∪ Sm
  hdisj : Disjoint SM Sm
  hN : (1:ℝ) / Real.sqrt (sigmaE2 E theta) ≤ (N:ℝ)
  htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10
  hsmall : ∀ m ∈ Finset.Icc (-N) N, (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10
  hmaps : ∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N
  hinj : ∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂
  hsurj : ∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m
  hterm : ∀ h ∈ SM, fourierTerm E theta b L h = term_label E theta b (lbl h)
  hminor : (∑ h ∈ Sm, ‖fourierTerm E theta b L h‖) ≤ Bm
  hbeat : Bm < 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)


end CircleMethod

end
