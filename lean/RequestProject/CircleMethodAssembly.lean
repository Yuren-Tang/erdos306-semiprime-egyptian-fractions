import RequestProject.CircleMethod
import RequestProject.CircleMethodMainTerm

open Complex Finset BigOperators Real

noncomputable section

namespace CircleMethod

/-!
# Phase C — R3 assembly glue (note 35 C5 / note 44 R3)

Pure arc-separation positivity: given the Fourier identity split
`range L = SM ⊎ Sm`, a real lower bound on the main-arc real part, a norm bound on
the minor-arc sum, and an imaginary-part bound on the main-arc sum (all supplied by
`main_sum_re_lower` and `minor_arc_bound`), `Wcount > 0` follows from
`positivity_from_arcs`.  No `BlockSystem`; everything BlockSystem-specific enters
only through the hypotheses.
-/

/-- **R3 separation glue.**  The Fourier sum splits into a main-arc part with
positive real part and a minor part of small norm; folding the main-arc imaginary
part into the minor remainder, `positivity_from_arcs` gives `Wcount > 0`. -/
lemma wcount_pos_of_split
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (hb : 2 ≤ b) (hL : 0 < L) (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L)
    (he0 : ∀ e ∈ E, 0 < e) (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (SM Sm : Finset ℕ)
    (hpart : Finset.range L = SM ∪ Sm) (hdisj : Disjoint SM Sm)
    (mainPos Bm Bi : ℝ)
    (hmainPos : 0 < mainPos)
    (hmain_re : mainPos ≤ (∑ h ∈ SM, fourierTerm E theta b L h).re)
    (hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm)
    (hmain_im : |(∑ h ∈ SM, fourierTerm E theta b L h).im| ≤ Bi)
    (hbeat : Bm + Bi < mainPos) :
    0 < Wcount E theta b := by
  set SMsum : ℂ := ∑ h ∈ SM, fourierTerm E theta b L h with hSM
  set Smsum : ℂ := ∑ h ∈ Sm, fourierTerm E theta b L h with hSm
  -- Fourier identity: (L:ℂ)·Wcount = ∑_{range L} fourierTerm = SMsum + Smsum
  have hsplit : (∑ h ∈ Finset.range L, fourierTerm E theta b L h) = SMsum + Smsum := by
    rw [hSM, hSm, ← Finset.sum_union hdisj, ← hpart]
  have hident0 : (L : ℂ) * (Wcount E theta b : ℂ)
      = ∑ h ∈ Finset.range L, fourierTerm E theta b L h := by
    rw [wcount_fourier_identity E theta b L hb hL hbL heL he0 hbound]
    rfl
  -- main := Re SMsum, minorSum := Smsum + (SMsum − Re SMsum) = Smsum + i·Im SMsum
  set main : ℝ := SMsum.re with hmaindef
  set minorSum : ℂ := Smsum + (SMsum - (SMsum.re : ℂ)) with hminordef
  have hident : (L : ℂ) * (Wcount E theta b : ℂ) = (main : ℂ) + minorSum := by
    rw [hident0, hsplit, hminordef, hmaindef]; ring
  -- main is large; minorSum is small
  have hmainpos' : 0 < main := lt_of_lt_of_le hmainPos hmain_re
  have himeq : SMsum - (SMsum.re : ℂ) = (SMsum.im : ℂ) * Complex.I := by
    have := Complex.re_add_im SMsum
    linear_combination -this
  have hminorbnd : ‖minorSum‖ ≤ Bm + Bi := by
    rw [hminordef]
    refine le_trans (norm_add_le _ _) ?_
    rw [himeq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add hminor hmain_im
  have hbeat' : Bm + Bi < main := lt_of_lt_of_le hbeat hmain_re
  exact positivity_from_arcs L hL (Wcount E theta b) main (Bm + Bi) minorSum
    hident hmainpos' hminorbnd hbeat'

/-- **C5 full assembly (b ≥ 2).**  From a circle-method construction — semiprime
edges `E` avoiding `T` with weights `θ ∈ [1/3,2/3]`, exact mass `∑θ_e/e = 1/b`, a
common period `L`, the main-arc label bijection (CRT/periodicity), the main-arc
smallness conditions, and a minor-arc bound `Bm` beaten by the Gaussian main term
`c₃/σ_E` — the deterministic weighted count is strictly positive.  This is the
verified circle-method core: main arc (`main_sum_re_lower`, real by
`main_sum_im_zero`) beats minor arc, via `wcount_pos_of_split`. -/
theorem exists_pos_weighted_of_construction
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b)
    (E : Finset ℕ) (theta : ℕ → ℝ) (L : ℕ) (N : ℤ) (SM Sm : Finset ℕ) (lbl : ℕ → ℤ)
    (Bm : ℝ)
    (hsemi : ∀ e ∈ E, IsSemiprime e) (havoid : ∀ e ∈ E, e ∉ T)
    (hne : E.Nonempty) (hL : 0 < L) (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L)
    (he0 : ∀ e ∈ E, 0 < e) (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (hlb : ∀ e ∈ E, 1/3 ≤ theta e) (hub : ∀ e ∈ E, theta e ≤ 2/3)
    (hmass : (∑ e ∈ E, theta e / (e : ℝ)) = 1 / (b : ℝ))
    (hpart : Finset.range L = SM ∪ Sm) (hdisj : Disjoint SM Sm)
    (hN : (1:ℝ) / Real.sqrt (sigmaE2 E theta) ≤ (N:ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N, (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10)
    (hmaps : ∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N)
    (hinj : ∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂)
    (hsurj : ∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m)
    (hterm : ∀ h ∈ SM, fourierTerm E theta b L h = term_label E theta b (lbl h))
    (hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm)
    (hbeat : Bm < 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)) :
    0 < Wcount E theta b := by
  have hσ2pos : 0 < sigmaE2 E theta := sigmaE2_pos E theta hne he0 hlb hub
  have hσpos : 0 < Real.sqrt (sigmaE2 E theta) := Real.sqrt_pos.mpr hσ2pos
  set mainPos : ℝ := 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)
    with hmainPosDef
  have hmainPos : 0 < mainPos := by
    rw [hmainPosDef]; positivity
  have hmain_re : mainPos ≤ (∑ h ∈ SM, fourierTerm E theta b L h).re :=
    main_sum_re_lower E theta b L N SM lbl hne he0 hlb hub hmass hN htw hsmall
      hmaps hinj hsurj hterm
  have hmain_im : |(∑ h ∈ SM, fourierTerm E theta b L h).im| ≤ 0 := by
    rw [main_sum_im_zero E theta b L N SM lbl hmaps hinj hsurj hterm, abs_zero]
  exact wcount_pos_of_split E theta b L hb hL hbL heL he0 hbound SM Sm hpart hdisj
    mainPos Bm 0 hmainPos hmain_re hminor hmain_im (by linarith [hbeat])

/-- **R2 construction interface (note 35 C1 / note 44 R3).**  The data of a
block-aligned circle-method construction for `1/b`: semiprime edges `E` avoiding
`T` with weights in `[1/3,2/3]` and exact mass, a common period `L`, a main-arc
frequency set `SM` bijecting (via `lbl`) to the label window `[-N,N]` with the
CRT/periodicity identity `fourierTerm = term_label`, the main-arc smallness
conditions, and a minor-arc bound `Bm` strictly beaten by the Gaussian main term
`c₃/σ_E`.  Exactly the hypotheses consumed by `exists_pos_weighted_of_construction`. -/
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
  hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm
  hbeat : Bm < 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)


end CircleMethod

end
