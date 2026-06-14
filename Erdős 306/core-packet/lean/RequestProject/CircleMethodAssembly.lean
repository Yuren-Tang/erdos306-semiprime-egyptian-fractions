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

end CircleMethod

end
