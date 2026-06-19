import RequestProject.R2MinorEndgameFrequency

open Finset BigOperators GlobalControl
open scoped Classical

noncomputable section

namespace CircleMethod

/-- Frequency `h` as a faithful block-support assignment. -/
def freqAssignmentOf {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (h : ℕ) : GlobalAssignment D.BS :=
  fun p => (h : ZMod p.1)

/-- Frequencies not lying over a global-control main arc go to the block lane. -/
def mainArcBlockSet {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C : ℝ) (MA : MainArcFields D.E W.theta b D.L N) : Finset ℕ :=
  MA.Sm.filter (fun h => freqAssignmentOf D h ∉ mainArc D.BS C)

/-- Frequencies lying over a global-control main arc go to the extra lane. -/
def mainArcExtraSet {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C : ℝ) (MA : MainArcFields D.E W.theta b D.L N) : Finset ℕ :=
  MA.Sm.filter (fun h => freqAssignmentOf D h ∈ mainArc D.BS C)

/-- The block/extra split defined by global-control main-arc membership covers
all minor frequencies. -/
def mainArcClassificationData {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C : ℝ) : R2MinorClassificationData D W N where
  Sblock := mainArcBlockSet D W N C
  Sextra := mainArcExtraSet D W N C
  hcover := by
    intro MA h hh
    by_cases hmain : freqAssignmentOf D h ∈ mainArc D.BS C
    · exact Finset.mem_union_right _ (by simp [mainArcExtraSet, hh, hmain])
    · exact Finset.mem_union_left _ (by simp [mainArcBlockSet, hh, hmain])

/-- Label selected from the global-control main-arc witness, with fallback `0`
off the extra lane. -/
def mainArcWitnessLabel {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (C : ℝ) (h : ℕ) : ℤ :=
  if hmain : freqAssignmentOf D h ∈ mainArc D.BS C then
    Classical.choose hmain
  else 0

lemma nat_eq_of_mem_range_and_zmod_eq {L h k : ℕ}
    (hh : h ∈ Finset.range L) (hk : k ∈ Finset.range L)
    (heq : (h : ZMod L) = (k : ZMod L)) : h = k := by
  rw [Finset.mem_range] at hh hk
  have hmod := (ZMod.natCast_eq_natCast_iff' h k L).mp heq
  rwa [Nat.mod_eq_of_lt hh, Nat.mod_eq_of_lt hk] at hmod

lemma mainArcFields_mem_range_of_mem_SM
    {E : Finset ℕ} {theta : ℕ → ℝ} {b L : ℕ} {N : ℤ}
    (MA : MainArcFields E theta b L N) {h : ℕ} (hh : h ∈ MA.SM) :
    h ∈ Finset.range L := by
  have hmem : h ∈ MA.SM ∪ MA.Sm := Finset.mem_union_left _ hh
  rwa [← MA.hpart] at hmem

lemma mainArcFields_mem_range_of_mem_Sm
    {E : Finset ℕ} {theta : ℕ → ℝ} {b L : ℕ} {N : ℤ}
    (MA : MainArcFields E theta b L N) {h : ℕ} (hh : h ∈ MA.Sm) :
    h ∈ Finset.range L := by
  have hmem : h ∈ MA.SM ∪ MA.Sm := Finset.mem_union_right _ hh
  rwa [← MA.hpart] at hmem

lemma zmod_eq_label_of_mainArcFields_hmod
    {E : Finset ℕ} {theta : ℕ → ℝ} {b L : ℕ} {N : ℤ}
    (MA : MainArcFields E theta b L N) {h : ℕ} (hh : h ∈ MA.SM) :
    (h : ZMod L) = (MA.lbl h : ZMod L) := by
  have hmod := MA.hmod h hh
  have key : ((h : ℤ) : ZMod L) = (MA.lbl h : ZMod L) := by
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    simpa [neg_sub] using (dvd_neg).mpr hmod
  rwa [Int.cast_natCast] at key

/-- Main-arc membership of an extra frequency supplies exactly the integer
block-label data needed by the multi-gadget extra-minor reservoir. -/
def intFrequencyLabelData_of_mainArcClassification
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ) (C : ℝ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (hlabelRange : ∀ {m : ℤ}, |(m : ℝ)| ≤ C / sigmaCtrl D.BS →
      m ∈ Finset.Icc (-N) N) :
    R2ExtraIntFrequencyLabelData D W N MA
      ((mainArcClassificationData D W N C).Sblock MA)
      ((mainArcClassificationData D W N C).Sextra MA) where
  mfun := mainArcWitnessLabel D C
  hblock := by
    intro h hh s hs
    rw [mem_extraMinorPart] at hh
    have hmain : freqAssignmentOf D h ∈ mainArc D.BS C := by
      have h22 := hh.2.2
      simp only [mainArcClassificationData, mainArcExtraSet, Finset.mem_filter] at h22
      exact h22.2
    have hspec := Classical.choose_spec hmain
    have hcoord := hspec.2 ⟨s, hs⟩
    simpa [mainArcWitnessLabel, hmain, freqAssignmentOf] using hcoord
  hnotGlobal := by
    intro h hh hglob
    rw [mem_extraMinorPart] at hh
    have hSm : h ∈ MA.Sm := hh.1
    have hnotBlock : h ∉ (mainArcClassificationData D W N C).Sblock MA := hh.2.1
    have hmain : freqAssignmentOf D h ∈ mainArc D.BS C := by
      have h22 := hh.2.2
      simp only [mainArcClassificationData, mainArcExtraSet, Finset.mem_filter] at h22
      exact h22.2
    have hspec := Classical.choose_spec hmain
    let m : ℤ := mainArcWitnessLabel D C h
    have hmdef : m = Classical.choose hmain := by
      simp [m, mainArcWitnessLabel, hmain]
    have hmrange : m ∈ Finset.Icc (-N) N := by
      rw [hmdef]
      exact hlabelRange hspec.1
    obtain ⟨h0, hh0, hlbl⟩ := MA.hsurj m hmrange
    have hhRange := mainArcFields_mem_range_of_mem_Sm MA hSm
    have hh0Range := mainArcFields_mem_range_of_mem_SM MA hh0
    have h0mod : (h0 : ZMod D.L) = (m : ZMod D.L) := by
      have hz := zmod_eq_label_of_mainArcFields_hmod MA hh0
      simpa [hlbl] using hz
    have heq : h = h0 :=
      nat_eq_of_mem_range_and_zmod_eq hhRange hh0Range (hglob.trans h0mod.symm)
    have hmemSM : h ∈ MA.SM := by
      simpa [heq] using hh0
    have hdisj := MA.hdisj
    rw [Finset.disjoint_left] at hdisj
    exact hdisj hmemSM hSm

end CircleMethod

end
