import RequestProject.R2ExtraReservoirUniformBudget
import RequestProject.R2ExtraCRTSibling

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-frequency choice task

This leaf bridges the finite CRT-selection step before the multi-gadget
reservoir.  It was originally isolated as an Aristotle-sized task; the proofs
below are now complete.

The goal is to bridge the last CRT-selection step before the multi-gadget
reservoir.  For each extra-minor frequency `h`, we are given its block label
`mfun h`: it agrees with `h` on every block-support prime, but is not globally
congruent to `h` modulo the full R2 period.  Since `b` is squarefree and `D.R`
covers the prime divisors of `b`, `R2ExtraCRTSibling.exists_R_mismatch...`
chooses a prime `r ∈ D.R` where `h` and the label differ.  Together with
preselected gadget sets `Gset h ⊆ D.S`, this should produce exactly the
`R2ExtraPreparedReservoirChoice` needed downstream.
-/

/-- Block-label data for the extra-minor frequencies. -/
structure R2ExtraFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ) where
  mfun : ℕ → ℕ
  hblock : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ blockSupport D.BS,
    (h : ZMod s) = (mfun h : ZMod s)
  hnotGlobal : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod D.L) ≠ (mfun h : ZMod D.L)

/-- From block-label data, every extra frequency has an `R`-prime sibling where
the global congruence fails. -/
theorem exists_r_sibling_of_extraFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (X : R2ExtraFrequencyLabelData D W N MA Sblock Sextra)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b) :
    ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      ∃ r ∈ D.R, Nat.Prime r ∧ r ∣ b ∧
        (h : ZMod r) ≠ (X.mfun h : ZMod r) := by
  intro h hh
  exact exists_R_mismatch_of_block_eq_not_global D.BS D.R b D.L h (X.mfun h)
    (by rfl) hbpos hsqfree hcover hcop (X.hblock h hh) (X.hnotGlobal h hh)

/-- Package the noncomputable sibling choice as functions `rfun`, with its
membership and mismatch certificates. -/
structure R2ExtraSiblingChoice
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (X : R2ExtraFrequencyLabelData D W N MA Sblock Sextra) where
  rfun : ℕ → ℕ
  hRmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∈ D.R
  hrprime : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Nat.Prime (rfun h)
  hrdvd : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, rfun h ∣ b
  hm_r : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod (rfun h)) ≠ (X.mfun h : ZMod (rfun h))

/-- Choose an `R`-prime sibling for every extra frequency. -/
def r2ExtraSiblingChoice_of_labelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (X : R2ExtraFrequencyLabelData D W N MA Sblock Sextra)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b) :
    R2ExtraSiblingChoice D W N MA Sblock Sextra X := by
  classical
  let extra := extraMinorPart MA.Sm Sblock Sextra
  have hex :
      ∀ h ∈ extra, ∃ r, r ∈ D.R ∧ Nat.Prime r ∧ r ∣ b ∧
        (h : ZMod r) ≠ (X.mfun h : ZMod r) := by
    intro h hh
    obtain ⟨r, hr, hprime, hdvd, hneq⟩ :=
      exists_r_sibling_of_extraFrequencyLabelData D W N MA Sblock Sextra X
        hbpos hsqfree hcover hcop h hh
    exact ⟨r, hr, hprime, hdvd, hneq⟩
  let rfun : ℕ → ℕ := fun h =>
    if hh : h ∈ extra then Classical.choose (hex h hh) else 0
  refine {
    rfun := rfun
    hRmem := ?_
    hrprime := ?_
    hrdvd := ?_
    hm_r := ?_
  }
  · intro h hh
    have hchoose := Classical.choose_spec (hex h hh)
    simpa [rfun, extra, hh] using hchoose.1
  · intro h hh
    have hchoose := Classical.choose_spec (hex h hh)
    simpa [rfun, extra, hh] using hchoose.2.1
  · intro h hh
    have hchoose := Classical.choose_spec (hex h hh)
    simpa [rfun, extra, hh] using hchoose.2.2.1
  · intro h hh
    have hchoose := Classical.choose_spec (hex h hh)
    dsimp [rfun]
    rw [dif_pos (show h ∈ extra from hh)]
    exact hchoose.2.2.2

/-- Final bridge: block-label data plus gadget sets and a uniform damping budget
produce the prepared reservoir choice. -/
def preparedChoice_of_extraFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (C Bextra : ℝ)
    (X : R2ExtraFrequencyLabelData D W N MA Sblock Sextra)
    (Gset : ℕ → Finset ℕ)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b)
    (hSblock : D.S ⊆ blockSupport D.BS)
    (hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S)
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      2 * |(X.mfun h : ℤ)| < (s : ℤ))
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) /
        (((r2ExtraSiblingChoice_of_labelData D W N MA Sblock Sextra X
          hbpos hsqfree hcover hcop).rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    R2ExtraPreparedReservoirChoice D W N MA Sblock Sextra Bextra := by
  classical
  let Sibling :=
    r2ExtraSiblingChoice_of_labelData D W N MA Sblock Sextra X
      hbpos hsqfree hcover hcop
  refine preparedChoice_of_pointwise_budget D W N MA Sblock Sextra C Bextra
    Sibling.rfun Gset (fun h => (X.mfun h : ℤ))
    Sibling.hRmem hSmem ?_ ?_ hm_small hcard ?_
  · intro h hh s hs
    have hblock := X.hblock h hh s (hSblock (hSmem h hh hs))
    simpa using hblock
  · intro h hh
    simpa [Sibling] using Sibling.hm_r h hh
  · intro h hh
    simpa [Sibling] using hpt h hh

/-- Same bridge, directly producing the downstream multi-gadget reservoir. -/
def r2MultiGadgetReservoir_of_extraFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (C Bextra : ℝ)
    (X : R2ExtraFrequencyLabelData D W N MA Sblock Sextra)
    (Gset : ℕ → Finset ℕ)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b)
    (hSblock : D.S ⊆ blockSupport D.BS)
    (hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S)
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      2 * |(X.mfun h : ℤ)| < (s : ℤ))
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) /
        (((r2ExtraSiblingChoice_of_labelData D W N MA Sblock Sextra X
          hbpos hsqfree hcover hcop).rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    R2MultiGadgetReservoir D W N MA Sblock Sextra Bextra := by
  exact r2MultiGadgetReservoir_of_preparedChoice D W N MA Sblock Sextra Bextra
    (preparedChoice_of_extraFrequencyLabelData D W N MA Sblock Sextra C Bextra X Gset
      hbpos hsqfree hcover hcop hSblock hSmem hm_small hcard hpt)

end CircleMethod

end
