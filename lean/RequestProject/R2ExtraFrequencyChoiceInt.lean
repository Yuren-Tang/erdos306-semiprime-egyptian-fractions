import RequestProject.R2ExtraFrequencyChoice

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# Integer-label extra-frequency choice

The main-arc labels are integers.  This leaf mirrors
`R2ExtraFrequencyChoice`, but keeps the labels in `ℤ` all the way to the
multi-gadget reservoir.
-/

/-- Integer block-label data for the extra-minor frequencies. -/
structure R2ExtraIntFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ) where
  mfun : ℕ → ℤ
  hblock : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ blockSupport D.BS,
    (h : ZMod s) = (mfun h : ZMod s)
  hnotGlobal : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
    (h : ZMod D.L) ≠ (mfun h : ZMod D.L)

/-- Choose an `R`-prime sibling for every integer-labelled extra frequency. -/
def r2ExtraSiblingChoice_of_intLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (X : R2ExtraIntFrequencyLabelData D W N MA Sblock Sextra)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b) :
    R2ExtraSiblingChoice D W N MA Sblock Sextra
      { mfun := fun h => Int.toNat (X.mfun h % D.L)
        hblock := by
          intro h hh s hs
          have hmod := X.hblock h hh s hs
          have hsdvd : (s : ℤ) ∣ (D.L : ℤ) := by
            have hsprod : s ∣ ∏ t ∈ blockSupport D.BS, t := Finset.dvd_prod_of_mem id hs
            have hsL : s ∣ D.L := by
              rw [R2ConcreteData.L]
              exact dvd_mul_of_dvd_right hsprod b
            exact_mod_cast hsL
          have hrep : ((Int.toNat (X.mfun h % D.L) : ℤ) : ZMod s) =
              ((X.mfun h % D.L : ℤ) : ZMod s) := by
            rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
              have hLpos : 0 < D.L := by
                rw [R2ConcreteData.L]
                positivity
              exact_mod_cast hLpos.ne'))]
          rw [← hrep]
          have hm : (X.mfun h % D.L : ℤ) ≡ X.mfun h [ZMOD s] := by
            have hDL : (X.mfun h % D.L : ℤ) ≡ X.mfun h [ZMOD D.L] := by
              simpa [Int.ModEq] using (Int.emod_emod_of_dvd (X.mfun h) hsdvd)
            exact Int.ModEq.of_dvd hDL hsdvd
          have hcast := (ZMod.intCast_eq_intCast_iff _ _ s).mpr hm
          rw [hcast]
          exact hmod
        hnotGlobal := by
          intro h hh hglob
          apply X.hnotGlobal h hh
          have hrep : ((Int.toNat (X.mfun h % D.L) : ℤ) : ZMod D.L) =
              ((X.mfun h % D.L : ℤ) : ZMod D.L) := by
            rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
              have hLpos : 0 < D.L := by
                rw [R2ConcreteData.L]
                positivity
              exact_mod_cast hLpos.ne'))]
          have hcast : ((Int.toNat (X.mfun h % D.L) : ℤ) : ZMod D.L) =
              (X.mfun h : ZMod D.L) := by
            rw [hrep]
            exact ZMod.intCast_mod (X.mfun h) D.L
          rwa [hcast] at hglob } hbpos hsqfree hcover hcop

/-- Integer-label data plus gadget sets and a uniform damping budget produce the
prepared reservoir choice. -/
def preparedChoice_of_intExtraFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (C Bextra : ℝ)
    (X : R2ExtraIntFrequencyLabelData D W N MA Sblock Sextra)
    (Gset : ℕ → Finset ℕ)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b)
    (hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S)
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      2 * |X.mfun h| < (s : ℤ))
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) /
        (((r2ExtraSiblingChoice_of_intLabelData D W N MA Sblock Sextra X
          hbpos hsqfree hcover hcop).rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    R2ExtraPreparedReservoirChoice D W N MA Sblock Sextra Bextra := by
  classical
  let Sibling :=
    r2ExtraSiblingChoice_of_intLabelData D W N MA Sblock Sextra X
      hbpos hsqfree hcover hcop
  refine preparedChoice_of_pointwise_budget D W N MA Sblock Sextra C Bextra
    Sibling.rfun Gset X.mfun Sibling.hRmem hSmem X.hblock ?_ hm_small hcard ?_
  · intro h hh hEq
    have hNat := Sibling.hm_r h hh
    apply hNat
    have hrdvdL : Sibling.rfun h ∣ D.L := by
      rw [R2ConcreteData.L]
      exact dvd_mul_of_dvd_left (Sibling.hrdvd h hh) (∏ s ∈ blockSupport D.BS, s)
    have hrdvdLZ : (Sibling.rfun h : ℤ) ∣ (D.L : ℤ) := by exact_mod_cast hrdvdL
    have hrep : ((Int.toNat (X.mfun h % D.L) : ℤ) : ZMod (Sibling.rfun h)) =
        ((X.mfun h % D.L : ℤ) : ZMod (Sibling.rfun h)) := by
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
        have hLpos : 0 < D.L := by
          rw [R2ConcreteData.L]
          positivity
        exact_mod_cast hLpos.ne'))]
    have hcast : ((Int.toNat (X.mfun h % D.L) : ℤ) : ZMod (Sibling.rfun h)) =
        (X.mfun h : ZMod (Sibling.rfun h)) := by
      rw [hrep]
      have hm : (X.mfun h % D.L : ℤ) ≡ X.mfun h [ZMOD Sibling.rfun h] := by
        have hDL : (X.mfun h % D.L : ℤ) ≡ X.mfun h [ZMOD D.L] := by
          simpa [Int.ModEq] using (Int.emod_emod_of_dvd (X.mfun h) hrdvdLZ)
        exact Int.ModEq.of_dvd hDL hrdvdLZ
      exact (ZMod.intCast_eq_intCast_iff _ _ (Sibling.rfun h)).mpr hm
    rw [hcast]
    exact hEq
  · intro h hh
    simpa [Sibling] using hpt h hh

/-- Direct downstream multi-gadget reservoir from integer-labelled frequency
data. -/
def r2MultiGadgetReservoir_of_intExtraFrequencyLabelData
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D)
    (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock Sextra : Finset ℕ)
    (C Bextra : ℝ)
    (X : R2ExtraIntFrequencyLabelData D W N MA Sblock Sextra)
    (Gset : ℕ → Finset ℕ)
    (hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors D.R b)
    (hcop : BlockSupportCoprimeWith D.BS b)
    (hSmem : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, Gset h ⊆ D.S)
    (hm_small : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra, ∀ s ∈ Gset h,
      2 * |X.mfun h| < (s : ℤ))
    (hcard :
      ((extraMinorPart MA.Sm Sblock Sextra).card : ℝ) * C ≤ Bextra)
    (hpt : ∀ h ∈ extraMinorPart MA.Sm Sblock Sextra,
      (Real.sqrt (1 - (8 / 9) /
        (((r2ExtraSiblingChoice_of_intLabelData D W N MA Sblock Sextra X
          hbpos hsqfree hcover hcop).rfun h : ℝ) ^ 2))) ^ (Gset h).card ≤ C) :
    R2MultiGadgetReservoir D W N MA Sblock Sextra Bextra := by
  exact r2MultiGadgetReservoir_of_preparedChoice D W N MA Sblock Sextra Bextra
    (preparedChoice_of_intExtraFrequencyLabelData D W N MA Sblock Sextra C Bextra
      X Gset hbpos hsqfree hcover hcop hSmem hm_small hcard hpt)

end CircleMethod

end
