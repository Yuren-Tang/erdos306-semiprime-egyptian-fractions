import RequestProject.R2MinorEndgameMultiGadget
import RequestProject.R2ExtraFrequencyChoice

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 minor endgame from extra-frequency labels

This leaf replaces the abstract multi-gadget reservoir field by the concrete
CRT label data proved in `R2ExtraFrequencyChoice`.
-/

/-- Endgame lanes where the extra-minor side is supplied by block-label data and
gadget reservoirs, rather than by an already-assembled
`R2MultiGadgetReservoir`. -/
structure R2MinorEndgameFrequencyLanes
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra η Ctail ρ Cextra : ℝ)
    (Cls : R2MinorClassificationData D W N) where
  component : R2ComponentScaleCoreSupply D N ρ
  hbpos : 0 < b
  hsqfree : Squarefree b
  hcoverR : CoversPrimeDivisors D.R b
  hcopBlock : BlockSupportCoprimeWith D.BS b
  block : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2BlockFiberTailData D W N MA (Cls.Sblock MA) Bblock η Ctail
  label : ∀ MA : MainArcFields D.E W.theta b D.L N,
    R2ExtraFrequencyLabelData D W N MA (Cls.Sblock MA) (Cls.Sextra MA)
  Gset : (MainArcFields D.E W.theta b D.L N) → ℕ → Finset ℕ
  hSmem : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∀ h ∈ extraMinorPart MA.Sm (Cls.Sblock MA) (Cls.Sextra MA),
      Gset MA h ⊆ D.S
  hm_small : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∀ h ∈ extraMinorPart MA.Sm (Cls.Sblock MA) (Cls.Sextra MA),
      ∀ s ∈ Gset MA h,
        2 * |((label MA).mfun h : ℤ)| < (s : ℤ)
  hcard : ∀ MA : MainArcFields D.E W.theta b D.L N,
      ((extraMinorPart MA.Sm (Cls.Sblock MA) (Cls.Sextra MA)).card : ℝ) *
          Cextra ≤ Bextra
  hpt : ∀ MA : MainArcFields D.E W.theta b D.L N,
    ∀ h ∈ extraMinorPart MA.Sm (Cls.Sblock MA) (Cls.Sextra MA),
      (Real.sqrt (1 - (8 / 9) /
        (((r2ExtraSiblingChoice_of_labelData D W N MA (Cls.Sblock MA)
          (Cls.Sextra MA) (label MA) hbpos
          hsqfree hcoverR hcopBlock).rfun h : ℝ) ^ 2))) ^
            (Gset MA h).card ≤ Cextra

/-- Frequency-label lanes produce the already-built multi-gadget lane package. -/
def R2MinorEndgameFrequencyLanes.toMultiGadget
    {T : Finset ℕ} {b : ℕ}
    {D : R2ConcreteData T b} {W : R2ConcreteData.Weights D} {N : ℤ}
    {Bblock Bextra η Ctail ρ Cextra : ℝ}
    {Cls : R2MinorClassificationData D W N}
    (L : R2MinorEndgameFrequencyLanes D W N Bblock Bextra η Ctail ρ Cextra Cls) :
    R2MinorEndgameMultiGadgetLanes D W N Bblock Bextra η Ctail ρ Cls where
  component := L.component
  block := L.block
  extra := by
    intro MA
    exact r2MultiGadgetReservoir_of_extraFrequencyLabelData D W N MA
      (Cls.Sblock MA) (Cls.Sextra MA) Cextra Bextra (L.label MA) (L.Gset MA)
      L.hbpos L.hsqfree L.hcoverR L.hcopBlock L.component.hSblock
      (L.hSmem MA) (L.hm_small MA) (L.hcard MA) (L.hpt MA)

/-- G7 plus block lanes and extra-frequency label lanes produce minor-ready
data. -/
theorem exists_r2_minorReady_from_frequency_lanes
    (eps : ℝ) (heps : 0 < eps) (η : ℝ) (hη : 0 < η) :
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ {T : Finset ℕ} {b : ℕ}
      (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
      (Ablock Aextra ρ Cextra : ℝ)
      (Cls : R2MinorClassificationData D W N),
      k0min ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameFrequencyLanes D W N
        (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS)
        η Ctail ρ Cextra Cls →
      Ablock + Aextra < r2MinorMainCtrlConstant →
      Nonempty (R2MinorReadyData D W N) := by
  obtain ⟨k0min, Ctail, hCtail, hminor⟩ :=
    exists_r2_minorReady_from_multiGadget_lanes eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro T b D W N Ablock Aextra ρ Cextra Cls hk0 hadm L hscaled
  exact hminor D W N Ablock Aextra ρ Cls hk0 hadm L.toMultiGadget hscaled

end CircleMethod

end
