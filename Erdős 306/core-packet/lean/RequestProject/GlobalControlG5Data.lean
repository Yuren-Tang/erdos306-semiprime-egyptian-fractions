/-
G5 helper layer for `GlobalControl`.

This file keeps the segment-encoding data spaces outside the large
`GlobalControl.lean` file so that the G5 proof can be developed incrementally
against the cached core.
-/
import RequestProject.GlobalControl

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### G5 data spaces (note 40 §3) -/

/-- Admissible hot sets: subsets of `[k₀,K]` whose forcing floors have total
    cost at most `R`. -/
def admH (BS : BlockSystem) (c2 R : ℝ) : Finset (Finset ℕ) :=
  (Finset.Icc BS.k0 BS.K).powerset.filter
    (fun H => ∑ k ∈ H, Rw c2 k ≤ R)

/-- Admissible boundary sets: subsets of `[k₀,K)` whose boundary penalties have
    total cost at most `R`. -/
def admB (BS : BlockSystem) (e0 R : ℝ) : Finset (Finset ℕ) :=
  (Finset.Ico BS.k0 BS.K).powerset.filter
    (fun B => ∑ k ∈ B, Pifloor BS e0 k ≤ R)

/-- Total shell functions obtained from dependent shell data on `[k₀,K]`,
    extended by zero outside the block interval. -/
def shellCarrier (BS : BlockSystem) (R : ℝ) : Finset (ℕ → ℕ) :=
  ((Finset.Icc BS.k0 BS.K).pi
      (fun _ => Finset.range (Nat.floor R + 1))).image
    (fun v k => if h : k ∈ Finset.Icc BS.k0 BS.K then v k h else 0)

/-- Admissible total shell functions, capped by `⌊R⌋₊`, with total shell mass at
    most `R` and with the hot-consistency condition needed by `hot_factor`. -/
def admShells (BS : BlockSystem) (c2 R : ℝ) (H : Finset ℕ) : Finset (ℕ → ℕ) :=
  (shellCarrier BS R).filter
    (fun v =>
      (∑ k ∈ Finset.Icc BS.k0 BS.K, (v k : ℝ)) ≤ R ∧
      ∀ k, k ∈ Finset.Icc BS.k0 BS.K → k ∈ H → Rw c2 k ≤ (v k : ℝ) + 1)

/-- The initial segment label window, carrying the sole global `sigmaCtrl`
    factor in G5. -/
def L0 (BS : BlockSystem) (R : ℝ) : ℤ :=
  ⌈(7 : ℝ) * Real.sqrt R / sigmaP (BS.P BS.k0)⌉

/-- Admissible labels at a segment start.  The initial segment has the
    `sqrt(R)/sigma` window; all later starts use the local `labelRange`. -/
def labelFin (BS : BlockSystem) (c2 R : ℝ) (k : ℕ) : Finset ℤ :=
  if k = BS.k0 then
    Finset.Icc (-(L0 BS R)) (L0 BS R)
  else
    Finset.Icc (-(labelRange c2 k)) (labelRange c2 k)

/-- Total label functions obtained from segment-start label data, extended by
    zero outside the segment-start set. -/
def admLabels (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) : Finset (ℕ → ℤ) :=
  ((segStarts BS H B).pi (fun k => labelFin BS c2 R k)).image
    (fun ell k => if h : k ∈ segStarts BS H B then ell k h else 0)

end GlobalControl
