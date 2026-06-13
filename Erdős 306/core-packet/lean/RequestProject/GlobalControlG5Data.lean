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

/-! ### Generic covering bound (note 41 §2) -/

/-- If `S` is covered by the indexed family `F` over `I`, then
    `|S| ≤ ∑_{i∈I} |F i|`.  Pure finite combinatorics. -/
lemma card_le_sum_fibers_of_cover {α ι : Type*} [DecidableEq α]
    (S : Finset α) (I : Finset ι) (F : ι → Finset α)
    (hcover : S ⊆ I.biUnion F) :
    S.card ≤ ∑ i ∈ I, (F i).card :=
  le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le

/-! ### Encoder membership (note 41 §§3,5) -/

/-- The segment start of a cold block in `[k₀,K]` is itself a segment start. -/
lemma segStart_mem (BS : BlockSystem) (H B : Finset ℕ) :
    ∀ (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → k ∉ H →
      segStart BS H B k ∈ segStarts BS H B := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hk2 hkH
    rw [segStart]
    by_cases hle : k ≤ BS.k0
    · -- then k = k0
      have hk0 : k = BS.k0 := le_antisymm hle hk1
      simp only [hle, if_true]
      rw [segStarts, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
      refine ⟨⟨⟨le_rfl, ?_⟩, ?_⟩, Or.inl rfl⟩
      · exact le_trans hk1 hk2 |>.trans_eq rfl |>.trans (by omega) |>.trans_eq rfl
      · intro hk0H; exact hkH (hk0 ▸ hk0H)
    · push_neg at hle
      by_cases hb : (k - 1) ∈ H ∨ (k - 1) ∈ B
      · simp only [Nat.not_le.mpr hle, if_false, hb, if_true]
        rw [segStarts, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
        exact ⟨⟨⟨hk1, hk2⟩, hkH⟩, Or.inr hb⟩
      · simp only [Nat.not_le.mpr hle, if_false, hb, if_false]
        exact ih (k - 1) (by omega) (by omega) (by omega)
          (fun h => hb (Or.inl h))

/-- The encoder lands `a` in the fiber of its own invariants
    `(hotSet, boundarySet, shellVec, coldLabel)`.  The cold-class lower bound
    is supplied as a hypothesis (discharged from the cold-block facts). -/
lemma mem_fiber_encode (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (hcold : ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (classCount BS a k (coldLabel BS a k) : ℝ)) :
    a ∈ fiber BS (hotSet BS c2 a) (boundarySet BS c2 a)
        (shellVec BS a) (coldLabel BS a) := by
  rw [fiber, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro k hk
  rw [Finset.mem_Icc] at hk
  refine ⟨?_, ?_⟩
  · -- energy shell: blockEnergy ≤ ⌊blockEnergy⌋ + 1
    rw [shellVec]
    exact le_of_lt (Nat.lt_floor_add_one _)
  · intro hkH
    -- k ∉ hotSet ⟹ ¬ isHot
    have hcoldk : k ∉ hotSet BS c2 a := hkH
    -- rewrite the segment-start label to the block's own label
    have heq := coldLabel_eq_segStart BS c2 a k hk.1 hk.2 hcoldk
    rw [classCount, ← heq]
    exact hcold k hk.1 hk.2 hcoldk
