import RequestProject.GlobalControl.Encoding.Fibers
import RequestProject.GlobalControl.LevelSetParameters

/-!
# Level-set encoding cover

The canonical finite encoding of a global assignment and the resulting
four-parameter fiber cover.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### Encoder membership (note 41 §§3,5) -/

/-- The segment start of a cold block in `[k₀,K]` is itself a segment start. -/
lemma segStart_mem (BS : BlockSystem) (H B : Finset ℕ) :
    ∀ (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → k ∉ H →
      RequestProject.segmentStart BS.k0 H B k ∈ RequestProject.segmentStarts BS.k0 BS.K H B := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hk2 hkH
    rw [RequestProject.segmentStart]
    by_cases hle : k ≤ BS.k0
    · -- then k = k0
      have hk0 : k = BS.k0 := le_antisymm hle hk1
      simp only [hle, if_true]
      rw [RequestProject.segmentStarts, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
      refine ⟨⟨⟨le_rfl, ?_⟩, ?_⟩, Or.inl rfl⟩
      · exact le_trans hk1 hk2 |>.trans_eq rfl |>.trans (by omega) |>.trans_eq rfl
      · intro hk0H; exact hkH (hk0 ▸ hk0H)
    · push Not at hle
      by_cases hb : (k - 1) ∈ H ∨ (k - 1) ∈ B
      · simp only [Nat.not_le.mpr hle, if_false, hb, if_true]
        rw [RequestProject.segmentStarts, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
        exact ⟨⟨⟨hk1, hk2⟩, hkH⟩, Or.inr hb⟩
      · simp only [Nat.not_le.mpr hle, if_false, hb, if_false]
        exact ih (k - 1) (by omega) (by omega) (by omega)
          (fun h => hb (Or.inl h))

/-- Zero-extension of the shell data outside `[k₀,K]`, matching the
    image form of `admShells`. -/
def extShell (BS : BlockSystem) (a : GlobalAssignment BS) : ℕ → ℕ :=
  fun k => if k ∈ Finset.Icc BS.k0 BS.K then shellVec BS a k else 0

/-- Zero-extension of the label data outside `RequestProject.segmentStarts H B`, matching the
    image form of `admLabels`. -/
def extLabel (BS : BlockSystem) (a : GlobalAssignment BS) (H B : Finset ℕ) : ℕ → ℤ :=
  fun k => if k ∈ RequestProject.segmentStarts BS.k0 BS.K H B then coldLabel BS a k else 0

/-- The encoder lands `a` in the fiber of its own zero-extended invariants.
    The cold-class lower bound is supplied as a hypothesis (discharged from the
    cold-block facts). -/
lemma mem_fiber_encode (BS : BlockSystem) (c2 _R : ℝ) (a : GlobalAssignment BS)
    (hcold : ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (classCount BS a k (coldLabel BS a k) : ℝ)) :
    a ∈ fiber BS (hotSet BS c2 a) (boundarySet BS c2 a)
        (extShell BS a) (extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a)) := by
  rw [fiber, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro k hk
  have hkmem := hk
  rw [Finset.mem_Icc] at hk
  refine ⟨?_, ?_⟩
  · -- energy shell: blockEnergy ≤ extShell + 1 = ⌊blockEnergy⌋ + 1
    rw [extShell, if_pos hkmem, shellVec]
    exact le_of_lt (Nat.lt_floor_add_one _)
  · intro hkH
    have hcoldk : k ∉ hotSet BS c2 a := hkH
    -- the fiber evaluates extLabel at the segment start, which lies in RequestProject.segmentStarts
    have hsmem := segStart_mem BS (hotSet BS c2 a) (boundarySet BS c2 a) k hk.1 hk.2 hkH
    rw [extLabel, if_pos hsmem]
    have heq := coldLabel_eq_segStart BS c2 a k hk.1 hk.2 hcoldk
    rw [classCount, ← heq]
    exact hcold k hk.1 hk.2 hcoldk

/-- **The four-level cover bound (note 41 §2).**  The level set injects into the
    union of fibers indexed by admissible `(H,B,v,ℓ)`; hence its cardinality is
    at most the four-fold sum of fiber cardinalities.  Parametrized by the four
    admissibility facts (proved separately) and the cold-class bound. -/
lemma cover_card_le (BS : BlockSystem) (c2 e0 R : ℝ)
    (hadmH : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        hotSet BS c2 a ∈ admH BS c2 R)
    (hadmB : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        boundarySet BS c2 a ∈ admB BS e0 R)
    (hadmS : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        extShell BS a ∈ admShells BS c2 R (hotSet BS c2 a))
    (hadmL : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a)
          ∈ admLabels BS c2 R (hotSet BS c2 a) (boundarySet BS c2 a))
    (hcold : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
        (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
          (classCount BS a k (coldLabel BS a k) : ℝ)) :
    (Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card ≤
      ∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
        ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card := by
  have hcover :
      (Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)) ⊆
        (admH BS c2 R).biUnion (fun H =>
          (admB BS e0 R).biUnion (fun B =>
            (admShells BS c2 R H).biUnion (fun v =>
              (admLabels BS c2 R H B).biUnion (fun ℓ => fiber BS H B v ℓ)))) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨_, hR⟩ := ha
    rw [Finset.mem_biUnion]
    refine ⟨hotSet BS c2 a, hadmH a hR, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨boundarySet BS c2 a, hadmB a hR, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨extShell BS a, hadmS a hR, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a), hadmL a hR,
      mem_fiber_encode BS c2 R a (hcold a hR)⟩
  calc
    (Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card
        ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ H ∈ admH BS c2 R,
          ((admB BS e0 R).biUnion (fun B =>
            (admShells BS c2 R H).biUnion (fun v =>
              (admLabels BS c2 R H B).biUnion (fun ℓ => fiber BS H B v ℓ)))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R,
          ((admShells BS c2 R H).biUnion (fun v =>
            (admLabels BS c2 R H B).biUnion (fun ℓ => fiber BS H B v ℓ))).card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ((admLabels BS c2 R H B).biUnion (fun ℓ => fiber BS H B v ℓ)).card :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le))
    _ ≤ ∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card :=
        Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun _ _ =>
          Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)))

end GlobalControl

end
