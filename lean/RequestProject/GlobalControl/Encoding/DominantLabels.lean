import RequestProject.Core.IntervalSegmentation
import RequestProject.GlobalControl.Encoding.BlockData
import RequestProject.LocalEnergy.DominantLabel

/-!
# Dominant labels across global block segments

Canonical dominant labels, mismatch boundaries, cold-block dominance, and
constancy of labels along cold segments.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- The dominant label of a block, and `0` when no dominant label exists. -/
def coldLabel (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℤ :=
  if h : LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1 / 4)
  then h.choose else 0

/-- Mismatch boundary: two consecutive cold blocks with distinct labels. -/
def boundarySet (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Ico BS.k0 BS.K).filter (fun k =>
    ¬ isHot BS c2 a k ∧ ¬ isHot BS c2 a (k+1) ∧
    coldLabel BS a k ≠ coldLabel BS a (k+1))
/-! ## Dominant labels -/

/-
When a dominant label exists for block `k`,
    `coldLabel` is one such label: it satisfies the size+class property.
-/
lemma coldLabel_spec (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (h : LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1 / 4)) :
    |coldLabel BS a k| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p
            = ((coldLabel BS a k : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
  simpa [coldLabel, h] using h.choose_spec

/-
Uniqueness: the dominant label is unique, so
    any `m` with the size+class property at a cold block equals `coldLabel`.
-/
lemma coldLabel_eq_of_dominant (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hX : 4 ≤ (2:ℕ) ^ k)
    (hN : 4 ≤ (BS.P k).card)
    (m : ℤ) (hm : |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2)
    (hclass : (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (((BS.P k).attach.filter
        (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)) :
    coldLabel BS a k = m := by
  have hdom : LocalEnergy.HasDominantLabel
      (2 ^ k) (BS.P k) (restrict BS a k) (1 / 4) :=
    ⟨m, hm, hclass⟩
  have hcold := coldLabel_spec BS a k hdom
  apply LocalEnergy.dominant_label_unique (2 ^ k) hX (BS.P k)
    (fun p hp => ⟨BS.hprime k p hp, by
      exact ⟨by linarith [BS.hwindow k p hp],
        by linarith [BS.hwindow k p hp, pow_succ' 2 k]⟩⟩)
    hN (1 / 4) (by positivity) (by norm_num) (restrict BS a k)
    (coldLabel BS a k) m
  · simpa using hcold.1
  · simpa using hm
  · exact hcold.2
  · exact hclass

/-
Contrapositive of
    `nondominant_energy_lower_bound` at `ρ = 1/4`: with `c2`/`X0` the constants it
    produces, every cold block (`¬ isHot`) is dominant.
-/
lemma cold_isDominant :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        X0 ≤ (2:ℝ) ^ k → BS.k0 ≤ k → k ≤ BS.K →
        ¬ isHot BS c2 a k →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4) := by
  obtain ⟨ c2, X0, hc2, hX0, hB ⟩ := LocalEnergy.nondominant_energy_lower_bound ( 1 / 4 ) ( by norm_num ) ( by norm_num );
  refine' ⟨ c2, X0, hc2, hX0, fun BS a k hk1 hk2 hk3 hk4 => _ ⟩;
  contrapose! hB;
  refine' ⟨ 2 ^ k, _, BS.P k, _, _, _, _ ⟩ <;> norm_num;
  · exact_mod_cast hk1;
  · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime k p hp ) ⟩;
  · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
  · have := BS.hdensity k hk2 hk3; norm_num at *; ring_nf at *; linarith;
  · refine' ⟨ restrict BS a k, blockEnergy BS a k, le_rfl, hB, _ ⟩;
    unfold isHot at hk4; norm_num [ Rw ] at hk4; linarith;

/-
Along a cold segment the dominant
    label is constant: a cold block's label equals the label of its segment
    start.
-/
lemma coldLabel_eq_segStart (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (k : ℕ) (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K)
    (hcold : k ∉ hotSet BS c2 a) :
    coldLabel BS a k
      = coldLabel BS a
          (RequestProject.segmentStart BS.k0 (hotSet BS c2 a) (boundarySet BS c2 a) k) := by
  have h_run : ∀ t, RequestProject.segmentStart BS.k0 (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ t ∧ t < k → coldLabel BS a t = coldLabel BS a (t + 1) := by
    intros t ht; by_contra h_neq; simp_all +decide [ hotSet, boundarySet ] ;
    have h_not_hot : ¬isHot BS c2 a t ∧ ¬isHot BS c2 a (t + 1) := by
      have h_not_hot : t ∉ hotSet BS c2 a ∧ t + 1 ∉ hotSet BS c2 a := by
        have h_not_hot : ∀ j, RequestProject.segmentStart BS.k0 (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ j ∧ j < k → j ∉ hotSet BS c2 a ∧ j ∉ boundarySet BS c2 a := by
          intros j hj; exact (by
          exact RequestProject.segmentStart_interior BS.k0 ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k j hj.1 hj.2);
        by_cases h : t + 1 < k <;> simp_all +decide [ hotSet, boundarySet ]; all_goals grind;
      exact ⟨ fun h => h_not_hot.1 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ RequestProject.segmentStart_ge BS.k0 ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩, h ⟩, fun h => h_not_hot.2 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ RequestProject.segmentStart_ge BS.k0 ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩, h ⟩ ⟩;
    have h_boundary : t ∈ Finset.filter (fun k => ¬isHot BS c2 a k ∧ ¬isHot BS c2 a (k + 1) ∧ coldLabel BS a k ≠ coldLabel BS a (k + 1)) (Finset.Ico BS.k0 BS.K) := by
      simp_all +decide [ Finset.mem_filter, Finset.mem_Ico ];
      exact ⟨ by linarith [ RequestProject.segmentStart_ge BS.k0 ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩;
    have := RequestProject.segmentStart_interior BS.k0 ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k t ht.1 ht.2; simp_all +decide [ hotSet, boundarySet ] ;
  have h_segment : ∀ i j, RequestProject.segmentStart BS.k0 (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ i → i ≤ j → j ≤ k → coldLabel BS a i = coldLabel BS a j := by
    intros i j hi hj hk; induction' hj with j hj ih <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
    rw [ ih ( by linarith ), h_run j ( by linarith ) hk ];
  exact Eq.symm ( h_segment _ _ le_rfl ( RequestProject.segmentStart_le _ _ _ _ hk1 ) le_rfl )

end GlobalControl

end
