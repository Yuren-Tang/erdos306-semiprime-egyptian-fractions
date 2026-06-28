/-
# Global block encoding

Cold and hot block data, segment labels, and the finite fiber determined by
those data.  This is the structural encoding layer of the global level-set
argument, before entropy and asymptotic estimates are applied.
-/
import RequestProject.GlobalControl.CrossBlockEnergy

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ## G5. Global level-set theorem (note 34 G5) -/

/-
**G5 (global level-set).**  For every `ε ∈ (0,1)` there is a starting scale
    `k₀(ε)` and a constant `C_glob` such that for every block system with
    `k₀ ≥ k₀(ε)` and all `R ≥ 1`, the number of global assignments with control
    energy `≤ R` is `≤ C_glob · e^{8εR}·(1 + √R/sigmaCtrl)`.

    **Faithfulness note (notes 36--37).**  The constant cannot be chosen after
    `BS` (that is vacuous), but the paper does allow a uniform base constant per
    block.  Hence the faithful form below has a uniform `A` and the harmless
    factor `exp(A * numBlocks BS)`, under `admissibleGlobalRange BS`.

    The count is encoded by the segment decoder of note 34 G5 (hot set, hot
    data, mismatch boundary, segment labels, cold exceptions), with the
    single-block inputs L1–L5 (`SBEEAssembly.unified_levelset`,
    `SBEEForcing.theorem_A_dominant_count`, …) and the exceptional mismatch
    penalty `mismatch_penalty_with_exceptions`.

    **Status**: the segment-encoding route is completed downstream in
    `GlobalControl.LevelSetAssembly`.
-/
/-! ### G5 skeleton (note 39) — setup definitions -/

/-- Per-block internal energy of a global assignment. -/
def blockEnergy (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  QP (BS.P k) (restrict BS a k)

/-- The cold/hot threshold `R_w(k) = c2·2^k/log³(2^k)` (Theorem-B floor). -/
def Rw (c2 : ℝ) (k : ℕ) : ℝ := c2 * 2 ^ k / (Real.log (2 ^ k)) ^ 3

/-- Hot block: internal energy at least the forcing floor. -/
def isHot (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (k : ℕ) : Prop :=
  Rw c2 k ≤ blockEnergy BS a k

instance instDecidableIsHot (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (k : ℕ) : Decidable (isHot BS c2 a k) := Classical.dec _

/-- The hot set: scales in `[k0,K]` whose block is hot. -/
def hotSet (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Icc BS.k0 BS.K).filter (isHot BS c2 a)

/-- The dominant label of a block (0 if none).  Uniqueness is hole 1. -/
def coldLabel (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℤ :=
  if h : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)
  then h.choose else 0

/-- Mismatch boundary: two consecutive cold blocks with distinct labels. -/
def boundarySet (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Ico BS.k0 BS.K).filter (fun k =>
    ¬ isHot BS c2 a k ∧ ¬ isHot BS c2 a (k+1) ∧
    coldLabel BS a k ≠ coldLabel BS a (k+1))

/-- Integer energy shell of each block. -/
def shellVec (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℕ :=
  ⌊blockEnergy BS a k⌋₊

/-- Segment starts determined by the DATA `(H,B)` alone (no `a`):
    cold blocks that open a maximal cold run. -/
def segStarts (BS : BlockSystem) (H B : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc BS.k0 BS.K) \ H).filter
    (fun k => k = BS.k0 ∨ (k - 1) ∈ H ∨ (k - 1) ∈ B)

/-- The start of the segment containing a cold `k` (recursion downward). -/
def segStart (BS : BlockSystem) (H B : Finset ℕ) : ℕ → ℕ
  | k => if k ≤ BS.k0 then BS.k0
         else if (k - 1) ∈ H ∨ (k - 1) ∈ B then k
         else segStart BS H B (k - 1)
  decreasing_by all_goals omega

/-- The exception-reduced boundary penalty floor `Π(k)`. -/
def Pifloor (BS : BlockSystem) (e0 : ℝ) (k : ℕ) : ℝ :=
  (((BS.P (k+1)).card : ℝ) - e0 - 1) * (((BS.P k).card : ℝ) - e0) ^ 3 /
    (2 ^ 13 * ((2:ℝ) ^ k) ^ 2)

/-- Label range at a segment start (L3 + cold threshold; note 38 §3 L3c). -/
def labelRange (c2 : ℝ) (k : ℕ) : ℤ := ⌈(168:ℝ) * Real.sqrt c2 *
    ((2:ℝ) ^ k) ^ (3/2 : ℝ) / Real.sqrt (Real.log (2 ^ k))⌉

/-! ### G5 skeleton (note 39) — holes -/

/-
**Hole 1a (`coldLabel_spec`).**  When a dominant label exists for block `k`,
    `coldLabel` is one such label: it satisfies the size+class property.
-/
lemma coldLabel_spec (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (h : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)) :
    |coldLabel BS a k| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p
            = ((coldLabel BS a k : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
  convert h.choose_spec; all_goals exact dif_pos h

/-
**Hole 1b (`coldLabel_eq`).**  Uniqueness: the dominant label is unique, so
    any `m` with the size+class property at a cold block equals `coldLabel`.
-/
lemma coldLabel_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (_hk1 : BS.k0 ≤ k) (_hk2 : k ≤ BS.K) (hX : 4 ≤ (2:ℕ) ^ k)
    (hN : 4 ≤ (BS.P k).card)
    (m : ℤ) (hm : |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2)
    (hclass : (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (((BS.P k).attach.filter
        (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)) :
    coldLabel BS a k = m := by
  have hdom : ∃ n : ℤ, |n| ≤ ((2 : ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1 / 4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter (fun p => restrict BS a k p =
          ((n : ℤ) : ZMod (p : ℕ)))).card : ℝ) := ⟨m, hm, hclass⟩
  have hcold := coldLabel_spec BS a k hdom
  apply SBEEForcing.dominant_label_unique (2 ^ k) hX (BS.P k)
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
**Hole 4a (`segStart_le`).**  For `k ≥ k0` the segment start of `k` is `≤ k`.
    (For `k < k0` the recursion returns `k0 > k`, so the hypothesis is needed.)
-/
lemma segStart_le (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ) (hk : BS.k0 ≤ k) :
    segStart BS H B k ≤ k := by
  induction' k using Nat.strong_induction_on with k ih;
  unfold segStart;
  grind +splitImp

/-
**Hole 4b (`segStart_ge`).**  The segment start of `k` is `≥ k0`.
-/
lemma segStart_ge (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ) :
    BS.k0 ≤ segStart BS H B k := by
  induction' k using Nat.strong_induction_on with k ih;
  unfold segStart;
  grind

/-
**Hole 4c (`segStart_run`).**  Every block strictly inside the run from the
    segment start of `k` up to `k` is cold-by-data and carries no internal
    boundary edge.
-/
lemma segStart_run (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ)
    (j : ℕ) (hj1 : segStart BS H B k ≤ j) (hj2 : j < k) :
    j ∉ H ∧ j ∉ B := by
  induction' k with k ih generalizing j <;> simp_all +decide;
  grind +locals

/-
**Hole 2 (`cold_isDominant`).**  Contrapositive of
    `theorem_B_nondominant_forcing` at `ρ = 1/4`: with `c2`/`X0` the constants it
    produces, every cold block (`¬ isHot`) is dominant.
-/
lemma cold_isDominant :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        X0 ≤ (2:ℝ) ^ k → BS.k0 ≤ k → k ≤ BS.K →
        ¬ isHot BS c2 a k →
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4) := by
  obtain ⟨ c2, X0, hc2, hX0, hB ⟩ := SBEEForcing.theorem_B_nondominant_forcing ( 1 / 4 ) ( by norm_num ) ( by norm_num );
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
**Hole 5 (`coldLabel_eq_segStart`).**  Along a cold segment the dominant
    label is constant: a cold block's label equals the label of its segment
    start.
-/
lemma coldLabel_eq_segStart (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (k : ℕ) (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K)
    (hcold : k ∉ hotSet BS c2 a) :
    coldLabel BS a k
      = coldLabel BS a
          (segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k) := by
  have h_run : ∀ t, segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ t ∧ t < k → coldLabel BS a t = coldLabel BS a (t + 1) := by
    intros t ht; by_contra h_neq; simp_all +decide [ hotSet, boundarySet ] ;
    have h_not_hot : ¬isHot BS c2 a t ∧ ¬isHot BS c2 a (t + 1) := by
      have h_not_hot : t ∉ hotSet BS c2 a ∧ t + 1 ∉ hotSet BS c2 a := by
        have h_not_hot : ∀ j, segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ j ∧ j < k → j ∉ hotSet BS c2 a ∧ j ∉ boundarySet BS c2 a := by
          intros j hj; exact (by
          exact segStart_run BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k j hj.1 hj.2);
        by_cases h : t + 1 < k <;> simp_all +decide [ hotSet, boundarySet ]; all_goals grind;
      exact ⟨ fun h => h_not_hot.1 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ segStart_ge BS ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩, h ⟩, fun h => h_not_hot.2 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ segStart_ge BS ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩, h ⟩ ⟩;
    have h_boundary : t ∈ Finset.filter (fun k => ¬isHot BS c2 a k ∧ ¬isHot BS c2 a (k + 1) ∧ coldLabel BS a k ≠ coldLabel BS a (k + 1)) (Finset.Ico BS.k0 BS.K) := by
      simp_all +decide [ Finset.mem_filter, Finset.mem_Ico ];
      exact ⟨ by linarith [ segStart_ge BS ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩;
    have := segStart_run BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k t ht.1 ht.2; simp_all +decide [ hotSet, boundarySet ] ;
  have h_segment : ∀ i j, segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ i → i ≤ j → j ≤ k → coldLabel BS a i = coldLabel BS a j := by
    intros i j hi hj hk; induction' hj with j hj ih <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
    rw [ ih ( by linarith ), h_run j ( by linarith ) hk ];
  exact Eq.symm ( h_segment _ _ le_rfl ( segStart_le _ _ _ _ hk1 ) le_rfl )

/-- The number of primes of block `k` on which `restrict BS a k` takes the
    residue `m` (the size of the `m`-class). -/
def classCount (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) (m : ℤ) : ℕ :=
  ((BS.P k).attach.filter
    (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card

/-- **Hole 6 (fiber).**  The data-fiber of `(H,B,v,ℓ)`: assignments whose every
    block energy sits in the shell `v k` and whose cold blocks carry the
    segment-start label `ℓ (segStart …)` on a `(1-ρ)` fraction of primes. -/
def fiber (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ) :
    Finset (GlobalAssignment BS) :=
  Finset.univ.filter (fun a => ∀ k ∈ Finset.Icc BS.k0 BS.K,
    blockEnergy BS a k ≤ (v k : ℝ) + 1 ∧
    (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (classCount BS a k (ℓ (segStart BS H B k)) : ℝ)))

/-
**Hole 7 (`fiber_card_le`).**  The fiber injects into the product of the
    per-block counts (Lemma D4, `restrict_filter_card_le`).
-/
lemma fiber_card_le (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ) :
    (fiber BS H B v ℓ).card ≤
      ∏ k ∈ Finset.Icc BS.k0 BS.K,
        (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
          QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
          (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
            (((BS.P k).attach.filter
              (fun p => b p = ((ℓ (segStart BS H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card := by
  unfold fiber; norm_num;
  convert restrict_filter_card_le BS ( fun k b => QP ( BS.P k ) b ≤ v k + 1 ∧ ( k ∉ H → ( 3 / 4 : ℝ ) * ( BS.P k |> Finset.card ) ≤ ( Finset.card ( Finset.filter ( fun p : { x // x ∈ BS.P k } => b p = ℓ ( segStart BS H B k ) ) ( Finset.attach ( BS.P k ) ) ) : ℝ ) ) ) using 2;
  · simp +decide [ blockEnergy, classCount ];
  · convert rfl

end GlobalControl

end
