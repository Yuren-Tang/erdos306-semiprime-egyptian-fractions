/-
G5 helper layer for `GlobalControl`.

This file keeps the segment-encoding data spaces outside the large
`GlobalControl.lean` file so that the G5 proof can be developed incrementally
against the cached core.
-/
import RequestProject.Core.IntervalSegmentation
import RequestProject.GlobalControl.BoundaryPenalty
import RequestProject.GlobalControl.Encoding.Fibers
import RequestProject.LocalEnergy.DominantLabel
import RequestProject.GlobalPeierlsBookkeeping

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
    most `R` and with the hot-consistency condition needed by `hot_block_count`. -/
def admShells (BS : BlockSystem) (c2 R : ℝ) (H : Finset ℕ) : Finset (ℕ → ℕ) :=
  (shellCarrier BS R).filter
    (fun v =>
      (∑ k ∈ Finset.Icc BS.k0 BS.K, (v k : ℝ)) ≤ R ∧
      ∀ k, k ∈ Finset.Icc BS.k0 BS.K → k ∈ H → Rw c2 k ≤ (v k : ℝ) + 1)

/-- The initial segment label window, carrying the sole global `sigmaCtrl`
    factor in G5. -/
def L0 (BS : BlockSystem) (R : ℝ) : ℤ :=
  ⌈(7 : ℝ) * Real.sqrt R / sigmaP (BS.P BS.k0)⌉

/-- The non-initial label window, in the exact form produced by
    `coldLabel_abs_bound` (`20/3·√(c2·2^k)`) and `block_deviation_reciprocal_bound`
    (`1/σ ≤ 16·2^k·log 2^k`).  Replaces the harder `rpow` form. -/
def labelBound (c2 : ℝ) (k : ℕ) : ℤ :=
  ⌈(20/3) * Real.sqrt (c2 * (2:ℝ) ^ k) * (16 * (2:ℝ) ^ k * Real.log (2 ^ k))⌉

/-- Admissible labels at a segment start.  The initial segment has the
    `sqrt(R)/sigma` window; all later starts use `labelBound`. -/
def labelFin (BS : BlockSystem) (c2 R : ℝ) (k : ℕ) : Finset ℤ :=
  if k = BS.k0 then
    Finset.Icc (-(L0 BS R)) (L0 BS R)
  else
    Finset.Icc (-(labelBound c2 k)) (labelBound c2 k)

/-- Total label functions obtained from segment-start label data, extended by
    zero outside the segment-start set. -/
def admLabels (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) : Finset (ℕ → ℤ) :=
  ((RequestProject.segmentStarts BS.k0 BS.K H B).pi (fun k => labelFin BS c2 R k)).image
    (fun ell k => if h : k ∈ RequestProject.segmentStarts BS.k0 BS.K H B then ell k h else 0)

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

/-! ### Admissibility facts (note 41 §4) -/

/-- The hot set is admissible (its forcing floors sum to `≤ R`). -/
lemma hotSet_mem_admH (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) : hotSet BS c2 a ∈ admH BS c2 R := by
  rw [admH, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, sum_Rw_hot_le BS c2 a R hR⟩
  rw [hotSet]; exact Finset.filter_subset _ _

/-- The boundary set is admissible (its Peierls penalties sum to `≤ R`), given
    the per-`k` penalty bound from `boundary_penalty_per_k`. -/
lemma boundarySet_mem_admB (BS : BlockSystem) (c2 e0 X0 R : ℝ)
    (a : GlobalAssignment BS) (hX0 : X0 ≤ (2:ℝ) ^ BS.k0)
    (hpen : ∀ k, BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k →
        k ∈ boundarySet BS c2 a → Pifloor BS e0 k ≤ Xen BS a k)
    (hR : Qctrl BS a ≤ R) : boundarySet BS c2 a ∈ admB BS e0 R := by
  have hsub : boundarySet BS c2 a ⊆ Finset.Ico BS.k0 BS.K := by
    rw [boundarySet]; exact Finset.filter_subset _ _
  rw [admB, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨hsub, ?_⟩
  calc ∑ k ∈ boundarySet BS c2 a, Pifloor BS e0 k
      ≤ ∑ k ∈ boundarySet BS c2 a, Xen BS a k := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hkIco := Finset.mem_Ico.mp (hsub hk)
        have hkX : X0 ≤ (2:ℝ) ^ k :=
          le_trans hX0 (pow_le_pow_right₀ (by norm_num) hkIco.1)
        exact hpen k hkIco.1 hkIco.2 hkX hk
    _ ≤ ∑ k ∈ Finset.Ico BS.k0 BS.K, Xen BS a k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ ≤ R := sum_bipartite_le BS a R hR

/-- The zero-extended shell data is admissible. -/
lemma extShell_mem_admShells (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (hR0 : 0 ≤ R) (hR : Qctrl BS a ≤ R) :
    extShell BS a ∈ admShells BS c2 R (hotSet BS c2 a) := by
  rw [admShells, Finset.mem_filter]
  refine ⟨?_, ?_, ?_⟩
  · -- extShell ∈ shellCarrier
    rw [shellCarrier, Finset.mem_image]
    refine ⟨fun k _ => shellVec BS a k, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro k hk
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (shellVec_le_floorR BS a R hR0 hR k hk)
    · funext k
      by_cases hk : k ∈ Finset.Icc BS.k0 BS.K <;> simp [extShell, hk]
  · -- shell mass ≤ R
    have hcongr : ∑ k ∈ Finset.Icc BS.k0 BS.K, ((extShell BS a k : ℕ) : ℝ)
         = ∑ k ∈ Finset.Icc BS.k0 BS.K, ((shellVec BS a k : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun k hk => by
        rw [show extShell BS a k = shellVec BS a k from by rw [extShell, if_pos hk]])
    rw [hcongr]; exact sum_shellVec_le BS a R hR
  · -- hot-consistency
    intro k hk hkH
    rw [show extShell BS a k = shellVec BS a k from by rw [extShell, if_pos hk]]
    have hisHot : isHot BS c2 a k := (Finset.mem_filter.mp hkH).2
    rw [isHot] at hisHot
    rw [shellVec]
    have hfloor : blockEnergy BS a k < (⌊blockEnergy BS a k⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith

/-- The cold-class lower bound (hypothesis `hcold` of `cover_card_le`), derived
    from the cold-block dominance (`cold_isDominant`) via `coldLabel_spec`. -/
lemma cold_class_of_isDominant (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (hdom : ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) :
    ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (classCount BS a k (coldLabel BS a k) : ℝ) := by
  intro k hk1 hk2 hkc
  obtain ⟨m, hmsize, hmclass⟩ := hdom k hk1 hk2 hkc
  have hex : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
    refine ⟨m, ?_, hmclass⟩
    have hcast : ((2:ℤ) ^ k) ^ 2 = ((2 ^ k : ℕ) : ℤ) ^ 2 := by push_cast; ring
    rw [hcast]; exact hmsize
  have hspec := (coldLabel_spec BS a k hex).2
  rw [classCount]; exact hspec

/-! ### Label-range admissibility (note 41 §5) -/

/-- Core label bound: a cold block's dominant label has size
    `≤ (20/3)·√(blockEnergy)/σ`, via `theoremA_label_range`. -/
lemma coldLabel_abs_bound (BS : BlockSystem) (a : GlobalAssignment BS) (s : ℕ)
    (hX16 : 16 ≤ (2:ℕ) ^ s) (hN8 : 8 ≤ (BS.P s).card)
    (hdomk : LocalEnergy.HasDominantLabel (2 ^ s) (BS.P s) (restrict BS a s) (1/4)) :
    |(coldLabel BS a s : ℝ)| ≤
      (20/3) * Real.sqrt (blockEnergy BS a s) / sigmaP (BS.P s) := by
  obtain ⟨m, hmsize, hmclass⟩ := hdomk
  have hex : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ s) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P s).card : ℝ) ≤
        (((BS.P s).attach.filter
          (fun p => restrict BS a s p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
    refine ⟨m, ?_, hmclass⟩
    have hcast : ((2:ℤ) ^ s) ^ 2 = ((2 ^ s : ℕ) : ℤ) ^ 2 := by push_cast; ring
    rw [hcast]; exact hmsize
  obtain ⟨hsize, hclass⟩ := coldLabel_spec BS a s hex
  have hP : ∀ p ∈ BS.P s, Nat.Prime p ∧ 2 ^ s ≤ p ∧ p ≤ 2 * 2 ^ s := by
    intro p hp
    refine ⟨BS.hprime s p hp, (BS.hwindow s p hp).1, ?_⟩
    have := (BS.hwindow s p hp).2
    have h2 : (2:ℕ) ^ (s + 1) = 2 * 2 ^ s := by ring
    omega
  have hbound := LocalEnergy.dominant_label_bound (2 ^ s) hX16 (BS.P s) hP hN8 (1/4)
    (by norm_num) (by norm_num) (restrict BS a s) (coldLabel BS a s)
    (blockEnergy BS a s) hsize hclass (le_of_eq rfl)
  rw [show (5 / (1 - (1/4:ℝ))) = 20/3 by norm_num] at hbound
  exact hbound

/-- A cold segment-start's dominant label lies in its `labelFin` window. -/
lemma coldLabel_mem_labelFin (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (s : ℕ) (hs1 : BS.k0 ≤ s) (hs2 : s ≤ BS.K) (_hR0 : 0 ≤ R) (hc2 : 0 ≤ c2)
    (hX16 : 16 ≤ (2:ℕ) ^ s) (hN8 : 8 ≤ (BS.P s).card) (hslog : 1 ≤ Real.log (2 ^ s))
    (hdomk : LocalEnergy.HasDominantLabel (2 ^ s) (BS.P s) (restrict BS a s) (1/4))
    (hcold : ¬ isHot BS c2 a s) (hbR : blockEnergy BS a s ≤ R)
    (hσpos : 0 < sigmaP (BS.P s)) :
    coldLabel BS a s ∈ labelFin BS c2 R s := by
  have habs := coldLabel_abs_bound BS a s hX16 hN8 hdomk
  have hbE0 : 0 ≤ blockEnergy BS a s := by rw [blockEnergy]; exact QP_nonneg _ _
  rw [labelFin]
  split_ifs with hsk0
  · -- initial segment: the √R/σ window
    subst hsk0
    have hnum : (20/3) * Real.sqrt (blockEnergy BS a BS.k0) ≤ 7 * Real.sqrt R := by
      have hsqrt : Real.sqrt (blockEnergy BS a BS.k0) ≤ Real.sqrt R := Real.sqrt_le_sqrt hbR
      nlinarith [Real.sqrt_nonneg (blockEnergy BS a BS.k0), Real.sqrt_nonneg R, hsqrt]
    have hdiv : (20/3) * Real.sqrt (blockEnergy BS a BS.k0) / sigmaP (BS.P BS.k0)
        ≤ 7 * Real.sqrt R / sigmaP (BS.P BS.k0) := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div (7 * Real.sqrt R)]
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
    have hkey : |(coldLabel BS a BS.k0 : ℝ)| ≤ (L0 BS R : ℝ) :=
      le_trans habs (le_trans hdiv (Int.le_ceil _))
    rw [Finset.mem_Icc]
    have hle : |coldLabel BS a BS.k0| ≤ L0 BS R := by exact_mod_cast hkey
    exact abs_le.mp hle
  · -- later segment: the labelBound window
    have hbE_Rw : blockEnergy BS a s ≤ Rw c2 s := by
      rw [isHot, not_le] at hcold; exact le_of_lt hcold
    have hlogpos : 0 < Real.log (2 ^ s) := lt_of_lt_of_le one_pos hslog
    have hcube : (1:ℝ) ≤ (Real.log (2 ^ s)) ^ 3 := one_le_pow₀ hslog
    have hRw_le : Rw c2 s ≤ c2 * (2:ℝ) ^ s := by
      rw [Rw, div_le_iff₀ (by positivity)]
      have hb : (0:ℝ) ≤ c2 * (2:ℝ) ^ s := mul_nonneg hc2 (by positivity)
      nlinarith [mul_nonneg hb (by linarith [hcube] : (0:ℝ) ≤ (Real.log (2 ^ s)) ^ 3 - 1)]
    have hsqrt_le : Real.sqrt (blockEnergy BS a s) ≤ Real.sqrt (c2 * (2:ℝ) ^ s) :=
      Real.sqrt_le_sqrt (le_trans hbE_Rw hRw_le)
    have hinv := block_deviation_reciprocal_bound BS s hs1 hs2
    have hinv0 : 0 ≤ 1 / sigmaP (BS.P s) := by positivity
    have hkey : |(coldLabel BS a s : ℝ)| ≤ (labelBound c2 s : ℝ) := by
      refine le_trans habs ?_
      have hstep : (20/3) * Real.sqrt (blockEnergy BS a s) / sigmaP (BS.P s)
          ≤ (20/3) * Real.sqrt (c2 * (2:ℝ) ^ s) * (16 * (2:ℝ) ^ s * Real.log (2 ^ s)) := by
        rw [div_eq_mul_one_div]
        calc (20/3 * Real.sqrt (blockEnergy BS a s)) * (1 / sigmaP (BS.P s))
            ≤ (20/3 * Real.sqrt (c2 * (2:ℝ) ^ s)) *
                (16 * (2:ℝ) ^ s * Real.log (2 ^ s)) := by
              apply mul_le_mul ?_ hinv hinv0 (by positivity)
              exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
          _ = (20/3) * Real.sqrt (c2 * (2:ℝ) ^ s) *
                (16 * (2:ℝ) ^ s * Real.log (2 ^ s)) := by ring
      exact le_trans hstep (Int.le_ceil _)
    rw [Finset.mem_Icc]
    have : |coldLabel BS a s| ≤ labelBound c2 s := by exact_mod_cast hkey
    exact abs_le.mp this

/-- Label admissibility (`hadmL`): the zero-extended cold labels lie in
    `admLabels`, given membership of each segment-start label in its window. -/
lemma extLabel_mem_admLabels (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (hmem : ∀ s ∈ RequestProject.segmentStarts BS.k0 BS.K (hotSet BS c2 a) (boundarySet BS c2 a),
        coldLabel BS a s ∈ labelFin BS c2 R s) :
    extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a)
      ∈ admLabels BS c2 R (hotSet BS c2 a) (boundarySet BS c2 a) := by
  rw [admLabels, Finset.mem_image]
  refine ⟨fun s _ => coldLabel BS a s, ?_, ?_⟩
  · rw [Finset.mem_pi]; intro s hs; exact hmem s hs
  · funext k
    by_cases hk : k ∈ RequestProject.segmentStarts BS.k0 BS.K (hotSet BS c2 a) (boundarySet BS c2 a) <;>
      simp [extLabel, hk]

/-! ### RHS ε-budget assembly (note 40 §5) -/

/-- Per-fiber product bound: given the per-block count bound (from
    `hot_block_count`/`fixed_label_block_count`), a fiber's cardinality is at most the product of
    `exp(2ε(v k+1))` over the blocks. -/
lemma fiber_prod_bound (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ)
    (eps : ℝ)
    (hcnt : ∀ k ∈ Finset.Icc BS.k0 BS.K,
        ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
            QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
            (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter
                (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card : ℝ)
          ≤ Real.exp (2 * eps * ((v k : ℝ) + 1))) :
    ((fiber BS H B v ℓ).card : ℝ) ≤
      ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
  have h1 := fiber_card_le BS H B v ℓ
  calc ((fiber BS H B v ℓ).card : ℝ)
      ≤ ((∏ k ∈ Finset.Icc BS.k0 BS.K,
          (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
            QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
            (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter
                (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∏ k ∈ Finset.Icc BS.k0 BS.K,
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
            QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
            (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
              (((BS.P k).attach.filter
                (fun p => b p = ((ℓ (RequestProject.segmentStart BS.k0 H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card : ℝ) := by
        push_cast; rfl
    _ ≤ ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) :=
        Finset.prod_le_prod (fun k _ => by positivity) hcnt

/-- Shell-sum bound for `admShells`: the sum over admissible shells of the
    per-block `exp(2ε(v k+1))` product is controlled by the verified
    `shell_sum_bound` (after reindexing the `Finset.pi` form to the subtype
    `Fintype.piFinset` form). -/
lemma shell_sum_le (BS : BlockSystem) (c2 R eps : ℝ)
    (H : Finset ℕ) (heps : 0 < eps) (hR0 : 0 ≤ R) :
    (∑ v ∈ admShells BS c2 R H,
        ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)))
      ≤ Real.exp ((2 * eps + eps) * R) *
          Real.exp ((numBlocks BS : ℝ) *
            (2 * eps + Real.log (1 / (1 - Real.exp (-eps))))) := by
  classical
  set c : {x // x ∈ Finset.Icc BS.k0 BS.K} → ℕ → ℝ :=
    fun _ n => Real.exp (2 * eps * ((n : ℝ) + 1)) with hc
  have hcard : Fintype.card {x // x ∈ Finset.Icc BS.k0 BS.K} = numBlocks BS := by
    simp only [Fintype.card_coe, Nat.card_Icc, numBlocks]
  have hshell := GlobalPeierls.shell_sum_bound c (2 * eps) eps R (by linarith) heps hR0
    (fun _ _ => Real.exp_nonneg _) (fun _ _ => le_of_eq (by simp only [hc]))
  rw [hcard] at hshell
  refine le_trans ?_ hshell
  set φ : (ℕ → ℕ) → ({x // x ∈ Finset.Icc BS.k0 BS.K} → ℕ) := fun v k => v k.1 with hφ
  have hsc : ∀ v ∈ admShells BS c2 R H,
      (∀ k : {x // x ∈ Finset.Icc BS.k0 BS.K}, v k.1 < ⌊R⌋₊ + 1) ∧
      (∀ k, k ∉ Finset.Icc BS.k0 BS.K → v k = 0) := by
    intro v hv
    rw [admShells, Finset.mem_filter] at hv
    obtain ⟨hvsc, -⟩ := hv
    rw [shellCarrier, Finset.mem_image] at hvsc
    obtain ⟨p, hp, rfl⟩ := hvsc
    rw [Finset.mem_pi] at hp
    refine ⟨fun k => ?_, fun k hk => ?_⟩
    · dsimp only; rw [dif_pos k.2]; exact Finset.mem_range.mp (hp k.1 k.2)
    · dsimp only; rw [dif_neg hk]
  have hAB : (∑ v ∈ admShells BS c2 R H,
        ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)))
      = ∑ w ∈ (admShells BS c2 R H).image φ, ∏ k, c k (w k) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      exact (Finset.prod_coe_sort (Finset.Icc BS.k0 BS.K)
        (fun k => Real.exp (2 * eps * ((v k : ℝ) + 1)))).symm
    · intro v hv v' hv' heq
      funext k
      by_cases hk : k ∈ Finset.Icc BS.k0 BS.K
      · have := congrFun heq ⟨k, hk⟩
        simpa [hφ] using this
      · rw [(hsc v hv).2 k hk, (hsc v' hv').2 k hk]
  rw [hAB]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro w hw
  rw [Finset.mem_image] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun k => ?_, ?_⟩
  · rw [Finset.mem_range]; exact (hsc v hv).1 k
  · rw [admShells, Finset.mem_filter] at hv
    have hsum := hv.2.1
    rw [Finset.sum_coe_sort (Finset.Icc BS.k0 BS.K) (fun k => (v k : ℝ))]
    exact hsum

/-- Inner `(v, ℓ)` double sum: given the per-fiber product bound, the sum over
    admissible shells and labels is `≤ |admLabels|·shellBound`. -/
lemma hrhs_inner (BS : BlockSystem) (c2 R eps : ℝ) (H B : Finset ℕ)
    (heps : 0 < eps) (hR0 : 0 ≤ R)
    (hbound : ∀ v ∈ admShells BS c2 R H, ∀ ℓ ∈ admLabels BS c2 R H B,
        ((fiber BS H B v ℓ).card : ℝ) ≤
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1))) :
    (∑ v ∈ admShells BS c2 R H, ∑ ℓ ∈ admLabels BS c2 R H B,
        ((fiber BS H B v ℓ).card : ℝ))
      ≤ ((admLabels BS c2 R H B).card : ℝ) *
          (Real.exp ((2 * eps + eps) * R) *
            Real.exp ((numBlocks BS : ℝ) *
              (2 * eps + Real.log (1 / (1 - Real.exp (-eps)))))) := by
  calc ∑ v ∈ admShells BS c2 R H, ∑ ℓ ∈ admLabels BS c2 R H B,
        ((fiber BS H B v ℓ).card : ℝ)
      ≤ ∑ v ∈ admShells BS c2 R H, ∑ ℓ ∈ admLabels BS c2 R H B,
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
        refine Finset.sum_le_sum (fun v hv => Finset.sum_le_sum (fun ℓ hℓ => hbound v hv ℓ hℓ))
    _ = ∑ v ∈ admShells BS c2 R H, ((admLabels BS c2 R H B).card : ℝ) *
          ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((admLabels BS c2 R H B).card : ℝ) *
          ∑ v ∈ admShells BS c2 R H,
            ∏ k ∈ Finset.Icc BS.k0 BS.K, Real.exp (2 * eps * ((v k : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ ((admLabels BS c2 R H B).card : ℝ) *
          (Real.exp ((2 * eps + eps) * R) *
            Real.exp ((numBlocks BS : ℝ) *
              (2 * eps + Real.log (1 / (1 - Real.exp (-eps)))))) :=
        mul_le_mul_of_nonneg_left (shell_sum_le BS c2 R eps H heps hR0) (by positivity)

/-! ### Route closure (confirms the cover layer composes to `global_levelset`)

This lemma wires the verified cover layer (`cover_card_le` + the four proved
admissibility facts + the cold-class bound) into the *exact* per-`BS` body of
`GlobalControl.global_levelset`.  The only inputs left open are:
  * `hadmL` — the label-range admissibility (`extLabel ∈ admLabels`), the one
    remaining numeric estimate; and
  * `hrhs` — the arithmetic bound on the four-fold fiber sum (the ε-budget).
together with the existential-derived facts `hX0`/`hpen`/`hdom` (supplied by
`cold_isDominant` and `boundary_penalty_per_k` in the final assembly).  Its
type-checking is the machine confirmation that the route closes. -/
lemma global_levelset_route (BS : BlockSystem) (eps c2 e0 X0 R A : ℝ)
    (hR0 : 0 ≤ R)
    (hX0 : X0 ≤ (2:ℝ) ^ BS.k0)
    (hpen : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        ∀ k, BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k →
        k ∈ boundarySet BS c2 a → Pifloor BS e0 k ≤ Xen BS a k)
    (hdom : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4))
    (hadmL : ∀ a : GlobalAssignment BS, Qctrl BS a ≤ R →
        extLabel BS a (hotSet BS c2 a) (boundarySet BS c2 a)
          ∈ admLabels BS c2 R (hotSet BS c2 a) (boundarySet BS c2 a))
    (hrhs : (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
        ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
        Real.exp (A * (numBlocks BS : ℝ)) *
          Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS)) :
    (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
      Real.exp (A * (numBlocks BS : ℝ)) *
        Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  have hbridge : ({a : GlobalAssignment BS | Qctrl BS a ≤ R}).ncard
      = (Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
  have hcov := cover_card_le BS c2 e0 R
    (fun a ha => hotSet_mem_admH BS c2 a R ha)
    (fun a ha => boundarySet_mem_admB BS c2 e0 X0 R a hX0 (hpen a ha) ha)
    (fun a ha => extShell_mem_admShells BS c2 R a hR0 ha)
    hadmL
    (fun a ha => cold_class_of_isDominant BS c2 a (hdom a ha))
  calc (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ)
      = ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) := by
        rw [hbridge]
    _ ≤ (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) := by exact_mod_cast hcov
    _ ≤ _ := hrhs

end GlobalControl
