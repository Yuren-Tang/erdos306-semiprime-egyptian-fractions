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

/-- Zero-extension of the shell data outside `[k₀,K]`, matching the
    image form of `admShells`. -/
def extShell (BS : BlockSystem) (a : GlobalAssignment BS) : ℕ → ℕ :=
  fun k => if k ∈ Finset.Icc BS.k0 BS.K then shellVec BS a k else 0

/-- Zero-extension of the label data outside `segStarts H B`, matching the
    image form of `admLabels`. -/
def extLabel (BS : BlockSystem) (a : GlobalAssignment BS) (H B : Finset ℕ) : ℕ → ℤ :=
  fun k => if k ∈ segStarts BS H B then coldLabel BS a k else 0

/-- The encoder lands `a` in the fiber of its own zero-extended invariants.
    The cold-class lower bound is supplied as a hypothesis (discharged from the
    cold-block facts). -/
lemma mem_fiber_encode (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
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
    -- the fiber evaluates extLabel at the segment start, which lies in segStarts
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
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4)) :
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
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4))
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
