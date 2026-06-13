/-
# G5 / G7 — Global level-set theorem and global control partition

Split out of `GlobalControl.lean` (note 34 / note 40, Phase G) so the heavy
G5 segment-encoding ("Peierls") assembly can be elaborated against the compiled
`GlobalControl` olean rather than re-elaborating the whole support layer.

All declarations stay in `namespace GlobalControl`.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEAssembly
import RequestProject.GlobalPeierlsBookkeeping
import RequestProject.GlobalControl

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- **Generic covering bound.**  If a finite set `S` is covered by the indexed
    family `F` over `I`, then `S.card ≤ ∑ i ∈ I, (F i).card`.  Proved once and
    reused in the four-level G5 covering argument (no disjointness needed). -/
lemma card_le_sum_fibers_of_cover {α ι : Type*} [DecidableEq α]
    (S : Finset α) (I : Finset ι) (F : ι → Finset α)
    (hcover : S ⊆ I.biUnion F) :
    S.card ≤ ∑ i ∈ I, (F i).card :=
  le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)

/-! ### G5 §3 data Finsets (note 40) -/

/-- Admissible hot sets: subsets of `[k0,K]` whose hot-floor weight is `≤ R`. -/
def admH (BS : BlockSystem) (c2 R : ℝ) : Finset (Finset ℕ) :=
  (Finset.Icc BS.k0 BS.K).powerset.filter (fun H => ∑ k ∈ H, Rw c2 k ≤ R)

/-- Admissible mismatch-boundary sets: subsets of `[k0,K)` whose boundary
    penalty is `≤ R`. -/
def admB (BS : BlockSystem) (e0 R : ℝ) : Finset (Finset ℕ) :=
  (Finset.Ico BS.k0 BS.K).powerset.filter (fun B => ∑ k ∈ B, Pifloor BS e0 k ≤ R)

/-- Initial-segment label window radius: the `√R`-window `L0`. -/
noncomputable def L0 (BS : BlockSystem) (R : ℝ) : ℤ :=
  ⌈(7 : ℝ) * Real.sqrt R / sigmaP (BS.P BS.k0)⌉

/-- Per-start label window: the `√R`-window `L0` at the initial scale `k0`,
    otherwise the `labelRange` window. -/
noncomputable def labelFin (BS : BlockSystem) (c2 R : ℝ) (k : ℕ) : Finset ℤ :=
  if k = BS.k0 then Finset.Icc (-(L0 BS R)) (L0 BS R)
  else Finset.Icc (-(labelRange c2 k)) (labelRange c2 k)

/-- Admissible shell vectors (total functions, `0` outside `[k0,K]`): each
    coordinate is `≤ ⌊R⌋₊`, the total energy is `≤ R`, and the hot blocks of `H`
    sit above the forcing floor. -/
def admShells (BS : BlockSystem) (c2 R : ℝ) (H : Finset ℕ) : Finset (ℕ → ℕ) :=
  (((Finset.Icc BS.k0 BS.K).pi (fun _ => Finset.range (⌊R⌋₊ + 1))).image
      (fun v => fun k => if h : k ∈ Finset.Icc BS.k0 BS.K then v k h else 0)).filter
    (fun w => (∑ k ∈ Finset.Icc BS.k0 BS.K, (w k : ℝ)) ≤ R ∧
      ∀ k ∈ H, Rw c2 k ≤ (w k : ℝ) + 1)

/-- Admissible label functions (total functions, `0` outside `segStarts`): each
    segment start carries a label in its window `labelFin`. -/
def admLabels (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) : Finset (ℕ → ℤ) :=
  ((segStarts BS H B).pi (fun k => labelFin BS c2 R k)).image
    (fun L => fun k => if h : k ∈ segStarts BS H B then L k h else 0)

/-- The shell encoder of an assignment: `shellVec`, truncated to `0` off
    `[k0,K]`. -/
def encShell (BS : BlockSystem) (a : GlobalAssignment BS) : ℕ → ℕ :=
  fun k => if k ∈ Finset.Icc BS.k0 BS.K then shellVec BS a k else 0

/-- The label encoder of an assignment: `coldLabel` on `segStarts`, `0`
    elsewhere. -/
def encLabel (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : ℕ → ℤ :=
  fun k => if k ∈ segStarts BS (hotSet BS c2 a) (boundarySet BS c2 a)
           then coldLabel BS a k else 0

/-! ### G5 §3 encoder membership / admissibility lemmas (note 40) -/

/-
The segment start of a cold block lies in `segStarts`.
-/
lemma segStart_mem_segStarts (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ)
    (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K) (hk : k ∉ H) :
    segStart BS H B k ∈ segStarts BS H B := by
  have hseg : segStart BS H B k ∈ Finset.Icc BS.k0 BS.K := by
    exact Finset.mem_Icc.mpr ⟨ segStart_ge BS H B k, by linarith [ segStart_le BS H B k hk1 ] ⟩;
  have hseg_not_in_H : segStart BS H B k ∉ H := by
    exact fun h => by have := segStart_run BS H B k ( segStart BS H B k ) ( by linarith ) ( by linarith [ show segStart BS H B k < k from lt_of_le_of_ne ( segStart_le BS H B k hk1 ) ( by aesop ) ] ) ; aesop;
  have hseg_or : segStart BS H B k = BS.k0 ∨ (segStart BS H B k - 1) ∈ H ∨ (segStart BS H B k - 1) ∈ B := by
    have hseg_or : ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ H → segStart BS H B k = BS.k0 ∨ (segStart BS H B k - 1) ∈ H ∨ (segStart BS H B k - 1) ∈ B := by
      intros k hk1 hk2 hk_not_in_H
      induction' k using Nat.strong_induction_on with k ih;
      unfold segStart;
      grind +qlia;
    grind +splitImp;
  exact Finset.mem_filter.mpr ⟨ Finset.mem_sdiff.mpr ⟨ hseg, hseg_not_in_H ⟩, hseg_or ⟩

/-
`hotSet` is an admissible hot set.
-/
lemma hotSet_mem_admH (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (hR : Qctrl BS a ≤ R) : hotSet BS c2 a ∈ admH BS c2 R := by
  exact Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr <| Finset.filter_subset _ _, by simpa using sum_Rw_hot_le BS c2 a R hR ⟩

/-
`encShell` is an admissible shell vector for `H = hotSet`.
-/
lemma encShell_mem_admShells (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (hR0 : 0 ≤ R) (hR : Qctrl BS a ≤ R) :
    encShell BS a ∈ admShells BS c2 R (hotSet BS c2 a) := by
  refine' Finset.mem_filter.mpr ⟨ _, _, _ ⟩;
  · simp [encShell];
    refine' ⟨ fun k hk => shellVec BS a k, _, _ ⟩;
    · exact fun k hk1 hk2 => shellVec_le_floorR BS a R hR0 hR k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ );
    · exact funext fun k => by unfold encShell; aesop;
  · convert sum_shellVec_le BS a R hR using 1;
    exact Finset.sum_congr rfl fun x hx => by unfold encShell; aesop;
  · intro k hk; unfold encShell; simp_all +decide [ isHot ] ;
    split_ifs <;> simp_all +decide [ hotSet ];
    exact le_trans hk ( Nat.lt_floor_add_one _ |> le_of_lt )

/-
`encLabel` is an admissible label function — provided each segment start's
    cold label lands in its window.  Stated abstractly via the window membership
    hypothesis `hwin`.
-/
lemma encLabel_mem_admLabels (BS : BlockSystem) (c2 R : ℝ) (a : GlobalAssignment BS)
    (hwin : ∀ s ∈ segStarts BS (hotSet BS c2 a) (boundarySet BS c2 a),
        coldLabel BS a s ∈ labelFin BS c2 R s) :
    encLabel BS c2 a ∈
      admLabels BS c2 R (hotSet BS c2 a) (boundarySet BS c2 a) := by
  convert Set.mem_image_of_mem _ ( Set.mem_pi.mpr fun s hs => hwin s hs ) using 1;
  rotate_left;
  exact ℕ → ℤ;
  exact fun f k => if h : k ∈ segStarts BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) then f k else 0;
  unfold encLabel admLabels; aesop;

/-
Every level-set assignment lands in the fiber of its own encoder data.
-/
lemma mem_fiber_encode (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (hdom : ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (classCount BS a k (coldLabel BS a k) : ℝ)) :
    a ∈ fiber BS (hotSet BS c2 a) (boundarySet BS c2 a)
        (encShell BS a) (encLabel BS c2 a) := by
  unfold fiber;
  simp +zetaDelta at *;
  intro k hk1 hk2; refine' ⟨ _, _ ⟩;
  · unfold encShell;
    rw [ if_pos ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ] ; exact Nat.lt_floor_add_one _ |> le_of_lt;
  · convert hdom k hk1 hk2 using 1;
    rw [ GlobalControl.encLabel ];
    rw [ if_pos ( segStart_mem_segStarts BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k hk1 hk2 ‹_› ), coldLabel_eq_segStart BS c2 a k hk1 hk2 ‹_› ]

/-! ### G5 §3 the four-level covering bound (note 40 6a/6b/6d) -/

lemma cover_card_le (BS : BlockSystem) (c2 e0 R : ℝ) (hR0 : 0 ≤ R)
    (hdom : ∀ (a : GlobalAssignment BS), Qctrl BS a ≤ R →
      ∀ k, BS.k0 ≤ k → k ≤ BS.K → k ∉ hotSet BS c2 a →
        (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
          (classCount BS a k (coldLabel BS a k) : ℝ))
    (hbdry : ∀ (a : GlobalAssignment BS), Qctrl BS a ≤ R →
      boundarySet BS c2 a ∈ admB BS e0 R)
    (hwin : ∀ (a : GlobalAssignment BS), Qctrl BS a ≤ R →
      ∀ s ∈ segStarts BS (hotSet BS c2 a) (boundarySet BS c2 a),
        coldLabel BS a s ∈ labelFin BS c2 R s) :
    ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ)
      ≤ ∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R,
          ∑ v ∈ admShells BS c2 R H, ∑ L ∈ admLabels BS c2 R H B,
            ((fiber BS H B v L).card : ℝ) := by
  refine' mod_cast le_trans ( Finset.card_le_card _ ) _;
  exact Finset.biUnion ( admH BS c2 R ) fun H => Finset.biUnion ( admB BS e0 R ) fun B => Finset.biUnion ( admShells BS c2 R H ) fun v => Finset.biUnion ( admLabels BS c2 R H B ) fun L => fiber BS H B v L;
  · intro a ha;
    simp +zetaDelta at *;
    refine' ⟨ _, hotSet_mem_admH BS c2 R a ha, _, hbdry a ha, _, encShell_mem_admShells BS c2 R a hR0 ha, _, encLabel_mem_admLabels BS c2 R a ( hwin a ha ), _ ⟩;
    exact mem_fiber_encode BS c2 a fun k hk1 hk2 hk3 => by simpa using hdom a ha k hk1 hk2 hk3;
  · refine' le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun H hH => _ );
    refine' le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun B hB => _ );
    refine' le_trans ( Finset.card_biUnion_le ) _;
    exact Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le

/-! ### G5 §3 admissibility (discharge) helpers for `cover_card_le` (note 40 §2) -/

/-
**hdom helper.**  If the exception set of (cold) block `k` is small
    (`≤ e0`) and the block is large enough that `4·e0 ≤ Nₖ`, then the dominant
    label covers a `(1-ρ)=3/4` fraction: the class count bound `cover_card_le`
    needs.  (Uses `conform_card_eq`: the conforming primes are exactly the
    `coldLabel`-class.)
-/
lemma classCount_dom_param (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) (e0 : ℝ)
    (hexc : ((excSet BS a k).card : ℝ) ≤ e0)
    (hN : 4 * e0 ≤ ((BS.P k).card : ℝ)) :
    (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (classCount BS a k (coldLabel BS a k) : ℝ) := by
  rw [ ← conform_card_eq BS a k hk ];
  rw [ Finset.card_sdiff ];
  rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a k ) ] ; rw [ Nat.cast_sub ( Finset.card_le_card <| excSet_subset BS a k ) ] ; linarith

/-
**hbdry helper.**  If every mismatch-boundary block contributes bipartite
    energy `≥ Pifloor`, then the boundary set is admissible (its boundary
    penalty is `≤ R`).
-/
lemma boundarySet_mem_admB_param (BS : BlockSystem) (c2 e0 R : ℝ)
    (a : GlobalAssignment BS)
    (hpen : ∀ k, BS.k0 ≤ k → k < BS.K → k ∈ boundarySet BS c2 a →
      Pifloor BS e0 k ≤ Xen BS a k)
    (hR : Qctrl BS a ≤ R) :
    boundarySet BS c2 a ∈ admB BS e0 R := by
  refine' Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr _, _ ⟩;
  · exact fun x hx => Finset.mem_filter.mp hx |>.1;
  · refine' le_trans ( Finset.sum_le_sum fun k hk => hpen k _ _ hk ) _;
    · exact Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ) |>.1;
    · exact Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ) |>.2;
    · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( show boundarySet BS c2 a ⊆ Finset.Ico BS.k0 BS.K from _ ) fun _ _ _ => _ ) ( GlobalControl.sum_bipartite_le BS a R hR );
      · exact fun x hx => Finset.mem_filter.mp hx |>.1;
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
**hwin helper (initial start).**  The cold label of the initial block `k0`
    lies in the `√R`-window `L0`.  Uses `theoremA_label_range` (the
    restricted-σ label bound) with `R' = R`: `|coldLabel k0| ≤ (20/3)√R/σ ≤
    7√R/σ ≤ L0`.
-/
lemma coldLabel_mem_labelFin_initial (BS : BlockSystem) (c2 R : ℝ)
    (a : GlobalAssignment BS) (hR : 1 ≤ R)
    (hN8 : 8 ≤ (BS.P BS.k0).card)
    (hsize : |coldLabel BS a BS.k0| ≤ ((2:ℤ) ^ BS.k0) ^ 2 / 2)
    (hclass : (1 - (1/4 : ℝ)) * ((BS.P BS.k0).card : ℝ) ≤
      (classCount BS a BS.k0 (coldLabel BS a BS.k0) : ℝ))
    (hQ : blockEnergy BS a BS.k0 ≤ R) :
    coldLabel BS a BS.k0 ∈ labelFin BS c2 R BS.k0 := by
  -- From `theoremA_label_range`, obtain `|coldLabel k0| ≤ (20/3) * sqrt(R) / sigmaP k0`.
  have h_bound : |(coldLabel BS a BS.k0 : ℝ)| ≤ (20 / 3) * Real.sqrt R / sigmaP (BS.P BS.k0) := by
    convert SBEEForcing.theoremA_label_range ( 2 ^ BS.k0 ) _ ( BS.P BS.k0 ) ( fun p hp => ⟨ BS.hprime BS.k0 p hp, ?_, ?_ ⟩ ) hN8 ( 1 / 4 ) ( by norm_num ) ( by norm_num ) ( restrict BS a BS.k0 ) ( coldLabel BS a BS.k0 ) R _ _ _ using 1 <;> norm_num at *;
    any_goals assumption;
    · have h_card_le : (BS.P BS.k0).card ≤ 2 ^ BS.k0 := by
        convert GlobalControl.block_card_le BS BS.k0 using 1;
      by_contra h_contra;
      have : BS.k0 ≤ 3 := Nat.le_of_not_lt fun h => by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) h ] ; ; interval_cases BS.k0 <;> norm_num at *;
      · linarith;
      · grobner;
      · linarith;
      · interval_cases _ : #(BS.P 3) ; norm_num at *;
        have h_card_le : (BS.P 3).card ≤ Finset.card (Finset.filter Nat.Prime (Finset.Ico (2 ^ 3) (2 ^ 4))) := by
          exact Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr <| BS.hwindow 3 x hx, BS.hprime 3 x hx ⟩;
        exact absurd h_card_le ( by rw [ ‹#(BS.P 3) = 8› ] ; native_decide );
    · linarith [ BS.hwindow BS.k0 p hp ];
    · linarith [ BS.hwindow BS.k0 p hp, pow_succ' 2 BS.k0 ];
  -- From `sigmaP_nonneg` (and `hN8` to get `sigmaP > 0`), we get `(20/3) * sqrt(R) / sigmaP k0 ≤ 7 * sqrt(R) / sigmaP k0 ≤ ⌈7 * sqrt(R) / sigmaP k0⌉ = L0`.
  have h_L0 : 7 * Real.sqrt R / sigmaP (BS.P BS.k0) ≤ L0 BS R := by
    exact Int.le_ceil _;
  unfold labelFin; norm_num [ abs_le ] at *;
  exact ⟨ by exact_mod_cast ( by ring_nf at *; linarith : ( -L0 BS R : ℝ ) ≤ coldLabel BS a BS.k0 ), by exact_mod_cast ( by ring_nf at *; linarith : ( coldLabel BS a BS.k0 : ℝ ) ≤ L0 BS R ) ⟩

/-
**hwin helper (non-initial start).**  The cold label of a non-initial
    segment start `s` lies in the `labelRange` window.  Uses
    `theoremA_label_range` with `R' = blockEnergy s < Rw c2 s` (cold) and
    `inv_sigmaP_bound`: `|coldLabel s| ≤ (20/3)√(Rw)/σ ≤ (320/3)√c2·(2^s)^{3/2}/√log
    ≤ labelRange c2 s`.
-/
lemma coldLabel_mem_labelFin_noninitial (BS : BlockSystem) (c2 R : ℝ)
    (a : GlobalAssignment BS) (hc2 : 0 < c2)
    (s : ℕ) (hs0 : BS.k0 ≤ s) (hsK : s ≤ BS.K) (hsne : s ≠ BS.k0)
    (hN8 : 8 ≤ (BS.P s).card)
    (hsize : |coldLabel BS a s| ≤ ((2:ℤ) ^ s) ^ 2 / 2)
    (hclass : (1 - (1/4 : ℝ)) * ((BS.P s).card : ℝ) ≤
      (classCount BS a s (coldLabel BS a s) : ℝ))
    (hcold : ¬ isHot BS c2 a s) :
    coldLabel BS a s ∈ labelFin BS c2 R s := by
  unfold labelFin;
  have h_label_range : |(coldLabel BS a s : ℝ)| ≤ (320 / 3) * Real.sqrt c2 * ((2:ℝ)^s)^(3/2:ℝ) / Real.sqrt (Real.log (2^s)) := by
    have h_label_range : |(coldLabel BS a s : ℝ)| ≤ (20 / 3) * Real.sqrt (blockEnergy BS a s) / sigmaP (BS.P s) := by
      have := SBEEForcing.theoremA_label_range (2 ^ s) (by
      by_contra h_contra;
      have h_card_le : (BS.P s).card ≤ 7 := by
        have h_card_le : (BS.P s).card ≤ Finset.card (Finset.filter Nat.Prime (Finset.Ico (2 ^ s) (2 ^ (s + 1)))) := by
          exact Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr <| BS.hwindow s x hx, BS.hprime s x hx ⟩;
        exact h_card_le.trans ( by have : s ≤ 3 := Nat.le_of_not_lt fun h => h_contra <| by linarith [ Nat.pow_le_pow_right two_pos h ] ; ; interval_cases s <;> trivial; );
      linarith) (BS.P s) (fun p hp => ⟨BS.hprime s p hp, by
        exact BS.hwindow s p hp |>.1, by
        linarith [ BS.hwindow s p hp, pow_succ' 2 s ]⟩) hN8 (1 / 4) (by
      norm_num) (by
      norm_num) (restrict BS a s) (coldLabel BS a s) (blockEnergy BS a s) (by
      convert hsize using 1) (by
      convert hclass using 1) (by
      exact le_rfl);
      exact this.trans_eq ( by ring );
    have h_label_range : Real.sqrt (blockEnergy BS a s) / sigmaP (BS.P s) ≤ Real.sqrt (Rw c2 s) * (16 * (2:ℝ) ^ s * Real.log (2 ^ s)) := by
      have h_label_range : Real.sqrt (blockEnergy BS a s) ≤ Real.sqrt (Rw c2 s) := by
        exact Real.sqrt_le_sqrt <| le_of_not_ge hcold;
      refine le_trans ( div_le_div_of_nonneg_right h_label_range <| ?_ ) ?_;
      · exact Real.sqrt_nonneg _;
      · convert mul_le_mul_of_nonneg_left ( inv_sigmaP_bound BS s hs0 hsK ) ( Real.sqrt_nonneg ( Rw c2 s ) ) using 1 ; ring;
    have h_label_range : Real.sqrt (Rw c2 s) * (16 * (2:ℝ) ^ s * Real.log (2 ^ s)) = (320 / 3) * Real.sqrt c2 * ((2:ℝ)^s)^(3/2:ℝ) / Real.sqrt (Real.log (2^s)) * (3 / 20) := by
      unfold Rw; norm_num [ Real.sqrt_div_self, Real.sqrt_mul_self, hc2.le ] ; ring;
      rw [ show ( 2 ^ s : ℝ ) ^ ( 3 / 2 : ℝ ) = ( 2 ^ s : ℝ ) * Real.sqrt ( 2 ^ s ) by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; norm_num [ pow_three, mul_assoc, mul_comm, mul_left_comm, hc2.le, Real.log_nonneg ] ; ring;
      grind;
    grind +qlia;
  have h_label_range : |(coldLabel BS a s : ℝ)| ≤ (168 : ℝ) * Real.sqrt c2 * ((2:ℝ)^s)^(3/2:ℝ) / Real.sqrt (Real.log (2^s)) := by
    exact h_label_range.trans ( by gcongr ; norm_num );
  simp_all +decide [ labelRange ];
  exact ⟨ neg_le_of_abs_le <| by exact_mod_cast h_label_range.trans <| Int.le_ceil _, le_of_abs_le <| by exact_mod_cast h_label_range.trans <| Int.le_ceil _ ⟩

/-- **G5 — Global level-set theorem** (note 34 / note 40, Phase G).

    **Status**: named `sorry` — the §4–§5 entropy summation (the Peierls
    "endgame") remains.  The entire §3 layer it builds on is now proved in this
    file: the data Finsets (`admH`, `admB`, `admShells`, `admLabels`,
    `labelFin`, `L0`), the encoder maps (`encShell`, `encLabel`), the encoder
    membership lemmas (`segStart_mem_segStarts`, `hotSet_mem_admH`,
    `encShell_mem_admShells`, `encLabel_mem_admLabels`, `mem_fiber_encode`),
    the four-level covering bound `cover_card_le`, and all three admissibility
    discharge helpers for its hypotheses (`classCount_dom_param`,
    `boundarySet_mem_admB_param`, `coldLabel_mem_labelFin_initial`,
    `coldLabel_mem_labelFin_noninitial`).

    What remains is precisely the analytic summation of `cover_card_le`'s right
    side via `GlobalPeierlsBookkeeping.{weighted_subset_entropy, shell_sum_bound}`
    together with `hot_factor`/`cold_factor`, plus the dedicated initial-segment
    treatment that produces the explicit `(1 + √R/sigmaCtrl BS)` factor: the
    initial label ranges over the `√R`-window `L0`, whose width is *not* covered
    by `cold_factor`'s label-size hypothesis `|m| ≤ Nₖ·2^k/16`, so it must be
    summed separately (it is the source of the `√R/σ` term) rather than absorbed
    into the energy exponent.  This is the genuine research core of Phase G. -/
theorem global_levelset (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  sorry

/-! ## G7 support. Elementary Gaussian integer-sum bound (note 38 §7) -/

/-
**Gaussian integer-sum lemma (note 38 §7, step II).**  For `0 < A ≤ 1`,
    `∑_{m ∈ ℤ} exp(-A·m²) ≤ 1 + 6/√A`.

    Proof: the `m = 0` term contributes `1`; by symmetry the rest is
    `2·∑_{m ≥ 1} exp(-A·m²)`.  Split that tail at `1/√A`: for `m ≤ 1/√A` use
    `exp ≤ 1` (at most `1/√A + 1` terms — bounded by `2/√A`), and for
    `m > 1/√A` use `m² ≥ m/√A` so `exp(-A·m²) ≤ exp(-√A·m)`, a geometric tail
    summing to `≤ 1/(√A·(1 - e^{-√A})) ≤ 2/(√A·√A)`… ; collecting gives the
    stated `1 + 6/√A`.
-/
lemma gaussian_int_sum_le (A : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∑' m : ℤ, Real.exp (-A * (m : ℝ) ^ 2) ≤ 1 + 6 / Real.sqrt A := by
  -- Let s := Real.sqrt A, so 0 < s ≤ 1 and s^2 = A (since 0 < A ≤ 1).
  set s := Real.sqrt A with hs_def
  have hs_pos : 0 < s := by
    exact Real.sqrt_pos.mpr hA0
  have hs_le_one : s ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, by linarith ⟩
  have hs_sq_eq_A : s^2 = A := by
    exact Real.sq_sqrt hA0.le;
  -- The sum over ℤ is 1 + 2 * ∑'_{n≥1} exp(-A*n^2).
  have h_sum_decomp : ∑' m : ℤ, Real.exp (-A * m ^ 2) = 1 + 2 * ∑' n : ℕ, Real.exp (-A * (n + 1) ^ 2) := by
    have h_sum_decomp : ∑' m : ℤ, Real.exp (-A * m ^ 2) = ∑' m : ℕ, Real.exp (-A * m ^ 2) + ∑' m : ℕ, Real.exp (-A * (-(m + 1) : ℤ) ^ 2) := by
      rw [ ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
      rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
      · norm_num [ Equiv.intEquivNatSumNat ];
      · have h_summable : Summable (fun n : ℕ => Real.exp (-A * n ^ 2)) := by
          have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hA0 ) );
          exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
        simpa using h_summable;
      · norm_num [ Equiv.intEquivNatSumNat ];
        have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ) );
        exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; nlinarith;
    rw [ h_sum_decomp, Summable.tsum_eq_zero_add ] <;> norm_num ; ring;
    have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hA0 ) );
    exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
  -- For 1 ≤ n ≤ N: exp(-A n^2) ≤ 1; there are ≤ N ≤ 1/s such terms, contributing ≤ 1/s.
  have h_tail_bound : ∑' n : ℕ, Real.exp (-A * (n + 1) ^ 2) ≤ ∑ n ∈ Finset.range (Nat.floor (1 / s)), Real.exp (-A * (n + 1) ^ 2) + ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) := by
    rw [ ← Summable.sum_add_tsum_nat_add ];
    refine' add_le_add le_rfl ( Summable.tsum_le_tsum _ _ _ );
    · intro i; rw [ ← hs_sq_eq_A ] ; ring_nf; norm_num;
      nlinarith only [ show ( 0 : ℝ ) ≤ s * i by positivity, show ( 0 : ℝ ) ≤ s * ⌊s⁻¹⌋₊ by positivity, show ( 0 : ℝ ) ≤ s ^ 2 * i by positivity, show ( 0 : ℝ ) ≤ s ^ 2 * ⌊s⁻¹⌋₊ by positivity, Nat.lt_floor_add_one ( s⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hs_pos ), hs_pos, hs_le_one ];
    · have h_summable : Summable (fun n : ℕ => Real.exp (-A * n ^ 2)) := by
        have := Real.summable_exp_nat_mul_of_ge ( show -A < 0 by linarith ) ( show ∀ n : ℕ, ( n : ℝ ) ≤ n ^ 2 by intros n; norm_cast; nlinarith );
        convert this using 1;
      exact_mod_cast h_summable.comp_injective ( add_left_injective ( ⌊1 / s⌋₊ + 1 ) );
    · have h_geo_series : Summable (fun n : ℕ => (Real.exp (-s)) ^ (n + Nat.floor (1 / s) + 1)) := by
        exact Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; linarith ) ) fun a b h => by simpa using h;
      convert h_geo_series using 2 ; norm_num [ ← Real.exp_nat_mul ] ; ring;
    · have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ) );
      exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith ) this;
  -- The tail ∑_{n≥1} exp(-s*n) = exp(-s)/(1-exp(-s)) = 1/(exp s - 1) ≤ 1/s (because exp s - 1 ≥ s for all s).
  have h_tail_sum : ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) ≤ 1 / s := by
    have h_tail_sum : ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) = Real.exp (-s * (Nat.floor (1 / s) + 1)) / (1 - Real.exp (-s)) := by
      convert HasSum.tsum_eq ( HasSum.mul_left _ <| hasSum_geometric_of_lt_one ( by positivity ) <| show Real.exp ( -s ) < 1 from by rw [ Real.exp_lt_one_iff ] ; linarith ) using 1 ; norm_num [ ← Real.exp_nat_mul ] ; ring;
      exact tsum_congr fun n => by rw [ ← Real.exp_add ] ; ring;
    rw [ h_tail_sum, div_le_div_iff₀ ] <;> norm_num [ Real.exp_neg ];
    · field_simp;
      rw [ mul_comm ];
      gcongr;
      · exact le_mul_of_one_le_right hs_pos.le ( by linarith );
      · linarith [ Real.add_one_le_exp s ];
    · exact inv_lt_one_of_one_lt₀ <| by norm_num; positivity;
    · positivity;
  -- For 1 ≤ n ≤ N: exp(-A n^2) ≤ 1; there are ≤ N ≤ 1/s such terms, contributing ≤ 1/s.
  have h_tail_bound : ∑ n ∈ Finset.range (Nat.floor (1 / s)), Real.exp (-A * (n + 1) ^ 2) ≤ Nat.floor (1 / s) := by
    exact le_trans ( Finset.sum_le_sum fun _ _ => Real.exp_le_one_iff.mpr <| by nlinarith ) <| by norm_num;
  ring_nf at *;
  norm_num [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ] at * ; nlinarith [ Nat.floor_le ( inv_nonneg.mpr hs_pos.le ), mul_inv_cancel₀ hs_pos.ne' ]

/-! ## G7. Prop 8.1 — global control partition (note 34 G7) -/

/-- The "main arc" set `𝔐_C` (note 34 G6): global assignments that are globally
    diagonal with a small common label `|m| ≤ C/sigmaCtrl`. -/
def mainArc (BS : BlockSystem) (C : ℝ) : Set (GlobalAssignment BS) :=
  {a | ∃ m : ℤ, |(m : ℝ)| ≤ C / sigmaCtrl BS ∧
        ∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (m : ZMod p.1)}

/-- **G7 (global control partition, Prop 8.1), final useful form.**  With the
    construction fixed (`k₀ ≥ k₀(c,η)`), the Peierls floor beats the
    `exp(A * numBlocks BS)` factor.  Thus the off-main-arc Laplace sum is bounded
    by an arbitrarily small `η/sigmaCtrl` term plus the one-dimensional Gaussian
    tail.

    **Status**: named `sorry` — Laplace/dyadic summation of `global_levelset`
    (via `SBEEAssembly.partfun_series_bound`) plus the G6 main-arc localization
    (note 34 G7).  Depends on the still-open `global_levelset`. -/
theorem global_control_partition (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (η + Ctail * Real.exp (-C ^ 2 * c / 2)) /
          sigmaCtrl BS := by
  sorry


end GlobalControl

end