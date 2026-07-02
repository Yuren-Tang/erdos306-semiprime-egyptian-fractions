import RequestProject.GlobalControl.BoundaryPenalty
import RequestProject.GlobalControl.LevelSetCover

/-!
# Level-set parameter admissibility

Energy-budget and dominant-label arguments placing canonical encoding data in
the admissible parameter spaces.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

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

end GlobalControl

end
