/-
# Cold-block bounds

Energy-budget identities, exception-set control, cold-label bounds, and the
cross-block penalty forced by a boundary between distinct cold labels.
-/
import RequestProject.Core.Asymptotics
import RequestProject.GlobalControl.BlockEntropy
import RequestProject.LocalEnergy.DominantLabel

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ### G5 assembly (note 40 §2): energy budget lemmas -/

/-- The bipartite cross-energy of block `k` (note 40 §3d-i). -/
def Xen (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  ∑ pq ∈ bipartitePairs BS k,
    ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2

/-
**Note 40 §3a (`sum_blockEnergy_le`).**  The per-block internal energies
    sum to at most `R`.
-/
lemma sum_blockEnergy_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Icc BS.k0 BS.K, blockEnergy BS a k ≤ R := by
  refine le_trans ?_ hR;
  refine le_trans ?_ ( energy_splits BS a );
  exact le_add_of_le_of_nonneg ( Finset.sum_le_sum fun _ _ => le_rfl ) ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ )

/-
**Note 40 §3b (`sum_shellVec_le`).**  The shell vector sums to at most `R`.
-/
lemma sum_shellVec_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Icc BS.k0 BS.K, (shellVec BS a k : ℝ) ≤ R := by
  refine' le_trans _ ( sum_blockEnergy_le BS a R hR );
  exact Finset.sum_le_sum fun _ _ => Nat.floor_le <| Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
**Note 40 §3b (`shellVec_le_floorR`).**  Each shell coordinate is at most
    `⌊R⌋₊`.
-/
lemma shellVec_le_floorR (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (_hR0 : 0 ≤ R) (hR : Qctrl BS a ≤ R) (k : ℕ) (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    shellVec BS a k ≤ ⌊R⌋₊ := by
  refine Nat.floor_mono ?_;
  exact le_trans ( Finset.single_le_sum ( fun x _ => show 0 ≤ blockEnergy BS a x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) hk ) ( sum_blockEnergy_le BS a R hR )

/-
**Note 40 §3c (`sum_Rw_hot_le`).**  The hot-floor weights sum to at most `R`.
-/
lemma sum_Rw_hot_le (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ hotSet BS c2 a, Rw c2 k ≤ R := by
  refine' le_trans _ ( sum_blockEnergy_le BS a R hR );
  refine' le_trans ( Finset.sum_le_sum fun k hk => _ ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ );
  exact Finset.mem_filter.mp hk |>.2

/-
**Note 40 §3d-i (`sum_bipartite_le`).**  The bipartite cross-energies sum to
    at most `R`.
-/
lemma sum_bipartite_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Ico BS.k0 BS.K, Xen BS a k ≤ R := by
  refine' le_trans _ hR;
  refine' le_trans _ ( energy_splits BS a );
  exact le_add_of_nonneg_of_le ( Finset.sum_nonneg fun _ _ => by exact_mod_cast QP_nonneg _ _ ) ( Finset.sum_le_sum fun _ _ => by rfl )

/-- The exception primes of (cold) block `k`: primes where the assignment
    deviates from the dominant label `coldLabel`. -/
def excSet (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : Finset ℕ :=
  (BS.P k).filter (fun p => toPlain BS a p ≠ ((coldLabel BS a k : ℤ) : ZMod p))

lemma excSet_subset (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    excSet BS a k ⊆ BS.P k := Finset.filter_subset _ _

/-
For `p ∈ BS.P k` with `k ∈ [k0,K]`, the restriction agrees with the
    extension `toPlain`.
-/
lemma restrict_eq_toPlain (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (_hk : k ∈ Finset.Icc BS.k0 BS.K) (p : {p : ℕ // p ∈ BS.P k}) :
    restrict BS a k p = toPlain BS a (p : ℕ) := by
  unfold restrict toPlain; simp +decide [ * ] ;

/-
The exception count equals the `attach`-form exception count of
    `cold_exception_bound`.
-/
lemma excSet_card_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    (excSet BS a k).card =
      ((BS.P k).attach.filter
        (fun q => restrict BS a k q ≠ ((coldLabel BS a k : ℤ) : ZMod (q : ℕ)))).card := by
  convert Finset.card_image_iff.mpr _ using 1;
  rotate_left;
  exact ℕ;
  exact fun q => q.val;
  infer_instance;
  · exact fun x hx y hy hxy => Subtype.ext hxy;
  · congr! 1;
    ext; simp [excSet];
    exact ⟨ fun h => ⟨ h.1, by simpa [ restrict_eq_toPlain BS a k hk ] using h.2 ⟩, fun h => ⟨ h.1, by simpa [ restrict_eq_toPlain BS a k hk ] using h.2 ⟩ ⟩

/-
The conforming count `card (P k \ excSet)` equals `classCount` of the
    dominant label.
-/
lemma conform_card_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    (BS.P k \ excSet BS a k).card = classCount BS a k (coldLabel BS a k) := by
  refine' Finset.card_bij _ _ _ _;
  use fun x hx => ⟨ x, Finset.mem_sdiff.mp hx |>.1 ⟩;
  · simp +contextual [ restrict_eq_toPlain BS a k hk, excSet ];
  · aesop;
  · simp +decide [ excSet, restrict_eq_toPlain BS a k hk ];
    tauto

/-
**Note 40 §3d-ii (`cold_exceptions_small`).**  For a cold block (`X = 2^k`
    large) the exception set is small: its cardinality is at most `e0`, hence
    the conforming set `BS.P k \ excSet` has at least `N_k - e0` primes.
-/
set_option maxHeartbeats 1600000 in
lemma cold_exceptions_small :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        ((BS.P k).card : ℝ) - e0 ≤ ((BS.P k \ excSet BS a k).card : ℝ) := by
  obtain ⟨c2, X0d, hc2, hX0d, hDom⟩ := cold_isDominant
  obtain ⟨e0, X0e, he0, hX0e, hExc⟩ := LocalEnergy.cold_exception_count_bound (1/4) (by norm_num) (by norm_num) c2 hc2
  obtain ⟨X0s, hX0s, hSize⟩ := LocalEnergy.cold_label_bound (1/4) (by norm_num) (by norm_num) c2 hc2
  obtain ⟨X0w, _, hRw⟩ := Rw_large 1 c2 hc2
  use c2, e0, max X0d (max X0e (max X0s (max X0w 16)));
  refine' ⟨ hc2, he0, by positivity, fun BS a k hk1 hk2 hk3 hk4 => _ ⟩;
  -- Apply the cold exception bound lemma to get the first part of the conjunction.
  have h_exc : (excSet BS a k).card ≤ e0 := by
    rw [ excSet_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ];
    apply hExc (2 ^ k) (by
    exact le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) ( mod_cast hk3 )) (BS.P k) (by
    exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩) (by
    convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ]) (restrict BS a k) (coldLabel BS a k) (max 1 (blockEnergy BS a k)) (by
    exact le_max_left _ _) (by
    exact le_max_of_le_right ( by rw [ blockEnergy ] )) (by
    simp +zetaDelta at *;
    unfold isHot at hk4; norm_num [ Rw ] at hk4;
    exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk4 ⟩) (by
    apply hSize (2 ^ k) (by
    exact_mod_cast le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_left _ _ ) ) ) hk3) (BS.P k) (by
    exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩) (by
    convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ]) (restrict BS a k) (coldLabel BS a k) (max 1 (blockEnergy BS a k)) (by
    exact le_max_left _ _) (by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (coldLabel_spec BS a k (hDom BS a k
        (by linarith [le_max_left X0d (max X0e (max X0s (max X0w 16)))])
        hk1 hk2 hk4)).1) (by
    have := coldLabel_spec BS a k ( hDom BS a k ( by linarith [ le_max_left X0d ( max X0e ( max X0s ( max X0w 16 ) ) ) ] ) hk1 hk2 hk4 ) ; norm_num at * ; linarith;) (by
    exact le_max_of_le_right ( by rw [ blockEnergy ] )) (by
    simp +zetaDelta at *;
    unfold isHot at hk4; norm_num [ Rw ] at hk4;
    exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk4 ⟩)) (by
    have := coldLabel_spec BS a k ( hDom BS a k ( by linarith [ le_max_left X0d ( max X0e ( max X0s ( max X0w 16 ) ) ) ] ) hk1 hk2 hk4 ) ; norm_num at * ; linarith;);
  rw [ Finset.card_sdiff ] ; norm_num [ h_exc ];
  rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a k ) ] ; rw [ Nat.cast_sub ( Finset.card_le_card ( excSet_subset BS a k ) ) ] ; linarith;

/-
**Sharper cold-label size bound** (note 40 §3d-iii needs `|m| ≤ N·X/64`,
    a factor `4` stronger than `cold_label_size`).  Proof identical in shape to
    `LocalEnergy.cold_label_bound`, with the polynomial threshold widened.
-/
lemma cold_label_size64 (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1],
          (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) →
          (X : ℝ) / (2 * Real.log X) ≤ P.card →
          ∀ (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
          |m| ≤ (X : ℤ) ^ 2 / 2 →
          (1 - (1/4:ℝ)) * (P.card : ℝ) ≤ ((P.attach.filter
              (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
          QP P a ≤ R → R ≤ c2 * X / (Real.log X) ^ 3 →
            |(m : ℝ)| ≤ (P.card : ℝ) * (X : ℝ) / 64 := by
  obtain ⟨ X0K, hX0K ⟩ :=RequestProject.eventually_const_mul_log_le_nat ( 1677721600 * c2 / 9 );
  obtain ⟨ X0d, hX0d ⟩ := RequestProject.eventually_const_mul_log_le_nat 64 ; refine' ⟨ Max.max 16 ( Max.max ⌈X0K⌉₊ ⌈X0d⌉₊ ), _, _ ⟩ <;> norm_num;
  intro X hX₁ hX₂ hX₃ P _ hP hP' a m R hR₁ hR₂ hR₃ hR₄ hR₅; have := hX0K.2 X hX₂; have := hX0d.2 X hX₃;
  -- By `theoremA_label_range X _ P hP (hN:8≤N) (1/4) _ _ a m R hm hclass hQ`, `|(m:ℝ)| ≤ (20/3)·√R/sigmaP P`.
  have h_bound : |(m : ℝ)| ≤ (20 / 3) * Real.sqrt R / sigmaP P := by
    have h_bound : |(m : ℝ)| ≤ (5 / (1 - 1 / 4)) * Real.sqrt R / sigmaP P := by
      have hN : 8 ≤ P.card := by
        exact_mod_cast ( by nlinarith [ show ( X : ℝ ) ≥ 16 by norm_cast, Real.log_pos ( show ( X : ℝ ) > 1 by norm_cast; linarith ), mul_div_cancel₀ ( X : ℝ ) ( show ( 2 * Real.log X ) ≠ 0 by exact mul_ne_zero two_ne_zero <| ne_of_gt <| Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith ) ] : ( 8 : ℝ ) ≤ P.card )
      convert LocalEnergy.dominant_label_bound X ( by linarith ) P hP hN ( 1 / 4 ) ( by positivity ) ( by norm_num ) a m R _ _ _ using 1 <;> norm_num at *;
      · grind +revert;
      · convert hR₂ using 1;
      · convert hR₃ using 1;
      · exact hR₄;
    exact h_bound.trans_eq ( by ring );
  -- By `sigmaP_lower X _ P hP (hN2:2≤N)`, `sigmaP P ≥ N/(8X²) > 0`, so `1/sigmaP P ≤ 8X²/N` and `|(m:ℝ)| ≤ (20/3)·√R·8X²/N = (160/3)·√R·X²/N`.
  have h_sigmaP_lower : 1 / sigmaP P ≤ 8 * (X : ℝ) ^ 2 / P.card := by
    have h_sigmaP_lower : sigmaP P ≥ (P.card : ℝ) / (8 * (X : ℝ) ^ 2) := by
      convert LocalEnergy.block_deviation_lower_bound X ( by linarith ) P _ _ using 1;
      · exact fun p => ‹∀ a ∈ P, NeZero a› p p.2;
      · assumption;
      · contrapose! hP';
        interval_cases _ : P.card <;> norm_num at *;
        · exact div_pos ( by positivity ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) );
        · rw [ lt_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( X : ℝ ) > 1 by norm_cast; linarith ), show ( X : ℝ ) ≥ 16 by norm_cast ];
    have hPcard : 0 < P.card := by
      by_contra h
      have hzero : P.card = 0 := Nat.eq_zero_of_not_pos h
      rw [hzero] at hP'
      norm_num at hP'
      exact (not_le_of_gt (div_pos (by positivity)
        (mul_pos zero_lt_two (Real.log_pos (by norm_cast; linarith))))) hP'
    calc
      1 / sigmaP P ≤ 1 / ((P.card : ℝ) / (8 * (X : ℝ) ^ 2)) :=
        one_div_le_one_div_of_le
          (div_pos (by exact_mod_cast hPcard) (by positivity)) h_sigmaP_lower
      _ = 8 * (X : ℝ) ^ 2 / P.card := by
        field_simp
  -- So it suffices to show `(160/3)·√R·X²/N ≤ N·X/64`, i.e. `√R ≤ 3·N²/(64·160·X) = 3N²/(10240·X)`, i.e. (squaring, both sides ≥0) `R ≤ 9·N⁴/(10240²·X²) = 9·N⁴/(104857600·X²)`.
  suffices h_suff : R ≤ 9 * (P.card : ℝ) ^ 4 / (104857600 * (X : ℝ) ^ 2) by
    refine le_trans h_bound ?_;
    convert mul_le_mul_of_nonneg_left ( mul_le_mul h_sigmaP_lower ( Real.sqrt_le_sqrt h_suff ) ( by positivity ) ( by positivity ) ) ( by positivity : ( 0 : ℝ ) ≤ 20 / 3 ) using 1 ; ring;
    field_simp;
    rw [ eq_div_iff ] <;> norm_num [ show X ≠ 0 by linarith, show P.card ≠ 0 by exact Nat.ne_of_gt <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty <| by rintro rfl; norm_num at * ; linarith [ show ( X : ℝ ) ≥ 16 by norm_cast ] ] ; ring_nf;
    rw [ show ( P.card : ℝ ) ^ 4 = ( P.card ^ 2 ) ^ 2 by ring, Real.sqrt_sq ( by positivity ) ] ; norm_num [ mul_comm, ne_of_gt ( by positivity : 0 < X ) ];
  refine' le_trans hR₅ _;
  rw [ div_le_div_iff₀ ];
  · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( show ( P.card : ℝ ) ≥ X / ( 2 * Real.log X ) by exact hP' ) 4 ) ( by positivity ) ) ( by positivity ) ) ; ring_nf at * ; norm_num at *;
    field_simp;
    rw [ le_div_iff₀ ( Real.log_pos ( by norm_cast; linarith ) ) ] ; linarith;
  · exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  · positivity

set_option maxHeartbeats 1600000 in
/-- **Bundled cold-block facts.**  Produces the global cold constants `c2,e0`
    and, for every cold block, (i) a small exception set, (ii) a sharp label
    bound `|coldLabel| ≤ N·X/64`, and (iii) the conforming primes carry the
    label.  This is the per-block input to the boundary penalty. -/
lemma cold_block_facts :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p)) := by
  obtain ⟨c2, X0d, hc2, hX0d, hDom⟩ := cold_isDominant;
  obtain ⟨e0, X0e, he0, hX0e, hExc⟩ := LocalEnergy.cold_exception_count_bound (1/4) (by norm_num) (by norm_num) c2 hc2;
  obtain ⟨X0s6, hX0s6, hSize6⟩ := cold_label_size64 c2 hc2
  obtain ⟨X0w, _, hRw⟩ := Rw_large 1 c2 hc2;
  refine' ⟨ c2, e0, Max.max X0d ( Max.max X0e ( Max.max X0s6 ( Max.max X0w 16 ) ) ), hc2, he0, _, _ ⟩ <;> norm_num;
  intro BS a k hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8
  have hcold := coldLabel_spec BS a k (hDom BS a k hk3 hk1 hk2 hk8)
  have hcold_size : |coldLabel BS a k| ≤ ((2 ^ k : ℕ) : ℤ) ^ 2 / 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcold.1
  refine' ⟨ _, _, _ ⟩;
  · convert hExc ( 2 ^ k ) ( mod_cast hk4 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
      exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) ( by
      unfold isHot at hk8; norm_num [ Rw ] at hk8; ring_nf at *;
      norm_num [ Real.log_pow ] at *;
      ring_nf at *;
      refine' ⟨ _, le_of_lt hk8 ⟩;
      calc
        1 ≤ Rw c2 k :=
          hRw k (Nat.pos_of_ne_zero (by rintro rfl; linarith [Nat.le_ceil X0d])) hk6
        _ = c2 * (Real.log 2)⁻¹ ^ 3 * (k : ℝ)⁻¹ ^ 3 * 2 ^ k := by
          rw [Rw, Real.log_pow]
          ring
    ) ( by
      convert hSize6 ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
        exact hcold_size ) ( by
        exact hcold.2 ) ( by
        exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
      constructor <;> intro h;
        · convert hSize6 ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
          exact hcold_size ) ( by
          exact hcold.2 ) ( by
          exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
      · refine' le_trans ( h _ ) _;
        · unfold isHot at hk8; norm_num [ Rw ] at hk8;
          norm_num [ Real.log_pow ] at *;
          exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk8 ⟩;
        · gcongr ; norm_num ) ( by
      exact hcold.2 ) using 1;
    convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( excSet_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ) using 1;
  · convert hSize6 ( 2 ^ k ) ( by exact_mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( Max.max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
      exact hcold_size ) ( by
      exact hcold.2 ) ( by
      exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
    norm_num +zetaDelta at *;
    exact ⟨ fun h => fun _ _ => h, fun h => h ( by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith ) ( by unfold isHot at hk8; norm_num [ Rw ] at hk8; linarith ) ⟩;
  · unfold excSet; aesop;

set_option maxHeartbeats 2000000 in
/-- **Note 40 §3d-iii/3d-iv master cold lemma.**  Produces the global cold
    constants and, besides the per-cold-block facts, the boundary penalty floor:
    every mismatch-boundary block contributes bipartite energy `≥ Pifloor`. -/
lemma boundary_penalty_per_k :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p))) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) := by
  obtain ⟨c2, e0, X0cbf, hc2, he0, hX0cbf, hCBF⟩ := cold_block_facts;
  obtain ⟨X0den, hX0den, hden⟩ := RequestProject.eventually_const_mul_log_le_nat (4*e0 + 26);
  use c2, e0, max X0cbf (max X0den 16); norm_num;
  refine' ⟨ hc2, he0, _, _ ⟩;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6; specialize hCBF BS a k hk1 hk2 hk3 hk6; aesop;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6
    set Nk := (BS.P k).card
    set Nk1 := (BS.P (k + 1)).card
    set ck := (BS.P k \ excSet BS a k).card
    set ck1 := (BS.P (k + 1) \ excSet BS a (k + 1)).card
    have hNk : 12 ≤ ck := by
      have hNk : Nk ≥ 2 * e0 + 13 := by
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
        have := hden ( 2 ^ k ) ( mod_cast hk4 ) ; norm_num at *;
        rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ) ) ( Real.log_pos one_lt_two ) ] ;
      have hck : (ck : ℝ) ≥ Nk - e0 := by
        have hck : (ck : ℝ) = Nk - (excSet BS a k).card := by
          exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card ( excSet_subset BS a k )
        generalize_proofs at *; (
        linarith [ hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) |>.1 ]);
      exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith )
    have hm : (32 : ℤ) * |coldLabel BS a k| ≤ (2 ^ k : ℤ) * ck := by
      have hck : (ck : ℝ) ≥ Nk - e0 := by
        have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
          exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
        convert add_le_add_left this.1 ck using 1 ; ring_nf;
        · rw_mod_cast [ ← Finset.card_union_of_disjoint ( Finset.disjoint_sdiff ), Finset.union_sdiff_of_subset ( excSet_subset BS a k ) ];
        · ring;
      have hck : (Nk : ℝ) ≥ 2 * e0 + 13 := by
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
        have := hden ( 2 ^ k ) ( by exact_mod_cast hk4 ) ; norm_num at *;
        rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ], Real.log_pos one_lt_two ];
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
        exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
      rw [ ← @Int.cast_le ℝ ] ; norm_num ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k ]
    have hm' : (32 : ℤ) * |coldLabel BS a (k + 1)| ≤ (2 ^ (k + 1) : ℤ) * Nk1 := by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by
        exact le_trans hk3 ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ( by
        unfold boundarySet at hk6; aesop; );
      rw [ ← @Int.cast_le ℝ ] ; push_cast ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k, pow_succ' ( 2 : ℝ ) k ]
    have hck : (ck : ℝ) ≥ Nk / 2 := by
      have hNk_ge : (Nk : ℝ) ≥ 2 * e0 + 13 := by
        have := hden ( 2 ^ k ) ( by simpa using hk4 ) ; norm_num at *;
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num at *;
        rw [ div_le_iff₀ ] at this <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ show ( 2 : ℝ ) ^ 0 = 1 by norm_num ] ) ) ) ( Real.log_pos one_lt_two ) ] ;
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) ; norm_num at * ; linarith [ show ( ck : ℝ ) = Nk - ( excSet BS a k |> Finset.card ) by exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card <| excSet_subset BS a k ] ;
    have hck1 : (ck1 : ℝ) ≥ Nk1 - e0 := by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by
        exact le_trans hk3 ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ( by
        exact Finset.mem_filter.mp hk6 |>.2.2.1 );
      simp +zetaDelta at *;
      rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a ( k + 1 ) ) ] ; linarith;
      · exact Finset.card_le_card fun x hx => by aesop;
    have hck2 : (ck : ℝ) ≥ Nk - e0 := by
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
        exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
      have hck2 : (ck : ℝ) = Nk - (excSet BS a k).card := by
        exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card <| Finset.filter_subset _ _;
      linarith
    have hck3 : (ck1 : ℝ) - 1 ≥ Nk1 - e0 - 1 := by
      linarith
    have hck4 : ((ck1 : ℝ) - 1) * (ck : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤ Xen BS a k := by
      apply consecutive_block_mismatch_energy_lower_bound BS (toPlain BS a) k
        (coldLabel BS a k) (coldLabel BS a (k + 1)) (by
      unfold boundarySet at hk6; aesop;) (excSet BS a k) (excSet BS a (k + 1)) (excSet_subset BS a k) (by
      exact hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) |>.2.2) (by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : k + 1 ≥ k ) ] ) ( by
        unfold boundarySet at hk6; aesop; ) ; aesop;) hNk hm hm'
    exact (by
    refine le_trans ?_ hck4;
    unfold Pifloor; gcongr;
    · exact pow_nonneg ( sub_nonneg_of_le <| by linarith [ show ( Nk : ℝ ) ≥ 2 * e0 + 13 by
                                                            have := BS.hdensity k hk1 ( by linarith ) ; norm_num at *;
                                                            have := hden ( 2 ^ k ) ( by exact_mod_cast hk4 ) ; norm_num at *;
                                                            rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ) ( Real.log_pos one_lt_two ) ] ] ) _;
    · have := BS.hdensity ( k + 1 ) ( by linarith [ show k + 1 ≥ BS.k0 from by linarith ] ) ( by linarith ) ; norm_num at *;
      refine' Nat.pos_of_ne_zero _;
      intro h; norm_num [ h ] at *;
      have := hden ( 2 ^ ( k + 1 ) ) ( by exact_mod_cast hk4.trans ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ; norm_num at *;
      rw [ div_le_iff₀ ] at * <;> nlinarith [ show 0 < ( k + 1 : ℝ ) * Real.log 2 by positivity, show ( 2 : ℝ ) ^ ( k + 1 ) > 0 by positivity ];
    · have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
      have := hden ( 2 ^ k ) ( mod_cast hk4 ) ; norm_num at *;
      rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ], Real.log_pos one_lt_two, mul_pos ( show ( k : ℝ ) > 0 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ] ) ( Real.log_pos one_lt_two ) ])

end GlobalControl

end
