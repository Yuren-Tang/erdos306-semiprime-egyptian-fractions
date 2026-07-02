import RequestProject.GlobalControl.LevelSetCharge
import RequestProject.GlobalControl.LevelSetColdFiber
import RequestProject.GlobalControl.LevelSetRoute

/-!
# Global level-set theorem

The final composition of cold-fiber counting, charge aggregation, and the
finite encoding route.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-
The four-fold fiber sum is bounded
    by the initial label window times the shell bound times the two Peierls
    charge sums, all kept in unsimplified `exp` form for the final algebra.
    Combines `hrhs_inner`, `fiber_card_exp_bound`, `admLabels_card`,
    `label_product_le` (with `hcharge_le`), and `chargeH_le`/`chargeB_le`.
-/
lemma hrhs_charge_bound (eps c2 e0 : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (hc2 : 0 < c2) (he0 : 0 < e0) (hdomB : ColdDominance c2) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem), k0min ≤ BS.k0 → ∀ R : ℝ, 0 ≤ R →
      (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
        ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
        ((labelFin BS c2 R BS.k0).card : ℝ)
          * (Real.exp ((2 * eps + eps) * R) *
              Real.exp ((numBlocks BS : ℝ) *
                (2 * eps + Real.log (1 / (1 - Real.exp (-eps))))))
          * (Real.exp (2 * eps * R) * Real.exp (numBlocks BS))
          * (Real.exp (2 * eps * R) * Real.exp (numBlocks BS)) := by
  obtain ⟨Xf, hXf0, hfib⟩ := fiber_card_exp_bound eps heps heps1 c2 hc2 hdomB;
  obtain ⟨kf, hkf⟩ : ∃ kf : ℕ, Xf ≤ 2 ^ kf := by
    exact pow_unbounded_of_one_lt Xf one_lt_two |> fun ⟨ kf, hkf ⟩ => ⟨ kf, le_of_lt hkf ⟩
  obtain ⟨kh, hchg⟩ := hcharge_le eps c2 e0 heps hc2 he0
  obtain ⟨kb, hchB⟩ := chargeB_le eps e0 heps he0
  obtain ⟨kPnn, hPnn⟩ := Pifloor_nonneg e0 he0
  use max kf (max kh (max kb kPnn));
  intro BS hBS R hR0
  set C := (labelFin BS c2 R BS.k0).card
  set SB := Real.exp ((2 * eps + eps) * R) * Real.exp ((numBlocks BS : ℝ) * (2 * eps + Real.log (1 / (1 - Real.exp (-eps)))) );
  refine' le_trans ( Finset.sum_le_sum fun H hH => Finset.sum_le_sum fun B hB => _ ) _;
  use fun H B => C * SB * (∏ j ∈ H, Real.exp (eps * Rw c2 j)) * (∏ j ∈ B, Real.exp (eps * Pifloor BS e0 j));
  · refine' le_trans ( hrhs_inner BS c2 R eps H B heps hR0 _ ) _;
    · intro v hv ℓ hℓ;
      apply hfib;
      · exact le_trans hkf ( pow_le_pow_right₀ ( by norm_num ) ( le_trans ( le_max_left _ _ ) hBS ) );
      · exact fun k hk hkH => Finset.mem_filter.mp hv |>.2.2 k hk hkH;
    · rw [ admLabels_card ];
      convert mul_le_mul_of_nonneg_right ( label_product_le BS c2 e0 eps R H B heps.le _ _ _ ) ( show 0 ≤ SB by positivity ) using 1;
      · norm_cast;
      · ring!;
      · exact fun _ _ => div_nonneg ( mul_nonneg hc2.le ( pow_nonneg zero_le_two _ ) ) ( pow_nonneg ( Real.log_nonneg ( one_le_pow₀ ( by norm_num ) ) ) _ );
      · simp +zetaDelta at *;
        exact fun j hj => hPnn BS j ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) hj ) ] ) ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) hj ) ] ) ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) hj ) ] );
      · exact hchg BS ( by linarith [ Nat.le_max_left kf ( Max.max kh ( Max.max kb kPnn ) ), Nat.le_max_right kf ( Max.max kh ( Max.max kb kPnn ) ), Nat.le_max_left kh ( Max.max kb kPnn ), Nat.le_max_right kh ( Max.max kb kPnn ), Nat.le_max_left kb kPnn, Nat.le_max_right kb kPnn ] ) R H B;
  · simp +decide only [mul_assoc, mul_comm, mul_left_comm];
    simp +decide only [← mul_assoc, ← sum_mul];
    simp +decide only [← mul_sum];
    refine' le_trans ( mul_le_mul_of_nonneg_left ( chargeH_le eps c2 R heps hc2 BS ) ( by positivity ) ) _;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( hchB BS ( by linarith [ Nat.le_max_right kf ( Max.max kh ( Max.max kb kPnn ) ), Nat.le_max_left kh ( Max.max kb kPnn ), Nat.le_max_right kh ( Max.max kb kPnn ), Nat.le_max_left kb kPnn, Nat.le_max_right kb kPnn ] ) R ) ( by positivity ) ) ( by positivity ) ) _ ; ring_nf ; norm_num

/-
The uniform cold-fiber bound leaves only the admissible initial-label window.
Its cardinality contributes `1 + √R / sigmaCtrl BS`; the shell count and the
hot and boundary charges supply the remaining exponential factors.
-/
lemma hrhs_final (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (c2 e0 X0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) (_hX0 : 0 < X0)
    (_hdom : ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        LocalEnergy.HasDominantLabel (2 ^ k) (BS.P k) (restrict BS a k) (1/4))
    (hdomB : ColdDominance c2) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      X0 ≤ (2:ℝ) ^ BS.k0 → ∀ R : ℝ, 1 ≤ R →
        (∑ H ∈ admH BS c2 R, ∑ B ∈ admB BS e0 R, ∑ v ∈ admShells BS c2 R H,
          ∑ ℓ ∈ admLabels BS c2 R H B, (fiber BS H B v ℓ).card : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  obtain ⟨kc, hc⟩ := hrhs_charge_bound eps c2 e0 heps heps1 hc2 he0 hdomB
  obtain ⟨csig, hcsig0, hsig⟩ := sigmaCtrl_le_sigmaP_k0
  set A0 := 2 * eps + Real.log (1 / (1 - Real.exp (-eps))) + 2
  set A := A0 + |Real.log (3 + 14 * csig)| + 2
  set k0min := max kc 2
  use k0min, A;
  refine' ⟨ _, _ ⟩;
  · exact add_pos_of_pos_of_nonneg ( add_pos_of_pos_of_nonneg ( add_pos_of_pos_of_nonneg ( by positivity ) ( Real.log_nonneg ( by rw [ le_div_iff₀ ] <;> nlinarith [ Real.exp_pos ( -eps ), Real.exp_lt_one_iff.mpr ( show -eps < 0 by linarith ) ] ) ) ) zero_le_two ) ( abs_nonneg _ ) |> add_pos_of_pos_of_nonneg <| by positivity;
  · intro BS hBS hk0 hX0 R hR
    have h_sigmaCtrl_pos : 0 < sigmaCtrl BS := by
      exact sigmaCtrl_pos_of_k0 BS ( le_trans ( le_max_right _ _ ) hBS )
    have h_sigmaP_pos : 0 < sigmaP (BS.P BS.k0) := by
      contrapose! h_sigmaCtrl_pos;
      exact le_trans ( hsig BS ( le_trans ( le_max_right _ _ ) hBS ) ) ( mul_nonpos_of_nonneg_of_nonpos ( by positivity ) h_sigmaCtrl_pos )
    have h_nb : (BS.k0 : ℝ) ≤ numBlocks BS := by
      exact_mod_cast Nat.le_sub_of_add_le ( by linarith [ hk0.1, hk0.2 ] )
    have h_nb_ge_1 : 1 ≤ numBlocks BS := by
      exact Nat.one_le_iff_ne_zero.mpr ( by rw [ numBlocks ] ; exact Nat.sub_ne_zero_of_lt ( by linarith [ hk0.1 ] ) );
    refine' le_trans ( hc BS ( le_trans ( le_max_left _ _ ) hBS ) R ( by positivity ) ) _;
    refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( labelFin_k0_card_le BS c2 R ( by positivity ) ) _ ) _ ) _ ) _;
    · positivity;
    · positivity;
    · positivity;
    · -- Apply the bounds on the exponential terms and the logarithmic terms.
      have h_exp_bound : (3 + 14 * Real.sqrt R / sigmaP (BS.P BS.k0)) ≤ (3 + 14 * csig * BS.k0) * (1 + Real.sqrt R / sigmaCtrl BS) := by
        have h_exp_bound : 14 * Real.sqrt R / sigmaP (BS.P BS.k0) ≤ 14 * csig * BS.k0 * Real.sqrt R / sigmaCtrl BS := by
          field_simp;
          grind +locals;
        ring_nf at *;
        nlinarith [ show 0 ≤ Real.sqrt R * ( sigmaCtrl BS ) ⁻¹ by positivity, show 0 ≤ csig * BS.k0 by positivity ];
      have h_exp_bound : (3 + 14 * csig * BS.k0) ≤ Real.exp (|Real.log (3 + 14 * csig)|) * Real.exp (numBlocks BS) := by
        have h_exp_bound : 3 + 14 * csig * BS.k0 ≤ (3 + 14 * csig) * BS.k0 := by
          nlinarith [ show ( BS.k0 : ℝ ) ≥ 2 by norm_cast; exact le_trans ( le_max_right _ _ ) hBS ];
        refine le_trans h_exp_bound ?_;
        gcongr;
        · rw [ abs_of_nonneg ( Real.log_nonneg ( by linarith ) ), Real.exp_log ( by linarith ) ];
        · exact le_trans h_nb ( by linarith [ Real.add_one_le_exp ( numBlocks BS : ℝ ) ] );
      refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ‹_› _ ) _ ) _ ) _;
      · positivity;
      · positivity;
      · positivity;
      · refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right h_exp_bound _ ) _ ) _ ) _ ) _;
        · positivity;
        · positivity;
        · positivity;
        · positivity;
        · norm_num [ ← Real.exp_add ] ; ring_nf;
          norm_num [ A, A0 ] ; ring_nf;
          norm_num [ mul_assoc, ← Real.exp_add, ← Real.exp_nat_mul ] ; ring_nf;
          refine' add_le_add _ _;
          · rw [ mul_assoc, mul_assoc, mul_assoc, mul_comm ];
            rw [ mul_assoc, mul_assoc, ← Real.exp_add ] ; ring_nf;
            exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ show ( numBlocks BS : ℝ ) ≥ 1 by norm_cast, abs_nonneg ( Real.log ( 3 + csig * 14 ) ) ] ) <| by positivity;
          · exact Real.exp_le_exp.mpr ( by nlinarith [ show ( numBlocks BS : ℝ ) ≥ 1 by norm_cast, show ( |Real.log ( 3 + csig * 14 )| : ℝ ) ≥ 0 by positivity, show ( eps : ℝ ) ≥ 0 by positivity, show ( R : ℝ ) ≥ 1 by norm_cast ] )

/-- The global level-set estimate, obtained by composing cold dominance,
    label admissibility, fiber counting, and the finite encoding route. -/
theorem global_levelset (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  obtain ⟨c2, e0, X0, hc2, he0, hX0, hdom, hpen, hdomB⟩ := cold_master
  obtain ⟨k0L, hadmL⟩ := hadmL_final c2 X0 hc2 hdom
  obtain ⟨k0R, A, hA, hrhs⟩ := hrhs_final eps heps heps1 c2 e0 X0 hc2 he0 hX0 hdom hdomB
  obtain ⟨k0X, hX0pow⟩ : ∃ n : ℕ, X0 ≤ (2:ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X0 (by norm_num : (1:ℝ) < 2)
    exact ⟨n, le_of_lt hn⟩
  refine ⟨max k0L (max k0R k0X), A, hA, ?_⟩
  intro BS hk0 hadm R hR
  have hk0L : k0L ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  have hk0R : k0R ≤ BS.k0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk0
  have hk0X : k0X ≤ BS.k0 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk0
  have hX0k0 : X0 ≤ (2:ℝ) ^ BS.k0 :=
    le_trans hX0pow (pow_le_pow_right₀ (by norm_num) hk0X)
  refine global_levelset_route BS eps c2 e0 X0 R A (by linarith) hX0k0 ?_ ?_ ?_ ?_
  · -- hpen
    intro a _ha k hk1 hk2 hkX hkb
    exact hpen BS a k hk1 hk2 hkX hkb
  · -- hdom
    intro a _ha k hk1 hk2 hkc
    have hXk : X0 ≤ (2:ℝ) ^ k := le_trans hX0k0 (pow_le_pow_right₀ (by norm_num) hk1)
    have hnh : ¬ isHot BS c2 a k := fun h =>
      hkc (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hk2⟩, h⟩)
    exact hdom BS a k hk1 hk2 hXk hnh
  · -- hadmL
    intro a ha
    exact hadmL BS hk0L hX0k0 a R (by linarith) ha
  · -- hrhs
    exact hrhs BS hk0R hadm hX0k0 R hR

end GlobalControl

end
