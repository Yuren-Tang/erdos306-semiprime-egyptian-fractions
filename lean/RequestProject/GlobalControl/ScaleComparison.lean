import RequestProject.GlobalControl.Basic
import RequestProject.LocalEnergy.DominantLabel

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- The global control deviation is bounded by the first-block deviation, up to
an absolute constant and the number-of-scales factor `k₀`. -/
lemma sigmaCtrl_le_sigmaP_k0 :
    ∃ csig : ℝ, 0 < csig ∧
      ∀ BS : BlockSystem, 2 ≤ BS.k0 →
        sigmaCtrl BS ≤ csig * (BS.k0 : ℝ) * sigmaP (BS.P BS.k0) := by
  use 64 * Real.log 2;
  have h_sigmaP_bound : ∀ (BS : BlockSystem), 2 ≤ BS.k0 → sigmaP (BS.P BS.k0) ≥ 1 / (16 * BS.k0 * Real.log 2 * 2 ^ BS.k0) := by
    intros BS hBS
    have hN : 2 ≤ (BS.P BS.k0).card := by
      have := BS.hdensity BS.k0 le_rfl ( by linarith [ BS.hk ] );
      rw [ Real.log_pow, div_le_iff₀ ] at this <;> norm_num at *;
      · contrapose! this;
        interval_cases _ : Finset.card ( BS.P BS.k0 ) <;> norm_num at *;
        rcases n : BS.k0 with ( _ | _ | k0 ) <;> simp_all +decide [ pow_succ' ];
        exact Nat.recOn k0 ( by norm_num; have := Real.log_two_lt_d9; norm_num1 at *; linarith ) fun n ihn => by norm_num [ pow_succ' ] at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) n.zero_le ] ;
      · positivity;
    have h_sigmaP_bound : sigmaP (BS.P BS.k0) ≥ (BS.P BS.k0).card / (8 * (2 ^ BS.k0 : ℝ) ^ 2) := by
      have := @LocalEnergy.block_deviation_lower_bound ( 2 ^ BS.k0 ) ?_ ( BS.P BS.k0 ) ?_ ?_ ?_ <;> norm_num at *;
      · exact this;
      · exact one_le_pow₀ ( by norm_num );
      · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime _ _ hp ) ⟩;
      · exact fun p hp => ⟨ BS.hprime _ _ hp, BS.hwindow _ _ hp |>.1, by linarith [ BS.hwindow _ _ hp |>.2, pow_succ' 2 BS.k0 ] ⟩;
      · linarith;
    have h_density_bound : (BS.P BS.k0).card ≥ (2 ^ BS.k0 : ℝ) / (2 * BS.k0 * Real.log 2) := by
      have := BS.hdensity BS.k0 ( by linarith ) ( by linarith [ BS.hk ] );
      convert this.ge using 1 ; norm_num [ Real.log_pow ] ; ring;
    refine le_trans ?_ h_sigmaP_bound;
    rw [ div_le_div_iff₀ ] <;> try positivity;
    rw [ ge_iff_le, div_le_iff₀ ] at h_density_bound <;> nlinarith [ show 0 < ( 2 : ℝ ) ^ BS.k0 by positivity, show 0 < ( BS.k0 : ℝ ) * Real.log 2 by positivity ];
  refine' ⟨ by positivity, fun BS hBS => le_trans ( sigmaCtrl_le_geom BS hBS ) _ ⟩;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( h_sigmaP_bound BS hBS ) ?_ ) <;> ring_nf <;> norm_num;
  · norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos, show BS.k0 > 0 by linarith ];
  · positivity

end GlobalControl

end
