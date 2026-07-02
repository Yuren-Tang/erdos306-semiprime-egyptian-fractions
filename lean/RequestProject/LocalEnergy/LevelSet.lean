import RequestProject.Core.Asymptotics
import RequestProject.Core.FiniteInterval
import RequestProject.Core.LevelSetLaplace
import RequestProject.LocalEnergy.CRTModel
import RequestProject.LocalEnergy.DominantLabel
import RequestProject.LocalEnergy.FingerprintCounting

/-!
# Single-block level-set and partition bounds

This file joins the dominant-label and fingerprint-counting branches into a
uniform block-energy level-set estimate, then converts it to a Gaussian
partition-function bound.

The mathematical stages are:

* `block_level_set_bound` joins the low-energy dominant-label estimate with
  the high-energy fingerprint estimate;
* `RequestProject.partition_function_bound_of_level_sets` performs the abstract Laplace
  conversion;
* `single_block_partition_bound` applies both to dense dyadic prime blocks.
-/

open Finset

namespace LocalEnergy

open scoped Classical

/-- Dense dyadic prime-block hypothesis.

    The block `P` is a set of primes lying in a dyadic window `[X, 2X]` of
    near-maximal density `|P| ≥ X/(2 log X)`. -/
def IsDensePrimeBlock (P : Finset ℕ) : Prop :=
  ∃ X : ℕ, 0 < X ∧ (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) ∧
    (X:ℝ) / (2 * Real.log X) ≤ P.card

/-- Uniform single-block partition-function target.

    A single block-independent constant `C` such that for every dense dyadic
    prime block `P` with at least two primes, the Gaussian partition function
    saves: `∑_a exp(-c·Q_P(a)) ≤ C / σ_P`.

    The constant is uniform in `P`; dominant labels occur only inside the proof. -/
def SingleBlockPartitionBound (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p),
      IsDensePrimeBlock P → 2 ≤ P.card →
        blockPartFun P hP c ≤ C / sigmaP P

/-
**Mesh `R_C ≤ R_w` (asymptotic).**  For `X` large the fingerprint threshold
    `Cε·X^{2/3}(log X)^{4/3}` is below the window floor `cp·X/(log X)³`.
-/
lemma fingerprint_threshold_le_nondominant_threshold (cp Ceps : ℝ) (hcp : 0 < cp) (_hCeps : 0 < Ceps) :
    ∃ X1 : ℝ, 0 < X1 ∧ ∀ X : ℕ, X1 ≤ X →
      Ceps*(X:ℝ)^((2:ℝ)/3)*(Real.log X)^((4:ℝ)/3) ≤ cp*(X:ℝ)/(Real.log X)^3 := by
  obtain ⟨X1, hX1⟩ : ∃ X1 : ℝ, 0 < X1 ∧ ∀ X : ℕ, X1 ≤ X → Ceps^3 * (X : ℝ)^2 * (Real.log X)^4 ≤ cp^3 * (X : ℝ)^3 / (Real.log X)^9 := by
    obtain ⟨ X1, hX1 ⟩ := RequestProject.eventually_le_natCast_div_log_pow 13 ( Ceps^3 / cp^3 );
    refine' ⟨ Max.max X1 3, _, _ ⟩ <;> norm_num;
    intro X hX₁ hX₂; have := hX1.2 X hX₁; rw [ div_le_div_iff₀ ] at this;
    · rw [ le_div_iff₀ ( pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _ ) ] ; nlinarith [ show ( X : ℝ ) ^ 3 > 0 by positivity ] ;
    · positivity;
    · exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  refine' ⟨ Max.max X1 3, by positivity, fun X hX => _ ⟩ ; specialize hX1 ; replace hX1 := hX1.2 X ( le_trans ( le_max_left _ _ ) hX ) ; norm_num at *;
  contrapose! hX1;
  convert pow_lt_pow_left₀ hX1 ( div_nonneg ( mul_nonneg hcp.le ( Nat.cast_nonneg _ ) ) ( pow_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) _ ) ) three_ne_zero using 1 <;> ring_nf;
  norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), ← Real.rpow_mul ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ]

/-
**Unified level-set bound.** Combining dominant-label counting below the window via
    `low_energy_level_set_bound` and fingerprint counting above the window via
    `fingerprint_levelSet_bound`, every level set is bounded by
    `C₀·e^{εR}·(1 + √R/σ_P)` for all `R ≥ 1`.
-/
set_option maxHeartbeats 1000000 in
lemma block_level_set_bound (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ (C0 X1 : ℝ), 0 < C0 ∧ 0 < X1 ∧
      ∀ (X : ℕ), X1 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ C0 * Real.exp (eps*R) * (1 + Real.sqrt R / sigmaP P) := by
  obtain ⟨cp, X0c, hcp, hX0c, Hcor⟩ := LocalEnergy.low_energy_level_set_bound eps hε0 (1/4) (by norm_num) (by norm_num)
  obtain ⟨Ceps, X0f, hCeps, hX0f, Hfp⟩ := LocalEnergy.fingerprint_levelSet_bound eps hε0 hε1
  obtain ⟨Xm, hXm0, hmesh⟩ := fingerprint_threshold_le_nondominant_threshold cp Ceps hcp hCeps
  obtain ⟨X16, hX160, hX16⟩ := RequestProject.eventually_le_natCast_div_log_pow 3 (16/cp)
  obtain ⟨Xc2, hXc20, hXc2⟩ := RequestProject.eventually_le_natCast_div_log_pow 1 4;
  refine' ⟨ 20, Max.max ( Max.max X0c X0f ) ( Max.max Xm ( Max.max X16 ( Max.max Xc2 3 ) ) ), _, _, _ ⟩ <;> norm_num;
  intro X hX0c hX0f hXm hX16 hXc2 hX3 P inst hP hN R hR1
  by_cases hRle : R ≤ cp * X / (Real.log X)^3;
  · convert le_trans ( Hcor X hX0c P hP hN R hR1 hRle ) _ using 1;
    ring_nf;
    linarith [ Real.exp_pos ( eps * R ) ];
  · have hRC : Ceps * X ^ ((2 : ℝ) / 3) * (Real.log X) ^ ((4 : ℝ) / 3) ≤ R := by
      exact le_trans ( hmesh X hXm ) ( le_of_not_ge hRle );
    have hNsqrt : (P.card : ℝ) ≤ Real.sqrt R / sigmaP P := by
      have hNsqrt : (P.card : ℝ) ≤ Real.sqrt R / sigmaP P := by
        have hσub : sigmaP P ≤ (P.card : ℝ) / (X : ℝ)^2 := by
          convert block_deviation_upper_bound X ( by linarith ) P hP using 1
        have hN2X : (P.card : ℝ) ≤ 2 * X := by
          exact_mod_cast RequestProject.card_le_upper_bound_of_pos P (2 * X)
            (fun p hp => (hP p hp).1.pos) (fun p hp => (hP p hp).2.2)
        have hR16 : (16 : ℝ) ≤ R := by
          rename_i hX16' hXc2';
          have := hX16' X hX16; rw [ div_le_iff₀ ( by positivity ) ] at this; ring_nf at *; nlinarith;
        have hNsqrt : (P.card : ℝ) * sigmaP P ≤ Real.sqrt R := by
          refine le_trans ( mul_le_mul_of_nonneg_left hσub <| Nat.cast_nonneg _ ) ?_;
          rw [ mul_div, div_le_iff₀ ] <;> try positivity;
          exact le_trans ( mul_le_mul hN2X hN2X ( by positivity ) ( by positivity ) ) ( by nlinarith [ Real.sqrt_nonneg R, Real.sq_sqrt ( show 0 ≤ R by positivity ), show ( X : ℝ ) ^ 2 ≥ 0 by positivity ] );
        rwa [ le_div_iff₀ ( show 0 < sigmaP P from _ ) ];
        apply sigmaP_pos_of_two;
        · exact fun p hp => hP p hp |>.1;
        · contrapose! hN;
          interval_cases _ : #P <;> norm_num at *;
          · exact div_pos ( by positivity ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) );
          · rw [ lt_div_iff₀ ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ];
            have := Real.log_lt_sub_one_of_pos ( by positivity : 0 < ( X : ℝ ) / 2 );
            rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this;
            linarith [ this ( by linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] ), Real.log_le_sub_one_of_pos zero_lt_two ];
      exact hNsqrt;
    have hNsqrt : (P.card : ℝ) * Real.exp (eps * R) ≤ 20 * Real.exp (eps * R) * (1 + Real.sqrt R / sigmaP P) := by
      nlinarith [ Real.exp_pos ( eps * R ), show 0 ≤ Real.sqrt R / sigmaP P by exact div_nonneg ( Real.sqrt_nonneg _ ) ( show 0 ≤ sigmaP P by exact Real.sqrt_nonneg _ ) ];
    refine le_trans ?_ hNsqrt;
    convert Hfp X hX0f P hP _ R hRC using 1;
    exact Nat.cast_pos.mp ( lt_of_lt_of_le ( by exact div_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ) hN )


/-
**Single-block partition bound.**
-/
theorem single_block_partition_bound (c : ℝ) (hc : 0 < c) :
    SingleBlockPartitionBound c := by
  -- Set eps := min (c/2) (1/2). Then 0<eps, eps<c (eps≤c/2<c), eps<1 (eps≤1/2<1), and c-eps>0.
  set eps := min (c / 2) (1 / 2)
  have hε0 : 0 < eps := by
    positivity
  have hεc : eps < c := by
    exact lt_of_le_of_lt ( min_le_left _ _ ) ( half_lt_self hc )
  have hε1 : eps < 1 := by
    exact lt_of_le_of_lt ( min_le_right _ _ ) ( by norm_num );
  obtain ⟨ C0, X1, hC0, hX1, Huni ⟩ := block_level_set_bound eps hε0 hε1;
  -- Set K := C0 * Real.exp eps / (1 - Real.exp (-(c-eps)))^2.
  set K := C0 * Real.exp eps / (1 - Real.exp (-(c-eps)))^2 with hK_def;
  -- Set M := ⌈X1⌉₊.
  set M := Nat.ceil X1 with hM_def;
  refine' ⟨ Max.max ( 3 * K ) ( ( 2 * ( M : ℝ ) ) ^ ( 2 * M ) * 2 + 1 ), _, _ ⟩ <;> norm_num;
  · exact Or.inr ( by positivity );
  · intro P hP hIrv hcard2
    obtain ⟨X, hX0, hPrange, hNbound⟩ := hIrv
    haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
    have hX1nat : 1 ≤ X := hX0
    have hσpos : 0 < sigmaP P := sigmaP_pos_of_two P hP hcard2
    have hσub : sigmaP P ≤ (P.card:ℝ)/(X:ℝ)^2 := block_deviation_upper_bound X hX1nat P hPrange
    have hN2X : (P.card:ℝ) ≤ 2*X := by
      exact_mod_cast RequestProject.card_le_upper_bound_of_pos P (2 * X)
        (fun p hp => (hPrange p hp).1.pos) (fun p hp => (hPrange p hp).2.2)
    have hXr1 : (1:ℝ) ≤ X := by exact_mod_cast hX1nat
    have hσ2 : sigmaP P ≤ 2 := le_trans hσub (by rw [div_le_iff₀ (by positivity)]; nlinarith [hN2X, hXr1]);
    by_cases hXbig : X1 ≤ (X:ℝ);
    · have hlevel : ∀ R:ℝ, 1≤R → ((Finset.univ.filter (fun a:BlockAssignment P => QP P a ≤ R)).card:ℝ) ≤ C0*Real.exp (eps*R)*(1+Real.sqrt R/sigmaP P) := fun R hR => Huni X hXbig P hPrange hNbound R hR;
      have hser := RequestProject.partition_function_bound_of_level_sets (fun a:BlockAssignment P => QP P a) (fun a => QP_nonneg P a) c eps C0 (sigmaP P) hc (by positivity) (lt_of_le_of_lt (min_le_left _ _) (by linarith)) hC0.le hσpos hlevel;
      have hKge : blockPartFun P hP c ≤ K * (1 + 1 / sigmaP P) := by
        unfold blockPartFun
        rw [hK_def]
        convert hser using 1
      rw [ le_div_iff₀ hσpos ];
      refine le_trans ?_ ( le_max_left _ _ );
      nlinarith [ mul_div_cancel₀ 1 hσpos.ne', show 0 ≤ K by exact div_nonneg ( mul_nonneg hC0.le ( Real.exp_nonneg _ ) ) ( sq_nonneg _ ) ];
    · have hbpf_le : blockPartFun P hP c ≤ (2*(X:ℝ))^P.card := by
        refine' le_trans ( Finset.sum_le_sum fun a _ => Real.exp_le_one_iff.mpr _ ) _ <;> norm_num;
        · exact mul_nonneg hc.le ( QP_nonneg P a );
        · exact le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun _ _ => show ( _ : ℝ ) ≤ 2 * X from mod_cast hPrange _ ( Subtype.mem _ ) |>.2.2 ) ( by norm_num );
      have hXM : X ≤ M := by
        exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil X1 ] );
      have hb : blockPartFun P hP c ≤ (2*(M:ℝ))^(2*M) := by
        refine le_trans hbpf_le ?_;
        exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr hXM ) zero_le_two ) _ ) ( pow_le_pow_right₀ ( by linarith [ show ( M : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.ceil_pos.mpr hX1 ) ] ) ( by linarith [ show ( P.card : ℕ ) ≤ 2 * X by exact_mod_cast hN2X ] ) );
      rw [ le_div_iff₀ hσpos ];
      exact le_trans ( mul_le_mul_of_nonneg_left hσ2 <| by exact Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) <| by nlinarith [ le_max_right ( 3 * K ) ( ( 2 * M : ℝ ) ^ ( 2 * M ) * 2 + 1 ) ] ;

end LocalEnergy
