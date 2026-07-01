import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import RequestProject.Core.Asymptotics
import RequestProject.Core.FiniteInterval
import RequestProject.LocalEnergy.CrossLabelEnergy
import RequestProject.LocalEnergy.DominantLabel.Basic

/-!
# Counting assignments with a dominant label

CRT label recovery, exception-energy bounds, and an entropy encoding control
the low-energy assignments carrying a fixed positive-density label.
-/

open Finset

namespace LocalEnergy

open scoped Classical

/-! ## Counting assignments with a dominant label -/

/-
**In-class CRT identity** (`29 §3` (A2)).  If `ap = m (mod p)` and `aq = m (mod q)`
    for an integer `m` with `2|m| < pq`, then the centered CRT representative equals `m`.
-/
lemma crtRepr_eq_label (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (m : ℤ) (hm : 2 * |m| < (p:ℤ) * q)
    (ap : ZMod p) (aq : ZMod q) (hap : ap = (m : ZMod p)) (haq : aq = (m : ZMod q)) :
    crtRepr p q ap aq = m := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, crtRepr p q ap aq - m = k * (p * q) := by
    have h_crt : (crtRepr p q ap aq : ℤ) ≡ m [ZMOD p] ∧ (crtRepr p q ap aq : ℤ) ≡ m [ZMOD q] := by
      have h_crt : (crtRepr p q ap aq : ZMod p) = ap ∧ (crtRepr p q ap aq : ZMod q) = aq := by
        exact ⟨ by simpa using crtRepr_congr_left p q ap aq ( (Nat.coprime_primes hp hq).mpr hpq ), by simpa using crtRepr_congr_right p q ap aq ( (Nat.coprime_primes hp hq).mpr hpq ) ⟩;
      simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
    have h_crt : (p * q : ℤ) ∣ (crtRepr p q ap aq - m) := by
      convert Int.coe_lcm_dvd ( Int.modEq_iff_dvd.mp h_crt.1.symm ) ( Int.modEq_iff_dvd.mp h_crt.2.symm ) using 1 ; norm_cast ; rw [ Nat.Coprime.lcm_eq_mul <| hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h ];
    exact dvd_iff_exists_eq_mul_left.mp h_crt;
  -- By `ZMod.natAbs_valMinAbs_le`, |crtRepr| ≤ pq/2. Combine with 2|m| < pq.
  have h_abs_crtRepr : |crtRepr p q ap aq| ≤ (p * q) / 2 := by
    apply crtRepr_abs_le;
    · simpa [ hpq ] using Nat.coprime_primes hp hq;
    · exact hp.pos;
    · exact hq.pos;
  rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> nlinarith [ Int.mul_ediv_add_emod ( p * q ) 2, Int.emod_nonneg ( p * q ) two_ne_zero, Int.emod_lt_of_pos ( p * q ) two_pos, abs_le.mp h_abs_crtRepr, abs_le.mp ( show |m| ≤ |m| by rfl ) ]

/-
**(A3a) Per-exception energy from a close-count bound.**  If at most half of
    the class `C` is `δ`-close to the exception vertex `q` (i.e. `|H_{pq}| ≤ δ·pq`),
    then the cross energy `∑_{p∈C}(H_{pq}/pq)²` is `≥ (|C|/2)·δ²`.  (Mirrors the
    sum-of-squares accounting in `crossLabel_energy_lower_bound`.)

The centered CRT representative lies in `(-pq/2, pq/2]`: equivalently
    `-(pq) < 2·crtRepr ≤ pq` (the strict lower bound is needed for uniqueness).
-/

lemma exception_energy_lower_bound_of_close_count
    (P : Finset ℕ) [∀ p : P, NeZero p.1] (a : BlockAssignment P)
    (C : Finset P) (q : P) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hCp : ∀ p ∈ C, Nat.Prime (p:ℕ)) (hqp : Nat.Prime (q:ℕ))
    (hclose : ((C.filter (fun p : P => |(crtRepr (p:ℕ) (q:ℕ) (a p) (a q) : ℝ)|
        ≤ δ * ((p:ℕ) * (q:ℕ)))).card : ℝ) ≤ (C.card:ℝ)/2) :
    (C.card:ℝ)/2 * δ^2 ≤
      ∑ p ∈ C, ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2 := by
  -- By definition of $Far$, we know that every element in $Far$ satisfies $|crtRepr| > δ * (p * q)$.
  have h_far : ∀ p ∈ C.filter (fun p => ¬ (|crtRepr p.1 q.1 (a p) (a q)| ≤ δ * (p.1 * q.1))), (crtRepr p.1 q.1 (a p) (a q) / (p.1 * q.1 : ℝ)) ^ 2 ≥ δ ^ 2 := by
    simp_all +decide [ div_pow, le_div_iff₀ ];
    intro p hp hpC h; rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < ( p : ℝ ) * q by exact mul_pos ( Nat.cast_pos.mpr <| Nat.Prime.pos <| hCp p hp hpC ) <| Nat.cast_pos.mpr <| Nat.Prime.pos hqp, abs_mul_abs_self <| ( crtRepr p q ( a ⟨ p, hp ⟩ ) ( a q ) : ℝ ), mul_le_mul_of_nonneg_left h.le hδ0 ] ;
  have h_sum_far : ∑ p ∈ C.filter (fun p => ¬ (|crtRepr p.1 q.1 (a p) (a q)| ≤ δ * (p.1 * q.1))), (crtRepr p.1 q.1 (a p) (a q) / (p.1 * q.1 : ℝ)) ^ 2 ≥ (C.filter (fun p => ¬ (|crtRepr p.1 q.1 (a p) (a q)| ≤ δ * (p.1 * q.1)))).card * δ ^ 2 := by
    simpa using Finset.sum_le_sum h_far;
  refine le_trans ?_ ( h_sum_far.trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _ );
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num;
  rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] ; gcongr ; rw [ Nat.cast_sub ( Finset.card_le_card <| Finset.filter_subset _ _ ) ] ; linarith;

/-
**(A2) Label range.**  For an `m`-dominant assignment of energy `≤ R`, the
    label satisfies `|m| ≤ (5/(1-ρ))·√R/σ_P`.  In-class pairs have `H_{pq}=m`
    (`crtRepr_eq_label`), so `R ≥ Q_P ≥ m²·S` with `S = ∑_{in-class}1/(pq)²`, and the
    restricted-σ comparison `S ≥ ((1-ρ)²/25)σ_P²`.
-/
set_option maxHeartbeats 1600000 in
lemma dominant_label_bound (X : ℕ) (hX : 16 ≤ X)
    (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 8 ≤ P.card)
    (ρ : ℝ) (_hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (m : ℤ) (R : ℝ)
    (hm : |m| ≤ (X:ℤ)^2 / 2)
    (hclass : (1-ρ)*(P.card:ℝ) ≤
        ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ))
    (hQ : QP P a ≤ R) :
    |(m:ℝ)| ≤ (5/(1-ρ)) * Real.sqrt R / sigmaP P := by
  -- Let $c = \text{card}(\{p \in P \mid a p = m\})$. From $hclass$, we have $(1-\rho)N \le c$.
  set c := (P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))).card
  have hc : (1 - ρ) * (P.card : ℝ) ≤ c := by
    exact hclass;
  -- From $hQ$, we have $R \ge m^2 \cdot S$ where $S = \sum_{pq \in Sset} W pq$.
  have hR_ge_m2S : R ≥ (m : ℝ) ^ 2 * (∑ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), (1 : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)) ^ 2) := by
    have hR_ge_m2S : ∀ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ))) ^ 2 = (m : ℝ) ^ 2 * (1 : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)) ^ 2 := by
      intros pq hpq
      have h_crt : crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) = m := by
        apply crtRepr_eq_label;
        all_goals norm_num [ orderedPrimePairsA ] at hpq ⊢;
        any_goals tauto;
        · exact hP _ pq.1.2 |>.1;
        · exact hP _ pq.2.2 |>.1;
        · exact ne_of_lt hpq.1;
        · rw [ Int.le_ediv_iff_mul_le ] at hm <;> norm_cast at *;
          norm_num at *;
          nlinarith [ hP _ pq.1.2, hP _ pq.2.2, show ( pq.1 : ℕ ) < pq.2 from hpq.1 ];
      rw [ h_crt ] ; ring;
    have hR_ge_m2S : ∑ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ))) ^ 2 ≤ R := by
      refine' le_trans _ hQ;
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _;
    rw [ Finset.mul_sum _ _ _ ] ; exact hR_ge_m2S.trans' ( Finset.sum_le_sum fun x hx => by aesop ) ;
  -- We need to show that $S \ge \frac{(1-\rho)^2}{25} \sigma_P^2$.
  have hS_ge_sigmaP2 : (∑ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), (1 : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)) ^ 2) ≥ (1 - ρ) ^ 2 / 25 * (sigmaP P) ^ 2 := by
    -- We need to show that $S \ge \frac{c(c-1)}{2} \cdot \frac{1}{16X^4}$.
    have hS_ge_c_c_minus_1_div_16X4 : (∑ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), (1 : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)) ^ 2) ≥ (c * (c - 1) / 2 : ℝ) * (1 / (16 * X ^ 4 : ℝ)) := by
      have hS_ge_c_c_minus_1_div_16X4 : (∑ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), (1 : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)) ^ 2) ≥ (∑ pq ∈ (orderedPrimePairsA P).filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))), (1 : ℝ) / (16 * X ^ 4 : ℝ)) := by
        refine Finset.sum_le_sum fun pq hpq => one_div_le_one_div_of_le ?_ ?_ <;> norm_cast <;> norm_num at *;
        · exact pow_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ pq.1.2 |>.1 ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ pq.2.2 |>.1 ) ) ) ) _;
        · exact le_trans ( Nat.pow_le_pow_left ( Nat.mul_le_mul ( hP _ pq.1.2 |>.2.2 ) ( hP _ pq.2.2 |>.2.2 ) ) 2 ) ( by ring_nf; norm_num );
      have h_card_filter : (Finset.filter (fun pq => pq.1 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ))) ∧ pq.2 ∈ P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))) (orderedPrimePairsA P)).card = c * (c - 1) / 2 := by
        have h_card_filter : ∀ (S : Finset P), (Finset.filter (fun pq => pq.1 ∈ S ∧ pq.2 ∈ S ∧ pq.1.1 < pq.2.1) (P.attach ×ˢ P.attach)).card = S.card * (S.card - 1) / 2 := by
          intros S
          have h_card_pairs : Finset.card (Finset.filter (fun pq => pq.1 ∈ S ∧ pq.2 ∈ S ∧ pq.1.1 < pq.2.1) (P.attach ×ˢ P.attach)) = Finset.card (Finset.powersetCard 2 S) := by
            refine' Finset.card_bij ( fun pq hpq => { pq.1, pq.2 } ) _ _ _;
            · grind;
            · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
              intros; omega;
            · simp +decide [ Finset.mem_powersetCard ];
              intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ x, y, hxy ⟩ := hb'; simp_all +decide [ Finset.subset_iff ] ;
              cases lt_or_gt_of_ne ( show x.1 ≠ y.1 from fun h => hxy.1 <| Subtype.ext h ) <;> [ exact ⟨ x.1, x.2, y.1, y.2, ⟨ hb.1, hb.2, by assumption ⟩, by aesop ⟩ ; exact ⟨ y.1, y.2, x.1, x.2, ⟨ hb.2, hb.1, by assumption ⟩, by aesop ⟩ ];
          rw [ h_card_pairs, Finset.card_powersetCard, Nat.choose_two_right ];
        convert h_card_filter ( Finset.filter ( fun p => a p = m ) P.attach ) using 1;
        congr 1 with x ; simp +decide [ orderedPrimePairsA ];
        tauto;
      rcases c with ( _ | _ | c ) <;> norm_num at *;
      · exact Finset.sum_nonneg fun _ _ => by positivity;
      · exact Finset.sum_nonneg fun _ _ => by positivity;
      · convert hS_ge_c_c_minus_1_div_16X4 using 1 ; norm_num [ h_card_filter ] ; ring_nf;
        exact Or.inl ( by rw [ Nat.cast_div ( show 2 ∣ 2 + c * 3 + c ^ 2 from even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ) ( by norm_num ) ] ; push_cast ; ring );
    -- We need to show that $\sigma_P^2 \le \frac{N(N-1)}{2} \cdot \frac{1}{X^4}$.
    have hsigmaP2_le_N_N_minus_1_div_2X4 : (sigmaP P) ^ 2 ≤ (P.card * (P.card - 1) / 2 : ℝ) * (1 / (X ^ 4 : ℝ)) := by
      have hsigmaP2_le_N_N_minus_1_div_2X4 : (sigmaP P) ^ 2 ≤ (∑ pq ∈ orderedPrimePairsA P, (1 : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)) ^ 2) := by
        unfold sigmaP; norm_num;
        rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => by positivity ) ];
      refine le_trans hsigmaP2_le_N_N_minus_1_div_2X4 ?_;
      refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le ( by positivity ) <| show ( ( x.1.1 : ℝ ) * x.2.1 ) ^ 2 ≥ X ^ 4 by
                                                                                                      norm_cast;
                                                                                                      rw [ show X ^ 4 = ( X ^ 2 ) ^ 2 by ring ] ; gcongr ; nlinarith only [ hP x.1 x.1.2, hP x.2 x.2.2 ] ; ) _ ; norm_num [ orderedPrimePairsA ];
      rw [ show ( Finset.filter ( fun pq : P × P => pq.1 < pq.2 ) ( P.attach ×ˢ P.attach ) ).card = P.card * ( P.card - 1 ) / 2 from ?_ ];
      · cases P using Finset.induction <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] at *;
        cases k : Finset.card ( insert ‹_› ‹_› ) <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
      · have h_card : Finset.card (Finset.filter (fun pq : P × P => pq.1 < pq.2) (P.attach ×ˢ P.attach)) = Finset.card (Finset.powersetCard 2 P) := by
          refine' Finset.card_bij ( fun pq hpq => { pq.1.val, pq.2.val } ) _ _ _ <;> simp +decide [ Finset.mem_powersetCard ];
          · grind;
          · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
            intros; omega;
          · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ x, y, hxy ⟩ := hb'; simp_all +decide [ Finset.subset_iff ] ;
            cases lt_or_gt_of_ne hxy.1 <;> [ exact ⟨ x, hb.1, y, ⟨ hb.2, by linarith ⟩, rfl ⟩ ; exact ⟨ y, hb.2, x, ⟨ hb.1, by linarith ⟩, by rw [ Finset.pair_comm ] ⟩ ];
        rw [ h_card, Finset.card_powersetCard, Nat.choose_two_right ];
    refine le_trans ?_ hS_ge_c_c_minus_1_div_16X4;
    refine le_trans ( mul_le_mul_of_nonneg_left hsigmaP2_le_N_N_minus_1_div_2X4 <| by positivity ) ?_;
    field_simp;
    nlinarith [ show ( P.card : ℝ ) ≥ 8 by norm_cast, mul_le_mul_of_nonneg_left hρ4 <| show ( 0 : ℝ ) ≤ P.card by positivity, mul_le_mul_of_nonneg_left hρ4 <| show ( 0 : ℝ ) ≤ c by positivity, sq_nonneg <| ( P.card : ℝ ) - 1, sq_nonneg <| ( c : ℝ ) - 1 ];
  rw [ div_mul_eq_mul_div, div_div, le_div_iff₀ ];
  · have h_sqrt : (m : ℝ) ^ 2 * ((1 - ρ) ^ 2 / 25 * (sigmaP P) ^ 2) ≤ R := by
      exact le_trans ( mul_le_mul_of_nonneg_left hS_ge_sigmaP2 <| sq_nonneg _ ) hR_ge_m2S;
    have h_sqrt : (|↑m| * ((1 - ρ) * sigmaP P)) ^ 2 ≤ 25 * R := by
      norm_num [ mul_pow ] at * ; linarith;
    nlinarith only [ h_sqrt, Real.sqrt_nonneg R, Real.sq_sqrt ( show 0 ≤ R by exact le_trans ( QP_nonneg P a ) hQ ) ];
  · exact mul_pos ( by linarith ) ( sigmaP_pos_of_two P ( fun p hp => hP p hp |>.1 ) ( by linarith ) )

/-
**σ lower bound.**  `σ_P ≥ N/(8X²)` for a dyadic prime block (`N = |P| ≥ 2`).
    Each pair term `1/(pq)² ≥ 1/(16X⁴)` and there are `C(N,2) ≥ N²/4` pairs.
-/
lemma block_deviation_lower_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card) :
    (P.card : ℝ) / (8 * (X:ℝ)^2) ≤ sigmaP P := by
  refine' Real.le_sqrt_of_sq_le _;
  refine' le_trans _ ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le _ <| pow_le_pow_left₀ ( by positivity ) ( show ( x.1.1 * x.2.1 : ℝ ) ≤ 4 * X ^ 2 by norm_cast; nlinarith [ hP x.1.1 x.1.2, hP x.2.1 x.2.2 ] ) 2 ) ; norm_num;
  · -- Since $P$ has at least 2 elements, the number of pairs is at least $P.card * (P.card - 1) / 2$.
    have h_pairs : (orderedPrimePairsA P).card ≥ P.card * (P.card - 1) / 2 := by
      have h_pairs : (orderedPrimePairsA P).card = Finset.card (Finset.powersetCard 2 P) := by
        refine' Finset.card_bij ( fun x hx => { x.1.1, x.2.1 } ) _ _ _ <;> simp +decide [ orderedPrimePairsA ];
        · grind;
        · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
          grind;
        · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; cases lt_trichotomy a b <;> aesop;
      simp_all +decide [ Nat.choose_two_right ];
    field_simp;
    norm_cast ; nlinarith [ Nat.div_mul_cancel ( show 2 ∣ #P * ( #P - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ), Nat.sub_add_cancel ( by linarith : 1 ≤ #P ) ];
  · exact sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ x.1.2 |>.1 ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ x.2.2 |>.1 ) ) ) )

/-
**Energy sub-sum.**  For disjoint vertex sets `C, E`, the cross energy between
    them is bounded by the full energy `Q_P` (the cross pairs are a sub-family of
    all ordered pairs; `crtRepr` is symmetric in its two vertices).  Mirrors
    `LocalEnergy.energy_relation`.
-/
lemma exception_subsum_le_QP (P : Finset ℕ) [∀ p : P, NeZero p.1] (a : BlockAssignment P)
    (C E : Finset P) (hCE : Disjoint C E)
    (hCp : ∀ p ∈ C, Nat.Prime (p:ℕ)) (hEp : ∀ q ∈ E, Nat.Prime (q:ℕ)) :
    ∑ q ∈ E, ∑ p ∈ C, ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q):ℝ)/((p:ℕ)*(q:ℕ)))^2 ≤ QP P a := by
  rw [ ← Finset.sum_product' ];
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
  case refine'_2 => exact Finset.image ( fun pq : P × P => if pq.1.1 < pq.2.1 then pq else ( pq.2, pq.1 ) ) ( E ×ˢ C );
  · rw [ Finset.sum_image ];
    · refine' Finset.sum_le_sum fun x hx => _;
      split_ifs <;> simp_all +decide [ mul_comm ];
      · rw [ if_pos ( by simpa using ‹x.1 < x.2› ) ];
        rw [ crtRepr_symm ];
        · exact hCp _ _ hx.2;
        · exact hEp _ _ hx.1;
        · exact ne_of_gt ‹_›;
      · rw [ if_neg ( by exact not_lt_of_ge ‹_› ) ];
    · intro x hx y hy; simp_all +decide [ Finset.disjoint_left ] ;
      grind +revert;
  · intro x hx; simp_all +decide [orderedPrimePairsA] ;
    rcases hx with ⟨ a, ha, b, hb, ⟨ haE, hbC ⟩, rfl ⟩ ; split_ifs <;> simp_all +decide [ Finset.disjoint_left ] ;
    grind;
  · exact fun _ _ _ => sq_nonneg _


/- **(A3 close) Close-count bound.**  With `δ = N/(128X)`, at most `N/2` primes of
    the class are `δ`-close to an exception vertex `q` (using `crossLabel_close_fiber_bound`). -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma dominant_exception_close_count (X : ℕ) (hX : 16 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 32 ≤ P.card)
    (ρ : ℝ) (_hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (m : ℤ)
    (hmsmall : |(m:ℝ)| ≤ (P.card:ℝ) * X / 16)
    (hCcard : (1-ρ)*(P.card:ℝ) ≤
        ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ))
    (q : P) (hqex : a q ≠ ((m:ℤ):ZMod (q:ℕ))) :
    (((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).filter (fun p : P =>
        |(crtRepr (p:ℕ) (q:ℕ) (a p) (a q):ℝ)| ≤ ((P.card:ℝ)/(128*X)) * ((p:ℕ)*(q:ℕ)))).card : ℝ)
      ≤ ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ)/2 := by
  have hq2 := hP q.1 q.2
  have hXpos : (0:ℝ) < X := by positivity
  have hXne : (X:ℝ) ≠ 0 := ne_of_gt hXpos
  have hN2X : (P.card:ℝ) ≤ 2*X := by
    exact_mod_cast RequestProject.card_le_upper_bound_of_pos P (2 * X)
      (fun p hp => (hP p hp).1.pos) (fun p hp => (hP p hp).2.2)
  have hBX : |(m:ℝ)| ≤ (X:ℝ)^2/4 := by nlinarith [abs_nonneg (m:ℝ), hN2X, hXpos, hmsmall]
  have hδ0 : (0:ℝ) ≤ (P.card:ℝ)/(128*X) := by positivity
  have hδ4 : (P.card:ℝ)/(128*X) ≤ 1/4 := by rw [div_le_iff₀ (by positivity)]; nlinarith [hN2X, hXpos]
  have hprodX : (P.card:ℝ)/(128*X)*X = (P.card:ℝ)/128 := by
    rw [div_mul_eq_mul_div, mul_comm (128:ℝ) (X:ℝ), ← div_div, mul_div_assoc, div_self hXne, mul_one]
  have hmXdiv : |(m:ℝ)|/X ≤ (P.card:ℝ)/16 := by rw [div_le_iff₀ hXpos]; nlinarith [hmsmall]
  have hClb : (1-ρ)*(P.card:ℝ) ≤ ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ) :=
    hCcard
  have hN32 : (32:ℝ) ≤ (P.card:ℝ) := by exact_mod_cast hN
  have hfinal : 2 * (2 * (2 * ((P.card:ℝ)/(128*X)) * X + |(m:ℝ)|/X) + 1)
      ≤ ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ)/2 := by
    nlinarith [hprodX, hmXdiv, hClb, hρ4, hN32, hXpos]
  have hCp : ∀ p ∈ (P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))),
      Nat.Prime (p:ℕ) ∧ X ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*X := fun p _ => hP p.1 p.2
  have hCa : ∀ p ∈ (P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))),
      a p = ((m:ℤ):ZMod (p:ℕ)) := fun p hp => (Finset.mem_filter.mp hp).2
  have hqa : a q = (((a q).valMinAbs : ℤ) : ZMod (q:ℕ)) := (ZMod.coe_valMinAbs (a q)).symm
  have hqd : ¬ ((q:ℕ):ℤ) ∣ ((a q).valMinAbs - m) := by
    intro hdvd
    apply hqex
    have h0 : (((a q).valMinAbs - m : ℤ) : ZMod (q:ℕ)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    rw [Int.cast_sub, ZMod.coe_valMinAbs, sub_eq_zero] at h0
    exact h0
  have hfib := crossLabel_close_fiber_bound X P a m ((a q).valMinAbs) (|(m:ℝ)|) (abs_nonneg _) (by omega)
    (P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))) hCp hCa (le_refl _) hBX
    q hq2.1 hq2.2.1 hq2.2.2 hqa hqd ((P.card:ℝ)/(128*X)) hδ0 hδ4
  exact le_trans hfib hfinal

/-- Pure-real arithmetic backing the per-exception energy bound. -/
lemma dominant_exception_energy_arithmetic (N X ρ c : ℝ) (hX : 0 < X) (hN : 0 < N) (hc : (1-ρ)*N ≤ c) :
    (1-ρ)*N^3/(2^15*X^2) ≤ c/2 * (N/(128*X))^2 := by
  rw [div_pow, div_le_iff₀ (by positivity)]
  have key : c/2 * (N^2/(128*X)^2) * (2^15*X^2) = c*N^2 := by field_simp; ring
  rw [key]
  nlinarith [hc, sq_nonneg N, hN]

/- **(A3) Per-exception energy.**  For a fixed label `m` with `|m| ≤ N·X/16`, every
    exception vertex `q` (`a q ≠ m mod q`) carries cross-energy over the class `C`
    at least `E₁ = (1-ρ)N³/2¹⁵X²`.  Via `crossLabel_close_fiber_bound` (close-count `≤ N/4`) and
    `exception_energy_lower_bound_of_close_count` with `δ = N/(128X)`. -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma dominant_exception_energy_lower_bound (X : ℕ) (hX : 16 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 32 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (m : ℤ)
    (hmsmall : |(m:ℝ)| ≤ (P.card:ℝ) * X / 16)
    (hCcard : (1-ρ)*(P.card:ℝ) ≤
        ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ))
    (q : P) (hqex : a q ≠ ((m:ℤ):ZMod (q:ℕ))) :
    (1-ρ)*(P.card:ℝ)^3/(2^15*(X:ℝ)^2) ≤
      ∑ p ∈ P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ))),
        ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q):ℝ)/((p:ℕ)*(q:ℕ)))^2 := by
  have hXpos : (0:ℝ) < X := by positivity
  have hNpos : (0:ℝ) < (P.card:ℝ) := by
    have h32 : (32:ℝ) ≤ P.card := by exact_mod_cast hN
    linarith
  have hclose := dominant_exception_close_count X hX P hP hN ρ hρ hρ4 a m hmsmall hCcard q hqex
  have hEC := exception_energy_lower_bound_of_close_count P a (P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))) q
    ((P.card:ℝ)/(128*X)) (by positivity) (fun p _ => (hP p.1 p.2).1) (hP q.1 q.2).1 hclose
  exact le_trans (dominant_exception_energy_arithmetic (P.card:ℝ) X ρ _ hXpos hNpos hCcard) hEC

/- **(A3+sub-sum) Exception count bound.**  An `m`-dominant assignment of energy
    `≤ R` (label small, `|m| ≤ NX/16`) has at most `2¹⁵RX²/((1-ρ)N³)` exceptions:
    each exception carries energy `≥ E₁` (`dominant_exception_energy_lower_bound`) and these
    cross-energies sum to `≤ Q_P ≤ R` (`exception_subsum_le_QP`). -/
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma dominant_exception_count_bound (X : ℕ) (hX : 16 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 32 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (m : ℤ) (R : ℝ) (_hR1 : 1 ≤ R) (hQ : QP P a ≤ R)
    (hmsmall : |(m:ℝ)| ≤ (P.card:ℝ) * X / 16)
    (hCcard : (1-ρ)*(P.card:ℝ) ≤
        ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ)) :
    ((P.attach.filter (fun q => a q ≠ ((m:ℤ):ZMod (q:ℕ)))).card : ℝ)
      ≤ 2^15 * R * (X:ℝ)^2 / ((1-ρ)*(P.card:ℝ)^3) := by
  have hXpos : (0:ℝ) < X := by positivity
  have hNpos : (0:ℝ) < (P.card:ℝ) := by
    have h32 : (32:ℝ) ≤ P.card := by exact_mod_cast hN
    linarith
  have hρ1 : (0:ℝ) < 1 - ρ := by linarith
  set E := P.attach.filter (fun q => a q ≠ ((m:ℤ):ZMod (q:ℕ))) with hEdef
  set C := P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ))) with hCdef
  set E1 := (1-ρ)*(P.card:ℝ)^3/(2^15*(X:ℝ)^2) with hE1def
  have hE1pos : 0 < E1 := by rw [hE1def]; positivity
  have hper : ∀ q ∈ E, E1 ≤ ∑ p ∈ C, ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q):ℝ)/((p:ℕ)*(q:ℕ)))^2 := by
    intro q hq
    exact dominant_exception_energy_lower_bound X hX P hP hN ρ hρ hρ4 a m hmsmall hCcard q (Finset.mem_filter.mp hq).2
  have hsum : (E.card:ℝ) * E1 ≤ ∑ q ∈ E, ∑ p ∈ C, ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q):ℝ)/((p:ℕ)*(q:ℕ)))^2 := by
    have : (E.card:ℝ) * E1 = ∑ _q ∈ E, E1 := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [this]; exact Finset.sum_le_sum hper
  have hdisj : Disjoint C E := by
    rw [Finset.disjoint_left]
    intro p hpC hpE
    exact (Finset.mem_filter.mp hpE).2 (Finset.mem_filter.mp hpC).2
  have hsub := exception_subsum_le_QP P a C E hdisj
    (fun p _ => (hP p.1 p.2).1) (fun q _ => (hP q.1 q.2).1)
  have hfin : (E.card:ℝ) * E1 ≤ R := le_trans hsum (le_trans hsub hQ)
  rw [hE1def] at hfin
  have hE1pos2 : 0 < (1-ρ)*(P.card:ℝ)^3/(2^15*(X:ℝ)^2) := by positivity
  have h1 : (E.card:ℝ) ≤ R/((1-ρ)*(P.card:ℝ)^3/(2^15*(X:ℝ)^2)) := by
    rw [le_div_iff₀ hE1pos2]; linarith [hfin]
  calc (E.card:ℝ) ≤ R/((1-ρ)*(P.card:ℝ)^3/(2^15*(X:ℝ)^2)) := h1
    _ = 2^15*R*(X:ℝ)^2/((1-ρ)*(P.card:ℝ)^3) := by rw [div_div_eq_mul_div]; ring_nf

/-
**(A4 encoding) Dominant encoding count.**  The number of assignments whose
    `m`-exception set has `≤ h` elements is `≤ ∑_{e≤h} C(N,e)(2X)^e`: an assignment
    is determined by its exception set and the residues there (outside, `a_q = m`).
    Mirrors `LocalEnergy.decoding_card_bound`.
-/
lemma dominant_assignment_encoding_bound (X : ℕ) (_hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (m : ℤ) (h : ℕ) :
    ((Finset.univ.filter (fun a : BlockAssignment P =>
        (P.attach.filter (fun q => a q ≠ ((m:ℤ):ZMod (q:ℕ)))).card ≤ h)).card : ℝ)
      ≤ ∑ e ∈ Finset.range (h+1), (Nat.choose P.card e : ℝ) * (2*(X:ℝ))^e := by
  refine' le_trans ( Nat.cast_le.mpr _ ) _;
  exact ∑ S ∈ Finset.powerset ( Finset.attach P ), if S.card ≤ h then ∏ q ∈ S, q.1 else 0;
  · have h_card : ∀ S ∈ Finset.powerset (Finset.attach P), Finset.card (Finset.filter (fun a : BlockAssignment P => {q ∈ P.attach | a q ≠ (m : ZMod q.1)} = S) Finset.univ) ≤ ∏ q ∈ S, (q.1 : ℕ) := by
      intro S hS
      have h_card : Finset.card (Finset.image (fun a : BlockAssignment P => fun q : S => a q) (Finset.filter (fun a : BlockAssignment P => {q ∈ P.attach | a q ≠ (m : ZMod q.1)} = S) Finset.univ)) ≤ ∏ q ∈ S, (q.1 : ℕ) := by
        refine' le_trans ( Finset.card_le_univ _ ) _ ; norm_num [ Finset.card_univ ];
        refine' le_of_eq _;
        refine' Finset.prod_bij ( fun x hx => x ) _ _ _ _ <;> aesop;
      rwa [ Finset.card_image_of_injOn ] at h_card;
      intro a ha b hb; simp_all +decide [ funext_iff, Finset.ext_iff ] ;
      grind;
    have h_card : Finset.card (Finset.filter (fun a : BlockAssignment P => (Finset.card (Finset.filter (fun q => a q ≠ (m : ZMod q.1)) (Finset.attach P))) ≤ h) Finset.univ) ≤ ∑ S ∈ Finset.powerset (Finset.attach P), if S.card ≤ h then Finset.card (Finset.filter (fun a : BlockAssignment P => {q ∈ P.attach | a q ≠ (m : ZMod q.1)} = S) Finset.univ) else 0 := by
      rw [ ← Finset.sum_filter ];
      rw [ ← Finset.card_biUnion ];
      · refine Finset.card_le_card ?_;
        intro a ha; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    exact h_card.trans ( Finset.sum_le_sum fun S hS => by aesop );
  · norm_num [ Finset.sum_ite ];
    refine' le_trans ( Finset.sum_le_sum fun s hs => Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun _ _ => show ( _ : ℝ ) ≤ 2 * X from _ ) _;
    · exact_mod_cast hP _ ( Subtype.mem _ ) |>.2.2;
    · simp +decide;
      rw [ show ( Finset.powerset ( Finset.attach P ) |> Finset.filter fun x => Finset.card x ≤ h ) = Finset.biUnion ( Finset.range ( h + 1 ) ) fun e => Finset.powersetCard e ( Finset.attach P ) from ?_, Finset.sum_biUnion ];
      · exact Finset.sum_le_sum fun i hi => by rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_comm ] ;
      · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by rw [ Finset.mem_powersetCard ] at hx₁ hx₂; aesop;
      · ext; simp [Finset.mem_biUnion, Finset.mem_powersetCard];
        tauto

/-
**(A4 entropy) Exception entropy.**  For `X` large, `∑_{e≤h} C(N,e)(2X)^e ≤ e^{εR}`
    when `h ≤ 2¹⁵RX²/((1-ρ)N³)` and `N ≥ X/(2 log X)` (`3h log X ≤ εR`).  Mirrors
    `LocalEnergy.entropy_inequality`.
-/
lemma dominant_encoding_entropy_bound (eps ρ : ℝ) (hε : 0 < eps) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ (X N h : ℕ) (R : ℝ),
      X0 ≤ X → 1 ≤ R → 1 ≤ N → N ≤ 2*X → (X:ℝ)/(2*Real.log X) ≤ (N:ℝ) →
      (h:ℝ) ≤ 2^15 * R * (X:ℝ)^2 / ((1-ρ)*(N:ℝ)^3) →
      ∑ e ∈ Finset.range (h+1), (Nat.choose N e : ℝ) * (2*(X:ℝ))^e ≤ Real.exp (eps * R) := by
  -- Choose X0 large enough such that for X ≥ X0, 5 * 2^18 * (Real.log X)^4 / ((1-ρ)*X) ≤ eps.
  obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℕ, (X0 ≤ ↑X → 5 * 2^18 * (Real.log X)^4 / ((1-ρ)*↑X) ≤ eps) := by
    have h_log_bound : Filter.Tendsto (fun X : ℝ => (Real.log X) ^ 4 / X) Filter.atTop (nhds 0) := by
      -- Let $y = \log X$, therefore the expression becomes $\frac{y^4}{e^y}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => y^4 / Real.exp y) Filter.atTop (nhds 0) by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
      simpa [div_eq_mul_inv, Real.exp_neg] using
        Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4;
    have := h_log_bound.const_mul ( 5 * 2 ^ 18 / ( 1 - ρ ) );
    have := this.eventually ( ge_mem_nhds <| show ( 5 * 2 ^ 18 / ( 1 - ρ ) * 0 : ℝ ) < eps by norm_num; linarith ) ; norm_num at *;
    obtain ⟨ X0, hX0 ⟩ := this; exact ⟨ ⌈X0⌉₊ + 1, by positivity, fun X hX => by
      convert hX0 X (by
        linarith [Nat.le_ceil X0,
          show (X : ℝ) ≥ ⌈X0⌉₊ + 1 by exact_mod_cast hX]) using 1
      · rfl
      · rw [div_mul_div_comm] ⟩ ;
  refine' ⟨ Max.max X0 16, _, _ ⟩ <;> norm_num;
  intro X N h R hX0 hX16 hR1 hN1 hN2 hN3 hh
  have hL : Real.log X ≥ 1 := by
    exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( X : ℝ ) ≥ 16 by norm_cast ] ) )
  have hsum : (∑ e ∈ Finset.range (h + 1), (Nat.choose N e : ℝ) * (2 * (X : ℝ)) ^ e) ≤ (h + 1) * (2 * (N : ℝ) * X) ^ h := by
    refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( show ( Nat.choose N i : ℝ ) ≤ N ^ i by exact_mod_cast Nat.le_trans ( Nat.choose_le_pow _ _ ) <| by ring_nf; norm_num ) <| by positivity ) _;
    norm_num [ ← mul_pow ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => pow_le_pow_right₀ ( by nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast, show ( X : ℝ ) ≥ 16 by norm_cast ] ) ( Finset.mem_range_succ_iff.mp ‹_› ) ) ( by norm_num; ring_nf; norm_num )
  have hlog : Real.log ((h + 1) * (2 * (N : ℝ) * X) ^ h) ≤ 5 * (h : ℝ) * Real.log X := by
    rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ];
    refine' le_trans ( add_le_add ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( show ( 2 * N * X : ℝ ) ≤ 4 * X ^ 2 by norm_cast; nlinarith ) ) ( by positivity ) ) ) _ ; ring_nf;
    rw [ show ( X : ℝ ) ^ 2 * 4 = ( X : ℝ ) ^ 2 * 2 ^ 2 by norm_num, Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow, Real.log_pow ] ; ring_nf;
    nlinarith [ show ( Real.log 2 : ℝ ) ≤ 1 by exact Real.log_two_lt_d9.le.trans ( by norm_num ), show ( Real.log X : ℝ ) ≥ 1 by exact hL ]
  have hfinal : 5 * (h : ℝ) * Real.log X ≤ eps * R := by
    have hfinal : 5 * (h : ℝ) * Real.log X ≤ 5 * 2^18 * R * (Real.log X)^4 / ((1 - ρ) * X) := by
      have hfinal : (N : ℝ) ^ 3 ≥ (X : ℝ) ^ 3 / (8 * (Real.log X) ^ 3) := by
        rw [ div_le_iff₀ ] at hN3 <;> try positivity;
        rw [ ge_iff_le, div_le_iff₀ ] <;> first | positivity | nlinarith [ pow_le_pow_left₀ ( by positivity ) hN3 3 ] ;
      have hfinal : (h : ℝ) ≤ 32768 * R * X^2 / ((1 - ρ) * (X^3 / (8 * (Real.log X)^3))) := by
        exact hh.trans ( div_le_div_of_nonneg_left ( by positivity ) ( by exact mul_pos ( by linarith ) ( by positivity ) ) ( mul_le_mul_of_nonneg_left hfinal ( by linarith ) ) );
      convert mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfinal (show (0 : ℝ) ≤ 5 by norm_num))
        (show (0 : ℝ) ≤ Real.log X by positivity) using 1
      all_goals first | rfl | ring_nf
      grind +splitImp;
    exact hfinal.trans ( by have := ‹0 < X0 ∧ ∀ X : ℕ, X0 ≤ ↑X → 5 * 2 ^ 18 * Real.log ↑X ^ 4 / ( ( 1 - ρ ) * ↑X ) ≤ eps›.2 X hX0; ring_nf at *; nlinarith )
  have hexp : (h + 1) * (2 * (N : ℝ) * X) ^ h ≤ Real.exp (eps * R) := by
    rw [ ← Real.log_le_iff_le_exp ( by positivity ) ] ; linarith
  exact le_trans hsum hexp

/-
**R-polynomial bound from the trivial-window cutoff.**  For `X` large, if
    `εR < N·log(2X)` (i.e. `R` below the trivial threshold) then
    `R ≤ N⁴(1-ρ)²/(409600 X²)` (the regime where the label is small).
-/
lemma dominant_energy_polynomial_bound (eps ρ : ℝ) (hε : 0 < eps) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ (X N : ℕ) (R : ℝ),
      X0 ≤ X → 1 ≤ R → 1 ≤ N → N ≤ 2*X → (X:ℝ)/(2*Real.log X) ≤ (N:ℝ) →
      eps*R < (N:ℝ)*Real.log (2*X) →
      R ≤ (N:ℝ)^4*(1-ρ)^2/(409600*(X:ℝ)^2) := by
  -- Choose X0 so that for all X ≥ X0, (Real.log X)^4/X ≤ eps*(1-ρ)^2/6553600 (and X ≥ 2, log X ≥ 1).
  have hX0 : ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → (Real.log X)^4 / X ≤ eps * (1 - ρ)^2 / 6553600 := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4;
    have := Metric.tendsto_nhds.mp ( this.comp ( Real.tendsto_log_atTop ) );
    norm_num [ Real.exp_neg, Real.exp_log ] at this;
    obtain ⟨ X0, hX0 ⟩ := this ( eps * ( 1 - ρ ) ^ 2 / 6553600 ) ( by exact div_pos ( mul_pos hε ( sq_pos_of_pos ( by linarith ) ) ) ( by norm_num ) ) ; exact ⟨ Max.max X0 2, by positivity, fun X hX => le_of_lt <| by simpa [ div_eq_mul_inv, abs_of_nonneg ( Real.log_nonneg <| show 1 ≤ X by linarith [ le_max_right X0 2 ] ), Real.exp_log ( show 0 < X by linarith [ le_max_right X0 2 ] ) ] using hX0 X <| le_trans ( le_max_left X0 2 ) hX ⟩ ;
  obtain ⟨ X0, hX0₁, hX0₂ ⟩ := hX0; use ⌈X0⌉₊ + 2;
  refine' ⟨ by positivity, fun X N R hX₁ hR₁ hN₁ hN₂ hN₃ hN₄ => _ ⟩;
  -- Using the bound from hX0₂, we get:
  have h_bound : 6553600 * (Real.log X)^4 ≤ eps * (1 - ρ)^2 * X := by
    have := hX0₂ X ( by linarith [ Nat.le_ceil X0, show ( X : ℝ ) ≥ ⌈X0⌉₊ + 2 by exact_mod_cast hX₁ ] ) ; rw [ div_le_iff₀ ( by linarith [ Nat.le_ceil X0, show ( X : ℝ ) ≥ ⌈X0⌉₊ + 2 by exact_mod_cast hX₁ ] ) ] at this; linarith;
  -- Using the bound from h_bound, we get:
  have h_bound' : 409600 * X^2 * Real.log (2 * X) ≤ eps * (1 - ρ)^2 * N^3 := by
    have h_bound' : 409600 * X^2 * Real.log (2 * X) ≤ eps * (1 - ρ)^2 * (X / (2 * Real.log X))^3 := by
      have h_bound' : 409600 * X^2 * Real.log (2 * X) ≤ 409600 * X^2 * (2 * Real.log X) := by
        rw [ Real.log_mul ( by positivity ) ( by norm_cast; linarith ) ];
        exact mul_le_mul_of_nonneg_left ( by linarith [ Real.log_le_log ( by norm_num ) ( show ( X : ℝ ) ≥ 2 by linarith [ Nat.le_ceil X0 ] ) ] ) ( by positivity );
      by_cases hX : Real.log X = 0 <;> simp_all +decide [ div_pow, mul_pow ];
      · rcases hX with ( rfl | rfl | hX ) <;> norm_cast at *;
      · rw [ mul_div, le_div_iff₀ ] <;> nlinarith [ show 0 < Real.log X ^ 3 by exact pow_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ hX.1, hX.2.1 ⟩ ) 3 ];
    exact h_bound'.trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg zero_le_two ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ) hN₃ 3 ) ( by exact mul_nonneg hε.le ( sq_nonneg _ ) ) );
  rw [ le_div_iff₀ ] <;> nlinarith [ show ( 0 :ℝ ) < X ^ 2 by norm_cast; nlinarith ]

/- **Label `≤ NX/16`.**  In the small-`R` regime, the label-range bound
    `(5/(1-ρ))√R/σ_P` is `≤ N·X/16` (uses `block_deviation_lower_bound`). -/
set_option maxHeartbeats 1000000 in
lemma dominant_label_linear_bound_with_divisor
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (D R : ℝ) (hD : 0 < D) (_hR0 : 0 ≤ R)
    (hRpoly : R ≤ (P.card:ℝ)^4*(1-ρ)^2/((40*D)^2*(X:ℝ)^2)) :
    (5/(1-ρ)) * Real.sqrt R / sigmaP P ≤ (P.card:ℝ) * X / D := by
  have hXpos : (0:ℝ) < X := by positivity
  have hNpos : (0:ℝ) < (P.card:ℝ) := by positivity
  have hρ1 : (0:ℝ) < 1 - ρ := by linarith
  have hσ : (P.card:ℝ)/(8*(X:ℝ)^2) ≤ sigmaP P := block_deviation_lower_bound X hX P hP hN
  have hσpos : 0 < sigmaP P := lt_of_lt_of_le (by positivity) hσ
  have hsqrtR : Real.sqrt R ≤ (P.card:ℝ)^2*(1-ρ)/((40*D)*X) := by
    rw [show (P.card:ℝ)^2*(1-ρ)/((40*D)*X) =
        Real.sqrt (((P.card:ℝ)^2*(1-ρ)/((40*D)*X))^2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have key : ((P.card:ℝ)^2*(1-ρ)/((40*D)*X))^2 =
        (P.card:ℝ)^4*(1-ρ)^2/((40*D)^2*(X:ℝ)^2) := by ring
    rw [key]; exact hRpoly
  rw [div_le_iff₀ hσpos]
  have hub : (5/(1-ρ)) * Real.sqrt R ≤ (P.card:ℝ)^2/((8*D)*(X:ℝ)) := by
    calc (5/(1-ρ)) * Real.sqrt R
        ≤ (5/(1-ρ)) * ((P.card:ℝ)^2*(1-ρ)/((40*D)*X)) :=
          mul_le_mul_of_nonneg_left hsqrtR (by positivity)
      _ = (P.card:ℝ)^2/((8*D)*(X:ℝ)) := by (field_simp; ring)
  have hlb : (P.card:ℝ)^2/((8*D)*(X:ℝ)) ≤ (P.card:ℝ)*X/D * sigmaP P := by
    have h2 : (P.card:ℝ)*X/D * ((P.card:ℝ)/(8*(X:ℝ)^2)) ≤
        (P.card:ℝ)*X/D * sigmaP P :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    calc (P.card:ℝ)^2/((8*D)*(X:ℝ))
        = (P.card:ℝ)*X/D * ((P.card:ℝ)/(8*(X:ℝ)^2)) := by field_simp
      _ ≤ (P.card:ℝ)*X/D * sigmaP P := h2
  linarith [hub, hlb]

/-- The standard `/16` specialization of the parameterized dominant-label
linear bound. -/
lemma dominant_label_linear_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (R : ℝ) (hR0 : 0 ≤ R)
    (hRpoly : R ≤ (P.card:ℝ)^4*(1-ρ)^2/(409600*(X:ℝ)^2)) :
    (5/(1-ρ)) * Real.sqrt R / sigmaP P ≤ (P.card:ℝ) * X / 16 := by
  apply dominant_label_linear_bound_with_divisor X hX P hP hN ρ hρ hρ4 16 R
    (by norm_num) hR0
  norm_num
  exact hRpoly

/- For `ε > 0`, `ρ ∈ (0, 1/4]`, and `X` large, the
    number of *dominant* low-energy assignments is at most
    `exp(ε R) · (1 + (10/(1-ρ))·√R/σ_P)`.

    The proof combines the label range
    `|m| ≤ (5/(1-ρ))·√R/σ_P`, a contribution of at least
    `N³/2¹⁵X²` from each exceptional coordinate, and the exception-encoding
    entropy bound `3e log X ≤ εR`. -/
set_option maxHeartbeats 1000000 in
theorem dominant_level_set_bound
    (eps : ℝ) (hε : 0 < eps) (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter
                (fun a : BlockAssignment P => QP P a ≤ R ∧ HasDominantLabel X P a ρ)).card : ℝ)
              ≤ Real.exp (eps * R) *
                  (1 + (10/(1-ρ)) * Real.sqrt R / sigmaP P) := by
  obtain ⟨X0e, hX0e, Hent⟩ := dominant_encoding_entropy_bound eps ρ hε hρ hρ4
  obtain ⟨X0r, hX0r, HRpoly⟩ := dominant_energy_polynomial_bound eps ρ hε hρ hρ4
  obtain ⟨X0c, hX0c, Hlog⟩ := RequestProject.eventually_const_mul_log_le_nat 64
  refine ⟨ max (max X0e X0r) (max X0c 16), by positivity, ?_ ⟩
  intro X hX P inst hP hN R hR1
  have hρ1 : (0:ℝ) < 1 - ρ := by linarith
  have hX16 : (16:ℝ) ≤ X := le_trans (le_max_of_le_right (le_max_right _ _)) hX
  have hX16' : 16 ≤ X := by exact_mod_cast hX16
  have hXe : X0e ≤ X := le_trans (le_max_of_le_left (le_max_left _ _)) hX
  have hXr : X0r ≤ X := le_trans (le_max_of_le_left (le_max_right _ _)) hX
  have hXc : X0c ≤ X := le_trans (le_max_of_le_right (le_max_left _ _)) hX
  have hXpos : (0:ℝ) < X := by linarith
  have hX1 : 1 ≤ X := by omega
  have hlogXpos : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by linarith : (1:ℝ) < X))
  have hN32 : 32 ≤ P.card := by
    have h64 := Hlog X hXc
    have h1 : (32:ℝ) ≤ (X:ℝ)/(2*Real.log X) := by rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : (32:ℝ) ≤ (P.card:ℝ) := le_trans h1 hN
    exact_mod_cast h2
  have hN8 : 8 ≤ P.card := by omega
  have hσpos : 0 < sigmaP P := sigmaP_pos_of_two P (fun p hp => (hP p hp).1) (by omega)
  by_cases htriv : (2*(X:ℝ))^P.card ≤ Real.exp (eps*R)
  · have hsub : (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R ∧ HasDominantLabel X P a ρ))
        ⊆ Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R) := by
      intro a ha; rw [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.1⟩
    have hle : ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R ∧ HasDominantLabel X P a ρ)).card : ℝ)
        ≤ (2*(X:ℝ))^P.card := by
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub)) ?_
      exact LocalEnergy.levelset_card_le_pow X P (fun p hp => (hP p hp).2.2) R
    have hRHS : Real.exp (eps*R) ≤ Real.exp (eps*R) * (1 + (10/(1-ρ)) * Real.sqrt R / sigmaP P) := by
      have hnn : (0:ℝ) ≤ (10/(1-ρ)) * Real.sqrt R / sigmaP P := by positivity
      nlinarith [Real.exp_pos (eps*R), hnn]
    linarith [le_trans hle htriv]
  · push Not at htriv
    have hRtriv : eps*R < (P.card:ℝ)*Real.log (2*X) := by
      have h1 : Real.exp (eps*R) < (2*(X:ℝ))^P.card := htriv
      have h2 := Real.log_lt_log (Real.exp_pos _) h1
      rw [Real.log_exp, Real.log_pow] at h2
      linarith
    have hN2X : P.card ≤ 2*X := RequestProject.card_le_upper_bound_of_pos P (2 * X)
      (fun p hp => (hP p hp).1.pos) (fun p hp => (hP p hp).2.2)
    have hRpoly := HRpoly X P.card R hXr hR1 (by omega) hN2X hN hRtriv
    have hLNX := dominant_label_linear_bound X hX1 P hP (by omega) ρ hρ hρ4 R (by linarith) hRpoly
    set L := (5/(1-ρ)) * Real.sqrt R / sigmaP P with hLdef
    have hL0 : 0 ≤ L := by rw [hLdef]; positivity
    set Mlab : Finset ℤ := Finset.Icc (-⌊L⌋) ⌊L⌋ with hMdef
    set fib : ℤ → Finset (BlockAssignment P) := fun m =>
      Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R ∧
        (1-ρ)*(P.card:ℝ) ≤ ((P.attach.filter (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ)) with hfibdef
    have hcover : (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R ∧ HasDominantLabel X P a ρ))
        ⊆ Mlab.biUnion fib := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨_, hQ, m0, hm0abs, hm0class⟩ := ha
      have hrange := dominant_label_bound X hX16' P hP hN8 ρ hρ hρ4 a m0 R hm0abs hm0class hQ
      rw [← hLdef] at hrange
      rw [Finset.mem_biUnion]
      refine ⟨m0, ?_, ?_⟩
      · rw [hMdef, Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [neg_le, Int.le_floor]; push_cast; linarith [(abs_le.mp hrange).1]
        · rw [Int.le_floor]; exact (abs_le.mp hrange).2
      · rw [hfibdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hQ, hm0class⟩
    have hfibcard : ∀ m ∈ Mlab, ((fib m).card : ℝ) ≤ Real.exp (eps*R) := by
      intro m hm
      rw [hMdef, Finset.mem_Icc] at hm
      have hm1 : -(⌊L⌋:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
      have hm2 : (m:ℝ) ≤ (⌊L⌋:ℝ) := by exact_mod_cast hm.2
      have hLfL : (⌊L⌋:ℝ) ≤ L := Int.floor_le L
      have hmabs : |(m:ℝ)| ≤ (P.card:ℝ)*X/16 := by
        rw [abs_le]; constructor <;> [linarith [hm1, hLfL, hLNX]; linarith [hm2, hLfL, hLNX]]
      set Hr := 2^15*R*(X:ℝ)^2/((1-ρ)*(P.card:ℝ)^3) with hHrdef
      have hHr0 : (0:ℝ) ≤ Hr := by rw [hHrdef]; positivity
      have hfsub : fib m ⊆ Finset.univ.filter (fun a : BlockAssignment P =>
          (P.attach.filter (fun q => a q ≠ ((m:ℤ):ZMod (q:ℕ)))).card ≤ ⌊Hr⌋₊) := by
        intro a ha
        rw [hfibdef, Finset.mem_filter] at ha
        obtain ⟨_, hQa, hclassa⟩ := ha
        have hcb := dominant_exception_count_bound X hX16' P hP hN32 ρ hρ hρ4 a m R hR1 hQa hmabs hclassa
        rw [← hHrdef] at hcb
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Nat.le_floor hcb⟩
      calc ((fib m).card : ℝ)
          ≤ ((Finset.univ.filter (fun a : BlockAssignment P =>
              (P.attach.filter (fun q => a q ≠ ((m:ℤ):ZMod (q:ℕ)))).card ≤ ⌊Hr⌋₊)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hfsub
        _ ≤ ∑ e ∈ Finset.range (⌊Hr⌋₊+1), (Nat.choose P.card e : ℝ) * (2*(X:ℝ))^e :=
            dominant_assignment_encoding_bound X hX1 P hP m ⌊Hr⌋₊
        _ ≤ Real.exp (eps*R) := Hent X P.card ⌊Hr⌋₊ R hXe hR1 (by omega) hN2X hN (by rw [hHrdef]; exact Nat.floor_le hHr0)
    have hfn : (0:ℤ) ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL0
    have hMc : (Mlab.card:ℝ) = 2*(⌊L⌋:ℝ)+1 := by
      rw [hMdef, Int.card_Icc, show (⌊L⌋ + 1 - -⌊L⌋) = 2*⌊L⌋+1 by ring]
      have h1 : ((2*⌊L⌋+1).toNat : ℤ) = 2*⌊L⌋+1 := Int.toNat_of_nonneg (by linarith)
      calc (((2*⌊L⌋+1).toNat : ℕ) : ℝ) = (((2*⌊L⌋+1).toNat : ℤ) : ℝ) := by push_cast; ring
        _ = ((2*⌊L⌋+1 : ℤ) : ℝ) := by rw [h1]
        _ = 2*(⌊L⌋:ℝ)+1 := by push_cast; ring
    have hMcard : (Mlab.card:ℝ) ≤ 1 + (10/(1-ρ)) * Real.sqrt R / sigmaP P := by
      rw [hMc]
      have hLfL : (⌊L⌋:ℝ) ≤ L := Int.floor_le L
      rw [hLdef] at hLfL
      have heq : (10/(1-ρ)) * Real.sqrt R / sigmaP P = 2*((5/(1-ρ)) * Real.sqrt R / sigmaP P) := by ring
      rw [heq]; linarith [hLfL]
    calc ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R ∧ HasDominantLabel X P a ρ)).card : ℝ)
        ≤ ((Mlab.biUnion fib).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
      _ ≤ (∑ m ∈ Mlab, (fib m).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ m ∈ Mlab, Real.exp (eps*R) := by
          exact Finset.sum_le_sum (fun m hm => hfibcard m hm)
      _ = (Mlab.card : ℝ) * Real.exp (eps*R) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Real.exp (eps * R) * (1 + (10/(1-ρ)) * Real.sqrt R / sigmaP P) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hMcard (Real.exp_pos _).le




end LocalEnergy
