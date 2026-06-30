import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import RequestProject.Core.Asymptotics
import RequestProject.Core.FiniteInterval
import RequestProject.LocalEnergy.CRTModel
import RequestProject.LocalEnergy.ReciprocalDispersion

/-!
# Dominant labels for local CRT energy

An assignment has a dominant label when one integer residue is carried by a
fixed positive proportion of its prime coordinates. This file develops the
single-block theory around that notion:

* CRT representatives inside one label class recover the integer label;
* cross-label dispersion forces quadratic energy;
* low-energy dominant assignments admit a small encoding;
* nondominant assignments have energy of order `X / (log X)^3`;
* below that scale, dominant labels and their exceptional coordinates obey
  uniform bounds.

The public conclusions are `dominant_level_set_bound`,
`nondominant_energy_lower_bound`, `fixed_label_level_set_bound`,
`cold_exception_count_bound`, and `cold_label_bound`.
-/

open Finset

namespace LocalEnergy

open scoped Classical

/-! ## Dominance -/

/-- `a` is **`m`-dominant** (parameter `ρ`) if the residue label `m` agrees with
    `a_p (mod p)` on at least a `(1-ρ)` fraction of the primes `p ∈ P`, with
    `|m| ≤ X²/2` (so that the in-class CRT representatives equal `m` exactly).
    (`29 §3`.) -/
def HasDominantLabel (X : ℕ) (P : Finset ℕ) (a : BlockAssignment P) (ρ : ℝ) : Prop :=
  ∃ m : ℤ, |m| ≤ (X:ℤ)^2 / 2 ∧
    (1 - ρ) * (P.card : ℝ) ≤
      ((P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))).card : ℝ)

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
lemma two_mul_crtRepr_mem_product_interval (p q : ℕ) (hcop : Nat.Coprime p q) (hp : 0 < p) (hq : 0 < q)
    (ap : ZMod p) (aq : ZMod q) :
    -((p * q : ℕ) : ℤ) < 2 * crtRepr p q ap aq ∧ 2 * crtRepr p q ap aq ≤ ((p * q : ℕ) : ℤ) := by
  unfold crtRepr
  rw [dif_pos hcop]
  letI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne' hq.ne'⟩
  simpa [mul_comm] using
    ZMod.valMinAbs_mem_Ioc ((ZMod.chineseRemainder hcop).symm (ap, aq))

lemma crtRepr_symm (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (ap : ZMod p) (aq : ZMod q) :
    crtRepr p q ap aq = crtRepr q p aq ap := by
  obtain ⟨H, H'⟩ : ∃ H H' : ℤ, crtRepr p q ap aq = H ∧ crtRepr q p aq ap = H' ∧ (p:ℤ) * q ∣ (H - H') ∧ (-((p:ℤ) * q) < 2 * H ∧ 2 * H ≤ ((p:ℤ) * q)) ∧ (-((p:ℤ) * q) < 2 * H' ∧ 2 * H' ≤ ((p:ℤ) * q)) := by
    refine' ⟨ _, _, rfl, rfl, _, _, _ ⟩;
    · have h_cong : (crtRepr p q ap aq : ℤ) ≡ (crtRepr q p aq ap : ℤ) [ZMOD p] ∧ (crtRepr p q ap aq : ℤ) ≡ (crtRepr q p aq ap : ℤ) [ZMOD q] := by
        have h_cong : (crtRepr p q ap aq : ZMod p) = (crtRepr q p aq ap : ZMod p) ∧ (crtRepr p q ap aq : ZMod q) = (crtRepr q p aq ap : ZMod q) := by
          have := crtRepr_congr_left p q ap aq ( (Nat.coprime_primes hp hq).mpr hpq ); have := crtRepr_congr_right p q ap aq ( (Nat.coprime_primes hp hq).mpr hpq ); have := crtRepr_congr_left q p aq ap ( (Nat.coprime_primes hq hp).mpr ( Ne.symm hpq ) ); have := crtRepr_congr_right q p aq ap ( (Nat.coprime_primes hq hp).mpr ( Ne.symm hpq ) ); aesop;
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
      convert Int.coe_lcm_dvd ( Int.modEq_iff_dvd.mp h_cong.1.symm ) ( Int.modEq_iff_dvd.mp h_cong.2.symm ) using 1;
      exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h );
    · convert two_mul_crtRepr_mem_product_interval p q ( (Nat.coprime_primes hp hq).mpr hpq ) hp.pos hq.pos ap aq using 1;
      all_goals norm_num [Nat.cast_mul]
    · convert two_mul_crtRepr_mem_product_interval q p ( (Nat.coprime_primes hq hp).mpr hpq.symm ) hq.pos hp.pos aq ap using 1;
      · norm_num [ mul_comm ];
      · grind;
  obtain ⟨ H', hH₁, hH₂, hH₃, hH₄, hH₅, hH₆ ⟩ := H';
  obtain ⟨ k, hk ⟩ := hH₃; nlinarith [ show k = 0 by nlinarith ] ;

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

/-! ## Cross-label energy -/

set_option maxHeartbeats 1600000 in
open LocalEnergy in
/-- Fix a prime `q ∈ [X,2X]` carrying residue
    `n'`, with `q ∤ (n'-n)`.  The primes `p ∈ C` (residue `n`) whose cross
    representative `H_{pq}` is `δ`-small inject into `linearCongruencePairs X q U (n'-n)` via
    `p ↦ (u, p)` with `H_{pq} - n = u·p`; hence by `linearCongruence_pair_count` their number is
    `≤ 2·(2·U+1) ≤ 2·(2·(2δX + B/X) + 1)`.

    Here `H_{pq} ≡ n (mod p)` (so `p ∣ H-n`, giving the integer `u`), and
    `H_{pq} ≡ n' (mod q)`, so `u·p = H-n ≡ n'-n (mod q)`; the size bound
    `|u| ≤ δq + |n|/p ≤ 2δX + B/X` uses `|H| ≤ δpq`, `q ≤ 2X`, `X ≤ p`. -/
lemma crossLabel_close_fiber_bound (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (a : BlockAssignment P) (n n' : ℤ) (B : ℝ) (hB : 0 ≤ B) (hX : 1 ≤ X)
    (C : Finset P)
    (hCp : ∀ p ∈ C, Nat.Prime (p:ℕ) ∧ X ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*X)
    (hCa : ∀ p ∈ C, a p = ((n:ℤ) : ZMod (p:ℕ)))
    (hnB : |(n:ℝ)| ≤ B) (_hBX : B ≤ (X:ℝ)^2/4)
    (q : P) (hq : Nat.Prime (q:ℕ)) (hXq : X ≤ (q:ℕ)) (hq2X : (q:ℕ) ≤ 2*X)
    (hqa : a q = ((n':ℤ) : ZMod (q:ℕ)))
    (hqd : ¬ ((q:ℕ):ℤ) ∣ (n' - n))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (_hδ4 : δ ≤ 1/4) :
    ((C.filter (fun p : P => |(crtRepr (p:ℕ) (q:ℕ) (a p) (a q) : ℝ)|
        ≤ δ * ((p:ℕ) * (q:ℕ)))).card : ℝ)
      ≤ 2 * (2 * (2*δ*X + B/X) + 1) := by
  have h_filter : ∀ p ∈ C, |(crtRepr p.1 q.1 (a p) (a q) : ℝ)| ≤ δ * (p.1 * q.1) → ∃ u : ℤ, |u| ≤ Nat.floor (2 * δ * X + B / X) ∧ (q : ℤ) ∣ (u * p.1 - (n' - n)) := by
    intro p hp h_abs
    obtain ⟨u, hu⟩ : ∃ u : ℤ, (crtRepr p.val q.val (a p) (a q) : ℤ) - n = u * p.val := by
      have h_div : (crtRepr p.val q.val (a p) (a q) : ZMod p.val) = n := by
        have := crtRepr_congr_left p.1 q.1 ( a p ) ( a q ) ?_ <;> simp_all +decide [ Nat.coprime_primes ];
        · rintro rfl; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
      exact exists_eq_mul_left_of_dvd <| by erw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
    refine' ⟨ u, _, _ ⟩;
    · have h_u_bound : |(u : ℝ)| ≤ 2 * δ * X + B / X := by
        have h_u_bound : |(u : ℝ)| * p.val ≤ δ * (p.val * q.val) + B := by
          norm_num [ ← @Int.cast_inj ℝ ] at *;
          cases abs_cases ( u : ℝ ) <;> cases abs_cases ( crtRepr p.val q.val ( a p ) ( a q ) : ℝ ) <;> nlinarith [ abs_le.mp hnB ];
        have h_u_bound : |(u : ℝ)| * p.val ≤ δ * (p.val * 2 * X) + B := by
          exact h_u_bound.trans ( by nlinarith [ show ( q : ℝ ) ≤ 2 * X by norm_cast, show ( p : ℝ ) ≥ 0 by positivity, mul_le_mul_of_nonneg_left ( show ( q : ℝ ) ≤ 2 * X by norm_cast ) ( show ( 0 : ℝ ) ≤ δ by positivity ) ] );
        rw [ add_div', le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) ≥ X by exact_mod_cast hCp p hp |>.2.1, show ( X : ℝ ) ≥ 1 by exact_mod_cast hX ];
      exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Nat.lt_floor_add_one ( 2 * δ * X + B / X ) ] );
    · have h_div : (crtRepr p.val q.val (a p) (a q) : ZMod q.val) = n' := by
        convert crtRepr_congr_right p.val q.val ( a p ) ( a q ) _ using 1 <;> norm_num [ hqa ];
        · by_cases h : p = q <;> simp_all +decide [ Nat.coprime_primes ];
          simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
      simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
      replace hu := congr_arg ( ( ↑ ) : ℤ → ZMod q.val ) hu ; aesop;
  have h_card : (Finset.filter (fun p => |(crtRepr p.1 q.1 (a p) (a q) : ℝ)| ≤ δ * (p.1 * q.1)) C).card ≤ (Finset.filter (fun up => Nat.Prime up.2 ∧ (q : ℤ) ∣ (up.1 * (up.2 : ℤ) - (n' - n))) (Finset.product (Finset.Icc (-Nat.floor (2 * δ * X + B / X) : ℤ) (Nat.floor (2 * δ * X + B / X))) (Finset.Icc X (2 * X)))).card := by
    have h_card : (Finset.image (fun p => (p.1 : ℕ)) (Finset.filter (fun p => |(crtRepr p.1 q.1 (a p) (a q) : ℝ)| ≤ δ * (p.1 * q.1)) C)).card ≤ (Finset.filter (fun up => Nat.Prime up.2 ∧ (q : ℤ) ∣ (up.1 * (up.2 : ℤ) - (n' - n))) (Finset.product (Finset.Icc (-Nat.floor (2 * δ * X + B / X) : ℤ) (Nat.floor (2 * δ * X + B / X))) (Finset.Icc X (2 * X)))).card := by
      have h_card : Finset.image (fun p => (p.1 : ℕ)) (Finset.filter (fun p => |(crtRepr p.1 q.1 (a p) (a q) : ℝ)| ≤ δ * (p.1 * q.1)) C) ⊆ Finset.image (fun up => up.2) (Finset.filter (fun up => Nat.Prime up.2 ∧ (q : ℤ) ∣ (up.1 * (up.2 : ℤ) - (n' - n))) (Finset.product (Finset.Icc (-Nat.floor (2 * δ * X + B / X) : ℤ) (Nat.floor (2 * δ * X + B / X))) (Finset.Icc X (2 * X)))) := by
        simp +decide [ Finset.subset_iff ];
        intro x hx hx' hx''; obtain ⟨ u, hu₁, hu₂ ⟩ := h_filter ⟨ x, hx ⟩ hx' hx''; use u; simp_all +decide [ abs_le ] ;
      exact le_trans ( Finset.card_le_card h_card ) ( Finset.card_image_le );
    rwa [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] at h_card;
  refine' le_trans ( Nat.cast_le.mpr h_card ) _;
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show ( 2 * ⌊2 * δ * X + B / X⌋₊ + 1 : ℝ ) ≤ 2 * ( 2 * δ * X + B / X ) + 1 by linarith [ Nat.floor_le ( show 0 ≤ 2 * δ * X + B / X by positivity ) ] ) zero_le_two );
  exact_mod_cast LocalEnergy.linearCongruence_pair_count X q ⌊2 * δ * X + B / X⌋₊ hq hXq ( n' - n ) hqd

open LocalEnergy in
/-- The number of cross pairs `(p,q) ∈ C×C'`
    whose representative is `δ`-small is `≤ 2|C| + |C'|·2(2(2δX+B/X)+1)`.

    The `≤ 2` primes `q ∈ C'` dividing `d = n'-n` contribute `≤ |C|` pairs each
    (`card_prime_factors_dyadic_le_two`, valid as `0 < |d| ≤ 2B ≤ X²/2 < X³`); each
    remaining `q` has `q ∤ d`, so `crossLabel_close_fiber_bound` bounds its close fiber. -/
lemma crossLabel_close_pair_count (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (a : BlockAssignment P) (n n' : ℤ) (B : ℝ) (hB : 0 ≤ B) (hX : 1 ≤ X)
    (hd : n ≠ n')
    (C C' : Finset P)
    (hCp : ∀ p ∈ C, Nat.Prime (p:ℕ) ∧ X ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*X)
    (hC'p : ∀ q ∈ C', Nat.Prime (q:ℕ) ∧ X ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*X)
    (hCa : ∀ p ∈ C, a p = ((n:ℤ) : ZMod (p:ℕ)))
    (hC'a : ∀ q ∈ C', a q = ((n':ℤ) : ZMod (q:ℕ)))
    (hnB : |(n:ℝ)| ≤ B) (hn'B : |(n':ℝ)| ≤ B) (hBX : B ≤ (X:ℝ)^2/4)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : δ ≤ 1/4) :
    (((C ×ˢ C').filter (fun pq : P × P =>
        |(crtRepr (pq.1:ℕ) (pq.2:ℕ) (a pq.1) (a pq.2) : ℝ)|
          ≤ δ * ((pq.1:ℕ) * (pq.2:ℕ)))).card : ℝ)
      ≤ 2 * (C.card : ℝ) + (C'.card : ℝ) * (2 * (2 * (2*δ*X + B/X) + 1)) := by
  have h_card_prime_factors : ((Finset.Icc X (2 * X)).filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (n' - n))).card ≤ 2 := by
    convert LocalEnergy.card_prime_factors_dyadic_le_two X ( n' - n ) ( sub_ne_zero.mpr ( Ne.symm hd ) ) _ using 1;
    rw [ ← @Int.cast_lt ℝ ] ; norm_num ; cases abs_cases ( n' - n : ℝ ) <;> cases abs_cases ( n : ℝ ) <;> cases abs_cases ( n' : ℝ ) <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ X ) ] ;
  have h_card_bad : (Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C').card ≤ 2 := by
    refine le_trans ?_ h_card_prime_factors;
    have h_image : Finset.image (fun q : P => q.1) (Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C') ⊆ Finset.filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (n' - n)) (Finset.Icc X (2 * X)) := by
      grind;
    exact le_trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ) ( Finset.card_mono h_image );
  have h_card_good : ∀ q ∈ C' \ Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C', (Finset.filter (fun p : P => |(crtRepr (p : ℕ) (q : ℕ) (a p) (a q) : ℝ)| ≤ δ * ((p : ℕ) * (q : ℕ))) C).card ≤ 2 * (2 * (2 * δ * X + B / X) + 1) := by
    intros q hq;
    convert crossLabel_close_fiber_bound X P a n n' B hB hX C hCp hCa hnB hBX q ( hC'p q ( Finset.mem_sdiff.mp hq |>.1 ) |>.1 ) ( hC'p q ( Finset.mem_sdiff.mp hq |>.1 ) |>.2.1 ) ( hC'p q ( Finset.mem_sdiff.mp hq |>.1 ) |>.2.2 ) ( hC'a q ( Finset.mem_sdiff.mp hq |>.1 ) ) ( by aesop ) δ hδ0 hδ4 using 1;
  have h_card_filter : (Finset.filter (fun pq : P × P => |(crtRepr (pq.1 : ℕ) (pq.2 : ℕ) (a pq.1) (a pq.2) : ℝ)| ≤ δ * ((pq.1 : ℕ) * (pq.2 : ℕ))) (C ×ˢ C')).card = ∑ q ∈ C', (Finset.filter (fun p : P => |(crtRepr (p : ℕ) (q : ℕ) (a p) (a q) : ℝ)| ≤ δ * ((p : ℕ) * (q : ℕ))) C).card := by
    simp +decide only [card_filter];
    rw [ Finset.sum_product, Finset.sum_comm ];
  have h_card_filter : ∑ q ∈ C', (Finset.filter (fun p : P => |(crtRepr (p : ℕ) (q : ℕ) (a p) (a q) : ℝ)| ≤ δ * ((p : ℕ) * (q : ℕ))) C).card ≤ ∑ q ∈ Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C', (C.card : ℝ) + ∑ q ∈ C' \ Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C', (2 * (2 * (2 * δ * X + B / X) + 1) : ℝ) := by
    push_cast [ ← Finset.sum_add_distrib ];
    rw [ ← Finset.sum_sdiff ( Finset.filter_subset ( fun q : P => ( q : ℤ ) ∣ n' - n ) C' ) ];
    rw [ add_comm ];
    exact add_le_add ( Finset.sum_le_sum fun x hx => mod_cast Finset.card_filter_le _ _ ) ( Finset.sum_le_sum fun x hx => h_card_good x hx );
  simp_all +decide [ Finset.card_sdiff ];
  exact h_card_filter.trans ( add_le_add ( mul_le_mul_of_nonneg_right ( mod_cast h_card_bad ) ( Nat.cast_nonneg _ ) ) ( mul_le_mul_of_nonneg_right ( mod_cast Nat.sub_le _ _ ) ( by positivity ) ) )

/-
**Lemma E** (`29 §5`).  For distinct integer labels `n ≠ n'` with
    `|n|, |n'| ≤ B ≤ X²/4`, and disjoint prime sets `C, C' ⊆ [X,2X]` on which `a`
    has constant residues `n`, `n'` respectively, with `|C| ≥ 32(B/X+1)` and
    `|C'| ≥ 8`:
    `∑_{p∈C, q∈C'} (H_{pq}/pq)² ≥ c·|C|³|C'|/X²` for an absolute `c > 0`.

    Proof (`29 §5`): reduce to `LocalEnergy.linearCongruence_pair_count` with `w = n'-n`; at most `2`
    primes divide `d = n'-n`; for the rest, `≤ 8δX+4B/X+2` cross pairs are close,
    so `≥ |C||C'|/2` pairs carry energy `≥ δ²`.

    **Verification finding (statement fix).**  The V5 statement omitted the
    hypotheses that the elements of `C` and `C'` are primes in `[X, 2X]`.  Without
    them the lemma is **false**: `crtRepr p q · ·` returns `0` whenever `p, q` are
    not coprime, so taking `C, C'` to consist of (say) even composite numbers
    makes every cross term `0` and the left sum `0`, while the right-hand side
    `c·|C|³|C'|/X²` is strictly positive.  The paper (`29 §5`) explicitly takes
    `C, C'` to be "sets of primes in `[X,2X]`", and Lemma D needs `q` prime with
    `X ≤ q`.  The hypotheses `hCp`, `hC'p` below restore this; they are exactly
    the regime the lemma is used in (Theorem B applies it to prime classes).

    **Status**: proved (`c = 1/8192`), via `crossLabel_close_fiber_bound` + `crossLabel_close_pair_count`,
    the choice `δ = |C|/(64X)`, and the sum-of-squares energy accounting.
-/
theorem crossLabel_energy_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
        (a : BlockAssignment P) (n n' : ℤ) (B : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ B → |(n':ℝ)| ≤ B → B ≤ (X:ℝ)^2/4 →
        ∀ (C C' : Finset P),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ X ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*X) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ X ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*X) →
          Disjoint C C' →
          (32 * (B/X + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, a p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', a q = ((n' : ℤ) : ZMod (q:ℕ))) →
          c * (C.card : ℝ)^3 * C'.card / (X:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2 := by
  refine' ⟨ 1 / 8192, by norm_num, _ ⟩;
  intro X P _ a n n' B hn hnB hn'B hBX C C' hCp hC'p hdisj hC hC' hCa hC'a
  by_cases hX : 1 ≤ X;
  · -- Set `δ := N/(64*X)`. Then `0 ≤ δ`, and `δ ≤ 1/4` since `N ≤ X+1 ≤ 2X`, so `δ ≤ 2X/(64X) = 1/32`. Also `δ > 0`.
    set δ := (C.card : ℝ) / (64 * X)
    have hδ0 : 0 ≤ δ := by
      positivity
    have hδ4 : δ ≤ 1 / 4 := by
      have hN_le_X_plus_1 : (C.card : ℝ) ≤ X + 1 := by
        have hN_le_X_plus_1 : (C.card : ℝ) ≤ Finset.card (Finset.image (fun p : P => p.val) C) := by
          rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ];
        exact hN_le_X_plus_1.trans ( mod_cast le_trans ( Finset.card_le_card <| show Finset.image ( fun p : P => ( p : ℕ ) ) C ⊆ Finset.Icc X ( 2 * X ) from Finset.image_subset_iff.mpr fun p hp => Finset.mem_Icc.mpr <| hCp p hp |>.2 ) <| by norm_num [ two_mul, add_assoc ] );
      rw [ div_le_iff₀ ] <;> nlinarith [ show ( X : ℝ ) ≥ 1 by norm_cast ]
    have hδ_pos : 0 < δ := by
      exact div_pos ( by linarith [ show ( 0 : ℝ ) ≤ B / X by exact div_nonneg ( by linarith [ abs_le.mp hnB ] ) ( by positivity ) ] ) ( by positivity );
    -- Let `Far := (C ×ˢ C').filter (fun pq => ¬ (|(crtRepr (pq.1:ℕ) (pq.2:ℕ) (a pq.1) (a pq.2):ℝ)| ≤ δ*((pq.1:ℕ)*(pq.2:ℕ))))` and `Close := (C ×ˢ C').filter (the un-negated predicate)`.
    set Far := (C ×ˢ C').filter (fun pq => ¬ (|(crtRepr (pq.1 : ℕ) (pq.2 : ℕ) (a pq.1) (a pq.2) : ℝ)| ≤ δ * ((pq.1 : ℕ) * (pq.2 : ℕ))))
    set Close := (C ×ˢ C').filter (fun pq => |(crtRepr (pq.1 : ℕ) (pq.2 : ℕ) (a pq.1) (a pq.2) : ℝ)| ≤ δ * ((pq.1 : ℕ) * (pq.2 : ℕ)));
    -- Energy lower bound: `∑ pq∈C×ˢC', g pq ≥ ∑ pq∈Far, g pq` (drop nonneg terms outside `Far`) `≥ ∑ pq∈Far, δ²` (on `Far`, `δ*(p*q) < |H|` and `p*q>0` give `|H/(p*q)| > δ ≥ 0`, so `g pq = (H/(p*q))² ≥ δ²`) `= (Far.card:ℝ)*δ²`.
    have h_energy_lower_bound : ∑ pq ∈ C ×ˢ C', ((crtRepr (pq.1 : ℕ) (pq.2 : ℕ) (a pq.1) (a pq.2) : ℝ) / ((pq.1 : ℕ) * (pq.2 : ℕ))) ^ 2 ≥ (Far.card : ℝ) * δ ^ 2 := by
      have h_energy_lower_bound : ∀ pq ∈ Far, ((crtRepr (pq.1 : ℕ) (pq.2 : ℕ) (a pq.1) (a pq.2) : ℝ) / ((pq.1 : ℕ) * (pq.2 : ℕ))) ^ 2 ≥ δ ^ 2 := by
        intro pq hpq
        have h_abs : |(crtRepr (pq.1 : ℕ) (pq.2 : ℕ) (a pq.1) (a pq.2) : ℝ)| > δ * ((pq.1 : ℕ) * (pq.2 : ℕ)) := by
          exact not_le.mp fun h => Finset.mem_filter.mp hpq |>.2 h;
        rw [ div_pow, ge_iff_le, le_div_iff₀ ] <;> norm_num at *;
        · convert pow_le_pow_left₀ ( by positivity ) h_abs.le 2 using 1 <;> norm_num [ mul_pow ];
        · exact sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by aesop ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by aesop ) ) ) );
      exact le_trans ( by norm_num ) ( Finset.sum_le_sum h_energy_lower_bound ) |> le_trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _;
    -- Count: by `crossLabel_close_pair_count` (with this `δ`), `(Close.card:ℝ) ≤ 2*N + N'*(2*(2*(2*δ*X + B/X)+1))`.
    have h_close_count : (Close.card : ℝ) ≤ 2 * (C.card : ℝ) + (C'.card : ℝ) * (2 * (2 * (2 * δ * X + B / X) + 1)) := by
      convert crossLabel_close_pair_count X P a n n' B ( show 0 ≤ B by linarith [ abs_le.mp hnB ] ) hX hn C C' hCp hC'p hCa hC'a hnB hn'B hBX δ hδ0 hδ4 using 1;
    -- Therefore, `(Far.card:ℝ) = N*N' - (Close.card:ℝ) ≥ N*N'/2`.
    have h_far_card : (Far.card : ℝ) ≥ (C.card : ℝ) * (C'.card : ℝ) / 2 := by
      have h_far_card : (Far.card : ℝ) = (C.card : ℝ) * (C'.card : ℝ) - (Close.card : ℝ) := by
        rw [ eq_sub_iff_add_eq', ← Nat.cast_add ];
        rw [ Finset.card_filter_add_card_filter_not ] ; norm_num;
      rw [ show δ = ( C.card : ℝ ) / ( 64 * X ) by rfl ] at * ; ring_nf at * ; nlinarith [ inv_mul_cancel₀ ( by positivity : ( X : ℝ ) ≠ 0 ) ] ;
    rw [ Finset.sum_product ] at h_energy_lower_bound;
    refine le_trans ?_ h_energy_lower_bound;
    convert mul_le_mul_of_nonneg_right h_far_card ( sq_nonneg ( δ : ℝ ) ) using 1 ; ring;
  · interval_cases X ; norm_num at *;
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

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
lemma dominant_label_linear_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (R : ℝ) (_hR0 : 0 ≤ R)
    (hRpoly : R ≤ (P.card:ℝ)^4*(1-ρ)^2/(409600*(X:ℝ)^2)) :
    (5/(1-ρ)) * Real.sqrt R / sigmaP P ≤ (P.card:ℝ) * X / 16 := by
  have hXpos : (0:ℝ) < X := by positivity
  have hNpos : (0:ℝ) < (P.card:ℝ) := by positivity
  have hρ1 : (0:ℝ) < 1 - ρ := by linarith
  have hσ : (P.card:ℝ)/(8*(X:ℝ)^2) ≤ sigmaP P := block_deviation_lower_bound X hX P hP hN
  have hσpos : 0 < sigmaP P := lt_of_lt_of_le (by positivity) hσ
  have hsqrtR : Real.sqrt R ≤ (P.card:ℝ)^2*(1-ρ)/(640*X) := by
    rw [show (P.card:ℝ)^2*(1-ρ)/(640*X) = Real.sqrt (((P.card:ℝ)^2*(1-ρ)/(640*X))^2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have key : ((P.card:ℝ)^2*(1-ρ)/(640*X))^2 = (P.card:ℝ)^4*(1-ρ)^2/(409600*(X:ℝ)^2) := by ring
    rw [key]; exact hRpoly
  rw [div_le_iff₀ hσpos]
  have hub : (5/(1-ρ)) * Real.sqrt R ≤ (P.card:ℝ)^2/(128*(X:ℝ)) := by
    calc (5/(1-ρ)) * Real.sqrt R
        ≤ (5/(1-ρ)) * ((P.card:ℝ)^2*(1-ρ)/(640*X)) :=
          mul_le_mul_of_nonneg_left hsqrtR (by positivity)
      _ = (P.card:ℝ)^2/(128*(X:ℝ)) := by (field_simp; ring)
  have hlb : (P.card:ℝ)^2/(128*(X:ℝ)) ≤ (P.card:ℝ)*X/16 * sigmaP P := by
    have h2 : (P.card:ℝ)*X/16 * ((P.card:ℝ)/(8*(X:ℝ)^2)) ≤ (P.card:ℝ)*X/16 * sigmaP P :=
      mul_le_mul_of_nonneg_left hσ (by positivity)
    calc (P.card:ℝ)^2/(128*(X:ℝ))
        = (P.card:ℝ)*X/16 * ((P.card:ℝ)/(8*(X:ℝ)^2)) := by (field_simp; ring)
      _ ≤ (P.card:ℝ)*X/16 * sigmaP P := h2
  linarith [hub, hlb]

/- **Theorem A** (`29 §3`).  For `ε > 0`, `ρ ∈ (0, 1/4]`, and `X` large, the
    number of *dominant* low-energy assignments is at most
    `exp(ε R) · (1 + (10/(1-ρ))·√R/σ_P)`.

    Proof ingredients (all in `29 §3`): (A1) the dominant label is unique; (A2) the
    label range `|m| ≤ (5/(1-ρ))·√R/σ_P`; (A3) each exception carries energy
    `≥ N³/2¹⁵X²` via `LocalEnergy.linearCongruence_pair_count`; (A4) the exception entropy
    `3e log X ≤ εR`.

    **Status**: `sorry` — the entropy bookkeeping (A4) and the per-exception energy
    accounting (A3) over the concrete CRT energy `QP`. -/
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


/-! ## Energy forcing without a dominant label -/

/-! ### Covering construction -/

/-
**Pair count (`29 §4`).**  The number of ordered pairs `p < q` whose centered
    representative exceeds `B` is `≤ 16 R X⁴ / B²`: each such pair contributes
    `(H/(pq))² > (B/(4X²))²` to `QP ≤ R`, using `pq ≤ 4X²`.
-/
lemma large_crt_pair_count
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (a : BlockAssignment P) (R : ℝ) (hQ : QP P a ≤ R)
    (B : ℝ) (hB : 0 < B) :
    (((orderedPrimePairsA P).filter (fun pq =>
        B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ)
      ≤ 16 * R * (X:ℝ)^4 / B^2 := by
  rw [ le_div_iff₀ ( by positivity ) ];
  have h_card_bound : ∀ pq ∈ orderedPrimePairsA P, B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)| → ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)/((pq.1.1:ℝ)*pq.2.1))^2 ≥ B^2/(16*X^4) := by
    intros pq hpq hBpq
    have h_bound : (pq.1.1 : ℝ) * (pq.2.1 : ℝ) ≤ 4 * (X : ℝ) ^ 2 := by
      exact_mod_cast by nlinarith [ hP _ pq.1.2, hP _ pq.2.2 ] ;
    rw [ div_pow, ge_iff_le, div_le_div_iff₀ ] <;> try positivity;
    · exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) h_bound 2 ) ( by positivity ) ) ( by nlinarith [ show ( |↑ ( crtRepr ( pq.1 : ℕ ) ( pq.2 : ℕ ) ( a pq.1 ) ( a pq.2 ) )| : ℝ ) ^ 2 = ( ↑ ( crtRepr ( pq.1 : ℕ ) ( pq.2 : ℕ ) ( a pq.1 ) ( a pq.2 ) ) : ℝ ) ^ 2 by rw [ sq_abs ], abs_mul_abs_self ( ( crtRepr ( pq.1 : ℕ ) ( pq.2 : ℕ ) ( a pq.1 ) ( a pq.2 ) : ℤ ) : ℝ ), pow_le_pow_left₀ ( by positivity ) hBpq.le 2 ] );
    · exact sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ pq.1.2 |>.1 ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ pq.2.2 |>.1 ) ) ) );
  have h_sum_bound : ∑ pq ∈ orderedPrimePairsA P, ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)/((pq.1.1:ℝ)*pq.2.1))^2 ≥ ∑ pq ∈ orderedPrimePairsA P, if B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)| then B^2/(16*X^4) else 0 := by
    exact Finset.sum_le_sum fun x hx => by split_ifs <;> [ exact h_card_bound x hx ‹_›; exact by positivity ] ;
  have h_indicator :
      (∑ pq ∈ orderedPrimePairsA P,
          if B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|
          then B ^ 2 / (16 * X ^ 4) else 0) =
        (((orderedPrimePairsA P).filter (fun pq =>
          B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) *
            (B ^ 2 / (16 * X ^ 4)) := by
    rw [← Finset.sum_filter]
    simp
  have h_count_energy :
      (((orderedPrimePairsA P).filter (fun pq =>
        B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) *
          (B ^ 2 / (16 * X ^ 4)) ≤ R := by
    rw [← h_indicator]
    exact h_sum_bound.trans (by simpa [QP] using hQ)
  have hscale_pos : 0 < (16 : ℝ) * X ^ 4 := by positivity
  calc
    (((orderedPrimePairsA P).filter (fun pq =>
        B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) * B ^ 2 =
      ((((orderedPrimePairsA P).filter (fun pq =>
          B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) *
          (B ^ 2 / (16 * X ^ 4))) * (16 * X ^ 4) := by
        field_simp
    _ ≤ R * (16 * X ^ 4) := mul_le_mul_of_nonneg_right h_count_energy hscale_pos.le
    _ = 16 * R * X ^ 4 := by ring

/-
**Double counting (`29 §4`).**  The sum over base points of the high-`H`
    neighbour counts equals twice the (ordered `p<q`) pair count, since the
    relation `q ≠ p0 ∧ B < |H_{p0 q}|` is symmetric (`crtRepr_symm`).
-/
lemma large_crt_basepoint_sum
    (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p)
    (a : BlockAssignment P) (B : ℝ) :
    (∑ p0 ∈ P.attach, (P.attach.filter (fun q => q ≠ p0 ∧
        B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card)
      = 2 * ((orderedPrimePairsA P).filter (fun pq =>
          B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card := by
  have h_sum_eq : ∑ p0 ∈ P.attach, (Finset.filter (fun q => q ≠ p0 ∧ B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|) P.attach).card = (Finset.filter (fun pq => pq.1 ≠ pq.2 ∧ B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (P.attach ×ˢ P.attach)).card := by
    simp +decide only [card_filter];
    erw [Finset.sum_product] ; simp +decide;
    simp +decide only [eq_comm];
  have h_symm : Finset.filter (fun pq => pq.1 ≠ pq.2 ∧ B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (P.attach ×ˢ P.attach) = Finset.image (fun pq => (pq.2, pq.1)) (Finset.filter (fun pq => B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (orderedPrimePairsA P)) ∪ Finset.filter (fun pq => B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (orderedPrimePairsA P) := by
    ext ⟨p, q⟩; simp [orderedPrimePairsA];
    constructor <;> intro h;
    · cases lt_or_gt_of_ne h.1 <;> [ exact Or.inr ⟨ by assumption, h.2 ⟩ ; exact Or.inl ⟨ q, q.2, p, p.2, ⟨ by assumption, by simpa only [ crtRepr_symm _ _ ( hP _ p.2 ) ( hP _ q.2 ) ( by aesop ) ] using h.2 ⟩, rfl, rfl ⟩ ];
    · grind +suggestions;
  rw [ h_sum_eq, h_symm, Finset.card_union_of_disjoint ];
  · rw [ two_mul, Finset.card_image_of_injective ] ; norm_num [ Function.Injective ];
  · simp +contextual [ Finset.disjoint_left, orderedPrimePairsA ];
    lia

/-
**Base point (`29 §4`).**  Averaging over base points, some `p0 ∈ P` has at
    most `32 R X⁴ / (B² N)` vertices `q` with `|H_{p0 q}| > B`.  Indeed the sum over
    base points of these counts equals twice the pair count (`large_crt_pair_count`,
    via the symmetry `crtRepr_symm`), so the minimum is `≤` the average.
-/
lemma exists_sparse_crt_basepoint
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hPne : 0 < P.card)
    (a : BlockAssignment P) (R : ℝ) (_hR : 0 ≤ R) (hQ : QP P a ≤ R)
    (B : ℝ) (hB : 0 < B) :
    ∃ p0 : P, p0 ∈ P.attach ∧
      ((P.attach.filter (fun q => q ≠ p0 ∧
          B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ)
        ≤ 32 * R * (X:ℝ)^4 / (B^2 * P.card) := by
  have h_avg : (∑ p0 ∈ P.attach, (P.attach.filter (fun q => q ≠ p0 ∧ B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) ≤ 2 * (16 * R * (X:ℝ)^4 / B^2) := by
    have h_avg : (∑ p0 ∈ P.attach, (P.attach.filter (fun q => q ≠ p0 ∧ B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) = 2 * ((orderedPrimePairsA P).filter (fun pq => B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card := by
      convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( large_crt_basepoint_sum P ( fun p hp => ( hP p hp ).1 ) a B ) using 1; all_goals norm_cast;
    exact h_avg.symm ▸ mul_le_mul_of_nonneg_left ( mod_cast large_crt_pair_count X hX P hP a R hQ B hB ) zero_le_two;
  contrapose! h_avg;
  convert Finset.sum_lt_sum_of_nonempty ( Finset.card_pos.mp <| by simpa [ Finset.card_attach ] using hPne ) h_avg using 1 ; norm_num ; ring_nf;
  norm_num [ hPne.ne' ]

/-
**Power-mean energy lower bound (combinatorial heart of `29 §6`).**  For a
    family of nonnegative class sizes `x` over labels `L`, with a maximal label
    `nstar`, the off-diagonal cubic form `∑_{n≠n'} x_n³ x_{n'}` is at least
    `M₂⁴ / |L|²`, where `M₂ = ∑_{n≠nstar} x_n`.  (Uses `S₄ ≤ x_{nstar}·S₃` and the
    power-mean inequality `∑ x_n³ ≥ (∑ x_n)³ / |L|²`.)
-/
lemma sum_cube_offdiag_ge {ι : Type*} [DecidableEq ι]
    (L : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ L, 0 ≤ x i)
    (nstar : ι) (hns : nstar ∈ L) (hmax : ∀ i ∈ L, x i ≤ x nstar) :
    (∑ n ∈ L \ {nstar}, x n)^4 / (L.card:ℝ)^2
      ≤ ∑ n ∈ L, ∑ n' ∈ L \ {n}, (x n)^3 * (x n') := by
  -- By the properties of sums and the power mean inequality, we can simplify the expression.
  have h_simplify : (∑ n ∈ L, ∑ n' ∈ L \ {n}, (x n)^3 * (x n')) ≥ (∑ n ∈ L, (x n)^3) * (∑ n ∈ L \ {nstar}, (x n)) := by
    have h_simplify : (∑ n ∈ L, ∑ n' ∈ L \ {n}, (x n)^3 * (x n')) = (∑ n ∈ L, (x n)^3 * (∑ n' ∈ L \ {n}, (x n'))) := by
      simp +decide only [Finset.mul_sum _ _ _];
    rw [ h_simplify, Finset.sum_mul _ _ _ ];
    refine' Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left _ ( pow_nonneg ( hx i hi ) 3 );
    by_cases hi' : i = nstar <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    linarith [ hmax i hi ];
  -- Apply the power mean inequality to the sum of cubes.
  have h_power_mean : (∑ n ∈ L \ {nstar}, x n) ^ 3 / (L.card - 1 : ℝ) ^ 2 ≤ ∑ n ∈ L \ {nstar}, x n ^ 3 := by
    have h_power_mean : ∀ (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i), s.Nonempty → (∑ i ∈ s, f i) ^ 3 / s.card ^ 2 ≤ ∑ i ∈ s, f i ^ 3 := by
      intro s f hf hs_nonempty
      have h_power_mean : (∑ i ∈ s, f i ^ 3) / s.card ≥ ((∑ i ∈ s, f i) / s.card) ^ 3 := by
        have := @Real.rpow_arith_mean_le_arith_mean_rpow;
        specialize this s ( fun _i => 1 / s.card ) ( fun _i => f _i ) ; simp_all +decide [ div_eq_inv_mul, Finset.mul_sum _ _ _ ];
        exact_mod_cast this ( mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr hs_nonempty.card_pos.ne' ) ) ( show 1 ≤ ( 3 : ℝ ) by norm_num );
      contrapose! h_power_mean;
      convert div_lt_div_iff_of_pos_right ( Nat.cast_pos.mpr hs_nonempty.card_pos ) |>.2 h_power_mean using 1 ; ring;
    by_cases hL : L = {nstar} <;> simp_all +decide;
    convert h_power_mean ( L \ { nstar } ) x ( fun i hi => hx i ( Finset.mem_sdiff.mp hi |>.1 ) ) ( Finset.nonempty_of_ne_empty ( by aesop ) ) using 1 <;> simp +decide [*, Finset.card_sdiff];
    rw [ Nat.cast_pred ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) ];
  by_cases hL : L.card = 1 <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
  · rw [ Finset.card_eq_one ] at hL ; aesop;
  · refine' le_trans _ ( h_simplify.trans _ );
    · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ∑ n ∈ L, x n ^ 3 ≥ ( ∑ n ∈ L, x n - x nstar ) ^ 3 / ( L.card - 1 : ℝ ) ^ 2 from _ ) ( sub_nonneg.mpr <| Finset.single_le_sum ( fun i _ => hx i ‹_› ) hns ) );
      · rw [ div_mul_eq_mul_div, div_le_div_iff₀ ];
        · exact mul_le_mul_of_nonneg_left ( by nlinarith only [ show ( L.card : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) ( Ne.symm hL ) ] ) ( mul_nonneg ( pow_nonneg ( sub_nonneg.mpr <| Finset.single_le_sum ( fun i _ => hx i ‹_› ) hns ) _ ) <| sub_nonneg.mpr <| Finset.single_le_sum ( fun i _ => hx i ‹_› ) hns );
        · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) );
        · exact sq_pos_of_pos ( sub_pos_of_lt ( mod_cast lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) ( Ne.symm hL ) ) );
      · exact h_power_mean.trans ( sub_le_self _ ( pow_nonneg ( hx _ hns ) _ ) );
    · rfl

/-
**Short list cardinality (`29 §4`).**  The covered labels `n = H_{p0 q}` lie in
    `[-B, B]` and all share the residue `a_{p0}` modulo `p0 ≥ X`, so there are at
    most `2B/X + 2` of them.
-/
lemma crt_label_shortlist_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (a : BlockAssignment P) (p0 : P) (B : ℝ) (hB : 0 ≤ B) :
    (((P.attach.filter (fun q => q ≠ p0 ∧
        |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B)).image
          (fun q => crtRepr p0.1 q.1 (a p0) (a q))).card : ℝ) ≤ 2*B/X + 2 := by
  have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (2 * B / (p0.1 : ℝ) + 2 : ℝ) := by
    have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (2 * B / (p0.1 : ℝ) + 2 : ℝ) := by
      have h_phi : ∀ q : P, q ≠ p0 → |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B → ∃ k : ℤ, |(k : ℝ)| ≤ B / (p0.1 : ℝ) + 1 / 2 ∧ (crtRepr p0.1 q.1 (a p0) (a q) : ℤ) = (k * (p0.1 : ℤ) + (a p0).valMinAbs) := by
        intro q hq hqB
        obtain ⟨k, hk⟩ : ∃ k : ℤ, (crtRepr p0.1 q.1 (a p0) (a q) : ℤ) = k * (p0.1 : ℤ) + (a p0).valMinAbs := by
          have h_crtRepr_congr_left : (crtRepr p0.1 q.1 (a p0) (a q) : ZMod p0.1) = (a p0).valMinAbs := by
            convert crtRepr_congr_left p0.1 q.1 ( a p0 ) ( a q ) _ using 1;
            · convert ZMod.coe_valMinAbs ( a p0 ) using 1;
            · exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := Nat.coprime_primes ( hP p0 p0.2 |>.1 ) ( hP q q.2 |>.1 ) ; aesop );
          exact ⟨ ( crtRepr p0.1 q.1 ( a p0 ) ( a q ) - ( a p0 ).valMinAbs ) / p0.1, by rw [ Int.ediv_mul_cancel ( by rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop ) ] ; ring ⟩;
        refine' ⟨ k, _, hk ⟩;
        rw [ div_add_div, le_div_iff₀ ] <;> norm_num;
        · have h_abs_k : |(k : ℝ) * (p0.1 : ℝ) + (a p0).valMinAbs| ≤ B := by
            convert hqB using 1 ; norm_cast ; aesop;
          have h_abs_k : |(a p0).valMinAbs| ≤ (p0.1 : ℝ) / 2 := by
            have := ZMod.natAbs_valMinAbs_le ( a p0 );
            rw [ le_div_iff₀ ] <;> norm_cast;
            linarith! [ Nat.div_mul_le_self p0 2 ];
          norm_num [ abs_le ] at *;
          cases abs_cases ( k : ℝ ) <;> nlinarith [ show ( p0 : ℝ ) ≥ 1 by exact_mod_cast Nat.Prime.pos ( hP p0 p0.2 |>.1 ) ];
        · exact Nat.Prime.pos ( hP _ p0.2 |>.1 );
        · exact Nat.Prime.ne_zero ( hP _ p0.2 |>.1 )
      have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (2 * ⌊B / (p0.1 : ℝ) + 1 / 2⌋ + 1 : ℝ) := by
        have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (Finset.image (fun k : ℤ => k * (p0.1 : ℤ) + (a p0).valMinAbs) (Finset.Icc (-⌊B / (p0.1 : ℝ) + 1 / 2⌋) ⌊B / (p0.1 : ℝ) + 1 / 2⌋)).card := by
          refine' Nat.cast_le.mpr ( Finset.card_le_card _ );
          simp_all +decide [ Finset.subset_iff ];
          rintro x q hq hq' hq'' rfl; obtain ⟨ k, hk₁, hk₂ ⟩ := h_phi q hq hq' hq''; exact ⟨ k, ⟨ neg_le_of_abs_le <| Int.le_floor.mpr <| by simpa using hk₁, le_of_abs_le <| Int.le_floor.mpr <| by simpa using hk₁ ⟩, hk₂.symm ⟩ ;
        refine le_trans h_card_image ?_;
        rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, NeZero.ne ];
        norm_cast ; linarith [ Int.toNat_of_nonneg ( by linarith [ Int.floor_nonneg.mpr ( show 0 ≤ B / ( p0 : ℝ ) + 1 / 2 by positivity ) ] : 0 ≤ ⌊B / ( p0 : ℝ ) + 1 / 2⌋ + 1 + ⌊B / ( p0 : ℝ ) + 1 / 2⌋ ) ];
      refine le_trans h_card_image ?_;
      ring_nf;
      linarith [ Int.floor_le ( 1 / 2 + B * ( p0 : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( 1 / 2 + B * ( p0 : ℝ ) ⁻¹ ) ];
    convert h_card_image using 1;
  refine le_trans h_card_image ?_;
  gcongr ; aesop

/-
**Label residue (`29 §4`).**  Every covered vertex `q ≠ p0` carries the residue
    of its label: `a q = (lab q : ZMod q)` (by `crtRepr_congr_right`).
-/
lemma crtRepr_eq_label_residue (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p) (a : BlockAssignment P) (p0 q : P) (hq : q ≠ p0) :
    a q = ((crtRepr p0.1 q.1 (a p0) (a q) : ℤ) : ZMod q.1) := by
  have h_coprime : Nat.Coprime p0.1 q.1 := by
    exact (Nat.coprime_primes ( hP _ p0.2 ) ( hP _ q.2 )).mpr ( by contrapose! hq; aesop );
  -- Apply `crtRepr_congr_right` to the coprime pair.
  have := crtRepr_congr_right p0.1 q.1 (a p0) (a q) h_coprime;
  aesop

/-
**Cross-energy double count (`29 §6`).**  Summing the cross energies of
    ordered pairs of distinct label classes (a partition of `S` by `f`) is at most
    `2·Q_P`, since each unordered vertex pair is counted at most twice and the
    energy is symmetric (`crtRepr_symm`).
-/
set_option maxHeartbeats 1000000 in
lemma crossLabel_energy_sum_le
    (P : Finset ℕ) [∀ p : P, NeZero p.1] (hP : ∀ p ∈ P, Nat.Prime p)
    (a : BlockAssignment P) (S : Finset P) (hS : S ⊆ P.attach)
    (f : P → ℤ) (L : Finset ℤ) :
    ∑ n ∈ L, ∑ n' ∈ L \ {n},
        (∑ p ∈ S.filter (fun q => f q = n), ∑ q ∈ S.filter (fun q => f q = n'),
          ((crtRepr p.1 q.1 (a p) (a q) : ℝ) / ((p.1:ℝ) * q.1))^2)
      ≤ 2 * QP P a := by
  have h_symm : (∑ n ∈ L, ∑ n' ∈ L \ {n}, ∑ p ∈ S.filter (fun q => f q = n), ∑ q ∈ S.filter (fun q => f q = n'), ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2) ≤
               (∑ p ∈ S, ∑ q ∈ S, if f p ≠ f q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) := by
                 have h_symm : (∑ n ∈ L, ∑ n' ∈ L \ {n}, ∑ p ∈ S.filter (fun q => f q = n), ∑ q ∈ S.filter (fun q => f q = n'), ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2) =
                                (∑ p ∈ S.filter (fun q => f q ∈ L), ∑ q ∈ S.filter (fun q => f q ∈ L ∧ f q ≠ f p), ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2) := by
                                  simp +decide only [sum_sigma'];
                                  refine' Finset.sum_bij ( fun x hx => ⟨ x.snd.snd.fst, x.snd.snd.snd ⟩ ) _ _ _ _ <;> simp +decide; all_goals grind;
                 simp_all +decide [ Finset.sum_ite ];
                 refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _;
                 exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum_of_subset_of_nonneg ( fun j hj => by aesop ) fun _ _ _ => sq_nonneg _;
  -- Apply the fact that the sum of the cross energies is less than or equal to twice the sum of the energies.
  have h_cross_le_2QP : (∑ p ∈ S, ∑ q ∈ S, if p ≠ q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) ≤ 2 * QP P a := by
    have h_cross_le_2QP : (∑ p ∈ P.attach, ∑ q ∈ P.attach, if p ≠ q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) = 2 * QP P a := by
      have h_cross_le_2QP : (∑ p ∈ P.attach, ∑ q ∈ P.attach, if p < q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) = QP P a := by
        unfold QP; simp +decide [ Finset.sum_ite ] ;
        simp +decide [ Finset.sum_filter, Finset.sum_product, orderedPrimePairsA ];
      have h_cross_le_2QP : (∑ p ∈ P.attach, ∑ q ∈ P.attach, if p > q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) = QP P a := by
        rw [ ← h_cross_le_2QP, Finset.sum_comm ];
        refine' Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => _;
        split_ifs <;> simp_all +decide [ mul_comm ];
        rw [ crtRepr_symm ];
        · exact hP _ q.2;
        · exact hP _ p.2;
        · exact ne_of_gt ‹_›;
      convert congr_arg₂ ( · + · ) ‹ ( ∑ p ∈ P.attach, ∑ q ∈ P.attach, if p < q then ( crtRepr p q ( a p ) ( a q ) / ( p * q : ℝ ) ) ^ 2 else 0 ) = QP P a › ‹ ( ∑ p ∈ P.attach, ∑ q ∈ P.attach, if p > q then ( crtRepr p q ( a p ) ( a q ) / ( p * q : ℝ ) ) ^ 2 else 0 ) = QP P a › using 1;
      · simp +decide only [← sum_add_distrib];
        refine' Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => _;
        grind +revert;
      · ring;
    rw [ ← h_cross_le_2QP ];
    refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity );
    exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum_of_subset_of_nonneg ( hS hi |> fun h => Finset.subset_univ _ ) fun _ _ _ => by positivity;
  refine le_trans h_symm <| h_cross_le_2QP.trans' <| Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_;
  split_ifs <;> norm_num ; aesop;
  positivity

/-
**Energy core (`29 §6`).**  For a covered set `S` (all `q ≠ p0` with
    `|H_{p0 q}| ≤ B`) and a set `L` of substantial labels (each class
    `Cls n = S.filter (lab = n)` has `≥ 32(B/X+1)` and `≥ 8` members), Lemma E
    applied to every ordered pair of distinct classes and summed (bounded by `2Q_P`
    via `crossLabel_energy_sum_le`) gives a lower bound on `R` by the off-diagonal
    cubic form of the class sizes.
-/
set_option maxHeartbeats 1000000 in
lemma class_partition_energy_lower_bound
    (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (a : BlockAssignment P) (p0 : P) (B : ℝ) (_hB0 : 0 ≤ B) (hBX : B ≤ (X:ℝ)^2/4)
    (S : Finset P) (hScov : ∀ q ∈ S, q ≠ p0 ∧
        |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B)
    (L : Finset ℤ)
    (hLsub : ∀ n ∈ L, (32*(B/X+1):ℝ) ≤
        ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)).card : ℝ))
    (hL8 : ∀ n ∈ L, (8:ℝ) ≤
        ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)).card : ℝ))
    (R : ℝ) (hQ : QP P a ≤ R)
    (cE : ℝ) (_hcE0 : 0 < cE)
    (hcE : ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1]
        (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 →
        ∀ (C C' : Finset Q),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) →
          Disjoint C C' →
          (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) →
          cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2) :
    cE/(X:ℝ)^2 *
        (∑ n ∈ L, ∑ n' ∈ L \ {n},
          ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)).card : ℝ)^3 *
            ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n')).card : ℝ))
      ≤ 2 * R := by
  rw [ Finset.mul_sum _ _ _ ];
  have h_cross_sum : ∀ n n' : ℤ, n ∈ L → n' ∈ L → n ≠ n' → cE / (X:ℝ)^2 * (Finset.card (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)) : ℝ)^3 * (Finset.card (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n')) : ℝ) ≤ ∑ q ∈ S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n), ∑ q' ∈ S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n'), ((crtRepr q.1 q'.1 (a q) (a q') : ℝ) / ((q.1:ℝ) * q'.1))^2 := by
    intros n n' hn hn' hne;
    specialize hcE X P a n n' B hne ?_ ?_ ?_ (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)) (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n'));
    · obtain ⟨q, hq⟩ : ∃ q ∈ S, crtRepr p0.1 q.1 (a p0) (a q) = n := by
        contrapose! hL8;
        exact ⟨ n, hn, by rw [ Finset.filter_eq_empty_iff.mpr hL8 ] ; norm_num ⟩;
      simpa [ ← hq.2 ] using hScov q hq.1 |>.2;
    · obtain ⟨ q, hq ⟩ := Finset.card_pos.mp ( by exact_mod_cast ( by linarith [ hL8 n' hn' ] : ( 0 : ℝ ) < Finset.card ( Finset.filter ( fun q : P => crtRepr p0.1 q.1 ( a p0 ) ( a q ) = n' ) S ) ) );
      grind +qlia;
    · exact hBX;
    · convert hcE _ _ _ ( hLsub n hn ) ( hL8 n' hn' ) _ _ using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      · exact fun p hp hp' hp'' => ⟨ hP p hp |>.1, hP p hp |>.2.1, by linarith [ hP p hp |>.2.2 ] ⟩;
      · exact fun p hp hp' hp'' => ⟨ hP p hp |>.1, hP p hp |>.2.1, by linarith [ hP p hp |>.2.2 ] ⟩;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by aesop;
      · intro p hp hpS hpn
        have h_eq : a ⟨p, hp⟩ = ((crtRepr p0.1 p (a p0) (a ⟨p, hp⟩) : ℤ) : ZMod p) := by
          convert crtRepr_eq_label_residue P ( fun p hp => ( hP p hp ).1 ) a p0 ⟨ p, hp ⟩ ( hScov _ hpS |>.1 ) using 1
        rw [h_eq]
        simp [hpn];
      · intro p hp hpS hp'; specialize hScov ⟨ p, hp ⟩ hpS; simp_all +decide [ Finset.disjoint_left ] ;
        convert crtRepr_eq_label_residue P ( fun p hp => hP p hp |>.1 ) a p0 ⟨ p, hp ⟩ hScov.1 using 1;
        · exact hp'.symm ▸ rfl;
        · exact fun p => ⟨ Nat.Prime.ne_zero ( hP p p.2 |>.1 ) ⟩;
  refine' le_trans _ ( le_trans ( crossLabel_energy_sum_le P ( fun p hp => ( hP p hp ).1 ) a S ( Finset.subset_univ _ ) ( fun q => crtRepr p0.1 q.1 ( a p0 ) ( a q ) ) L ) _ );
  · exact Finset.sum_le_sum fun i hi => by simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun j hj => h_cross_sum i j hi ( Finset.mem_sdiff.mp hj |>.1 ) ( by rintro rfl; exact Finset.mem_sdiff.mp hj |>.2 <| Finset.mem_singleton_self _ ) ;
  · exact mul_le_mul_of_nonneg_left hQ zero_le_two

/-
**Zero energy is dominant.**  If `Q_P(a) = 0` then every cross representative
    vanishes, so `a_p ≡ 0` for all `p`, and `a` is `0`-dominant.
-/
lemma zero_label_dominant_of_large_class (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (a : BlockAssignment P) (ρ : ℝ) (hρ : 0 ≤ ρ) (hQ0 : QP P a = 0) :
    HasDominantLabel X P a ρ := by
  -- Since $a_p = 0$ for all $p \in P$, we can choose $m = 0$.
  use 0; simp;
  have h_all_zero : ∀ p ∈ P.attach, a p = 0 := by
    intro p hp
    have h_cross : ∀ q ∈ P.attach, q ≠ p → crtRepr (p.1) (q.1) (a p) (a q) = 0 := by
      intro q hq hqp
      have h_cross : ((crtRepr (p.1) (q.1) (a p) (a q) : ℝ) / ((p.1 : ℝ) * (q.1 : ℝ)))^2 = 0 := by
        have h_cross : ∀ pq ∈ orderedPrimePairsA P, ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)))^2 = 0 := by
          exact fun pq hpq => by rw [ QP ] at hQ0; exact Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 hQ0 pq hpq;
        cases lt_or_gt_of_ne hqp <;> simp_all +decide [ orderedPrimePairsA ];
        grind +suggestions;
      simp_all +decide [ div_eq_iff, NeZero.ne ];
    obtain ⟨q, hq⟩ : ∃ q ∈ P.attach, q ≠ p := by
      exact Finset.exists_mem_ne (by simpa [Finset.card_attach] using (show 1 < P.card by omega)) p;
    have := crtRepr_congr_left p.1 q.1 ( a p ) ( a q ) ( Nat.coprime_primes ( hP p p.2 |>.1 ) ( hP q q.2 |>.1 ) |>.2 <| by aesop ) ; aesop;
  exact ⟨ by positivity, by rw [ Finset.filter_true_of_mem h_all_zero ] ; norm_num; nlinarith ⟩

/-
**Covering dichotomy (`29 §6`).**  With base point `p0`, threshold `B`, and the
    exception count controlled (`hexc`), either the energy is large (disjunct 1,
    from the substantial-class energy) or the tiny-class bound forces `B/X` large
    (disjunct 2).  This is the structural heart of Theorem B; the final parameter
    chase plugs in `B = √(A²R)·X²/N`.
-/
set_option maxHeartbeats 2000000 in
lemma label_covering_energy_dichotomy
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (hnd : ¬ HasDominantLabel X P a ρ)
    (R : ℝ) (hR0 : 0 < R) (hQ : QP P a ≤ R)
    (p0 : P) (B : ℝ) (hB0 : 0 < B) (hBX : B ≤ (X:ℝ)^2/4)
    (hexc : ((P.attach.filter (fun q => q ≠ p0 ∧
        B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) ≤ ρ * (P.card:ℝ)/8)
    (h1 : 1 ≤ ρ * (P.card:ℝ)/8)
    (cE : ℝ) (hcE0 : 0 < cE)
    (hcE : ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1]
        (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 →
        ∀ (C C' : Finset Q),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) →
          Disjoint C C' →
          (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) →
          cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2) :
    cE * (ρ*(P.card:ℝ)/2)^4 / (2 * (X:ℝ)^2 * (2*B/X+2)^2) ≤ R ∨
      ρ*(P.card:ℝ)/4 < (2*B/X+2)*(32*(B/X+1)+8) := by
  -- Define the relevant quantities for the proof.
  set N := (P.card : ℝ)
  set lab := fun q : P => crtRepr p0.1 q.1 (a p0) (a q)
  set S := P.attach.filter (fun q => q ≠ p0 ∧ |(lab q : ℝ)| ≤ B)
  set allLabels := S.image lab
  set s0 := 32 * (B / X + 1) + 8
  set Cls := fun n => S.filter (fun q => lab q = n)
  set Lsub := allLabels.filter (fun n => s0 ≤ ((Cls n).card : ℝ))
  set exc' := P.attach.filter (fun q => q ≠ p0 ∧ B < |(lab q : ℝ)|)
  set k0 := allLabels.card;
  -- Preliminary bounds.
  have hk0 : (k0 : ℝ) ≤ 2 * B / X + 2 := by
    convert crt_label_shortlist_bound X hX P hP a p0 B hB0.le using 1
  have hS_card : (S.card : ℝ) ≥ N - 1 - ρ * N / 8 := by
    have hS_card : (S.card : ℝ) + (exc'.card : ℝ) = (P.card - 1 : ℝ) := by
      rw [ ← Nat.cast_add, ← Finset.card_union_of_disjoint ];
      · rw [ show S ∪ exc' = Finset.filter ( fun q => q ≠ p0 ) P.attach from ?_ ];
        · simp +decide [ Finset.filter_ne' ];
          rw [ Nat.cast_pred ( by linarith ) ];
        · grind +splitIndPred;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith
  have htiny_le : (∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ)) ≤ ρ * N / 4 → (∑ n ∈ Lsub, ((Cls n).card : ℝ)) ≥ (N - 1 - ρ * N / 8 - ρ * N / 4) := by
    have hsum_card : ∑ n ∈ allLabels, ((Cls n).card : ℝ) = S.card := by
      rw [ ← Nat.cast_sum, Finset.card_eq_sum_ones ];
      rw [ Finset.sum_image' ];
      simp +zetaDelta at *;
    intro htiny_le
    have hsum_card_split : ∑ n ∈ allLabels, ((Cls n).card : ℝ) = ∑ n ∈ Lsub, ((Cls n).card : ℝ) + ∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ) := by
      rw [ add_comm, Finset.sum_sdiff <| Finset.filter_subset _ _ ];
    linarith;
  by_cases htiny : (∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ)) ≤ ρ * N / 4;
  · obtain ⟨nstar, hnstar⟩ : ∃ nstar ∈ Lsub, ∀ n ∈ Lsub, (Cls n).card ≤ (Cls nstar).card := by
      apply_rules [ Finset.exists_max_image ];
      contrapose! htiny_le;
      simp [htiny_le] at *;
      exact ⟨ htiny, by nlinarith [ show ( P.card : ℝ ) ≥ 2 by norm_cast ] ⟩;
    have hCls_nstar_card : (Cls nstar).card ≤ (1 - ρ) * N := by
      have hCls_nstar_card : |nstar| ≤ (X : ℤ) ^ 2 / 2 := by
        obtain ⟨q, hq⟩ : ∃ q ∈ S, lab q = nstar := by
          exact Finset.mem_image.mp ( Finset.mem_filter.mp hnstar.1 |>.1 );
        rw [ ← hq.2, Int.le_ediv_iff_mul_le ] <;> norm_num;
        exact_mod_cast ( by linarith [ Finset.mem_filter.mp hq.1 ] : ( |lab q| : ℝ ) * 2 ≤ X ^ 2 );
      have hCls_nstar_card : (Cls nstar).card ≤ (P.attach.filter (fun q => a q = ((nstar : ℤ) : ZMod q.1))).card := by
        refine Finset.card_le_card ?_;
        simp +zetaDelta at *;
        simp +contextual [ Finset.subset_iff ];
        intro q hq hq' hq'' hq''';
        convert crtRepr_eq_label_residue P ( fun p hp => ( hP p hp ).1 ) a p0 ⟨ q, hq ⟩ hq' using 1;
        · exact hq'''.symm ▸ rfl;
        · exact fun p => ⟨ Nat.Prime.ne_zero ( hP p p.2 |>.1 ) ⟩;
      contrapose! hnd;
      use nstar;
      exact ⟨ by assumption, le_trans hnd.le <| mod_cast hCls_nstar_card ⟩;
    have hM₂ : (∑ n ∈ Lsub \ {nstar}, ((Cls n).card : ℝ)) ≥ ρ * N / 2 := by
      have hM₂ : (∑ n ∈ Lsub \ {nstar}, ((Cls n).card : ℝ)) = (∑ n ∈ Lsub, ((Cls n).card : ℝ)) - ((Cls nstar).card : ℝ) := by
        rw [Finset.sum_eq_sum_sdiff_singleton_add
          (show nstar ∈ Lsub from hnstar.1), add_tsub_cancel_right];
      linarith [ htiny_le htiny ];
    have h_energy : cE / X^2 * (∑ n ∈ Lsub, ∑ n' ∈ Lsub \ {n}, ((Cls n).card : ℝ)^3 * ((Cls n').card : ℝ)) ≤ 2 * R := by
      apply class_partition_energy_lower_bound X P hP a p0 B hB0.le hBX S (fun q hq => by
        exact Finset.mem_filter.mp hq |>.2) Lsub (fun n hn => by
        grind +qlia) (fun n hn => by
        exact le_trans ( by linarith [ show ( 0 : ℝ ) ≤ B / X by positivity ] ) ( Finset.mem_filter.mp hn |>.2 )) R hQ cE hcE0 hcE;
    have h_power_mean : (∑ n ∈ Lsub \ {nstar}, ((Cls n).card : ℝ))^4 / (Lsub.card : ℝ)^2 ≤ ∑ n ∈ Lsub, ∑ n' ∈ Lsub \ {n}, ((Cls n).card : ℝ)^3 * ((Cls n').card : ℝ) := by
      convert sum_cube_offdiag_ge Lsub ( fun n => ( Cls n |> Finset.card : ℝ ) ) _ nstar _ _ using 1 <;> norm_num [ hnstar ];
      exact hnstar.2;
    have h_final : cE / X^2 * (ρ * N / 2)^4 / (2 * B / X + 2)^2 ≤ 2 * R := by
      have h_final : cE / X^2 * (ρ * N / 2)^4 / (Lsub.card : ℝ)^2 ≤ 2 * R := by
        refine le_trans ?_ h_energy;
        rw [ mul_div_assoc ];
        gcongr;
        exact le_trans ( by gcongr ) h_power_mean;
      refine le_trans ?_ h_final;
      gcongr;
      · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ nstar, hnstar.1 ⟩ ) );
      · exact le_trans ( Nat.cast_le.mpr <| Finset.card_le_card <| Finset.filter_subset _ _ ) hk0;
    field_simp at h_final ⊢;
    exact Or.inl h_final;
  · have hTiny_le : (∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ)) ≤ k0 * s0 := by
      refine' le_trans ( Finset.sum_le_sum fun x hx => show ( # ( Cls x ) : ℝ ) ≤ s0 from _ ) _ <;> norm_num [ hk0 ];
      · grind;
      · exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_le_card <| Finset.sdiff_subset ) <| by positivity;
    generalize_proofs at *; (
    exact Or.inr ( lt_of_lt_of_le ( lt_of_not_ge htiny ) ( hTiny_le.trans ( mul_le_mul_of_nonneg_right hk0 ( by positivity ) ) ) ))

/-
**Log-growth threshold.**  Since `X/ log X → ∞`, for any `K` there is `X0` with
    `K ≤ X/ log X` for all `X ≥ X0`.
-/
lemma exists_logarithmic_threshold (K : ℝ) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℕ, X0 ≤ X → K ≤ (X:ℝ)/Real.log X := by
  -- By the properties of the logarithm and the fact that $X / \log X$ tends to infinity, we can find such an $X_0$.
  have h_log_growth : Filter.Tendsto (fun X : ℕ => (X : ℝ) / Real.log (X : ℝ)) Filter.atTop Filter.atTop := by
    have h_log_growth : Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
      -- We can use the change of variables $u = \log x$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
      simpa using Real.tendsto_exp_div_pow_atTop 1;
    exact h_log_growth.comp tendsto_natCast_atTop_atTop;
  exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop K ) |> fun ⟨ X0, hX0 ⟩ ↦ ⟨ ⌈X0⌉₊ + 1, by positivity, fun X hX ↦ hX0 X <| by linarith [ Nat.le_ceil X0, show ( X : ℕ ) ≥ ⌈X0⌉₊ + 1 by exact_mod_cast hX ] ⟩

/-
**Left-disjunct chase.**  Pure algebra: the large-energy disjunct of the
covering dichotomy forces `R ≳ X/log³X`.
-/
/-- A cutoff with scale coefficient `kappa` and comparison loss `lambda`
transfers an energy lower bound into a quadratic lower bound with the single
combined loss `kappa * lambda`.  This is the parameter mechanism behind the
left branch of the covering dichotomy; numerical choices belong only in its
specialization. -/
lemma cutoff_energy_quadratic_lower_bound
    (energy kappa lambda rho R x N : ℝ)
    (hkappa : 0 < kappa) (hlambda : 0 < lambda) (hrho : 0 < rho)
    (hx : 0 < x) (hN : 0 < N)
    (h : energy * rho ^ 4 * N ^ 4 / (lambda * x ^ 2) ≤
      (kappa / rho) * R ^ 2 * x ^ 2 / N ^ 2) :
    energy * rho ^ 5 * N ^ 6 / (kappa * lambda * x ^ 4) ≤ R ^ 2 := by
  field_simp at h ⊢
  nlinarith

lemma low_cutoff_energy_bound (cE ρ : ℝ) (hcE0 : 0 < cE) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (X : ℕ) (N R u : ℝ)
    (hlogX : 0 < Real.log X) (hN : (X:ℝ)/(2*Real.log X) ≤ N) (hNpos : 0 < N)
    (hR0 : 0 < R) (hu0 : 0 ≤ u)
    (husq : u^2 = (256/ρ)*R*(X:ℝ)^2/N^2)
    (hRle : R ≤ cE*ρ^4*(X:ℝ)^2/(8192*(Real.log X)^4))
    (hdisj : cE*(ρ*N/2)^4/(2*(X:ℝ)^2*(2*u+2)^2) ≤ R) :
    ρ^2 * Real.sqrt (cE*ρ) / (10^6) * (X:ℝ)/(Real.log X)^3 ≤ R := by
  -- From hN: N^4 ≥ (X/(2 log X))^4 = X^4/(16*(log X)^4), so T ≥ cE*ρ^4*X^2/(4096*(log X)^4) = 2*(cE*ρ^4*X^2/(8192*(log X)^4)) ≥ 2*R (by hRle). So R ≤ T/2.
  set T := cE * ρ^4 * N^4 / (256 * X^2)
  have hT : T ≥ 2 * R := by
    have hT' : N^4 ≥ X^4 / (16 * (Real.log X)^4) := by
      exact le_trans ( by rw [ div_pow ] ; ring_nf; norm_num ) ( pow_le_pow_left₀ ( by positivity ) hN 4 );
    by_cases hX : X = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    rw [ le_div_iff₀ ] <;> first | positivity | nlinarith [ show 0 < cE * ρ ^ 4 by positivity ] ;
  -- So (256/ρ)*R^2*X^2/N^2 ≥ T/2 = cE*ρ^4*N^4/(512*X^2).
  have hR2 : (256 / ρ) * R^2 * X^2 / N^2 ≥ cE * ρ^4 * N^4 / (512 * X^2) := by
    have hR2 : cE * ρ^5 * N^6 / 16 ≤ 16 * 256 * R^2 * X^4 + 16 * ρ * R * X^2 * N^2 := by
      have hR2 : cE * ρ^5 * N^6 / 16 ≤ 2 * X^2 * (2 * u + 2)^2 * R * ρ * N^2 := by
        rw [ div_le_iff₀ ] at hdisj;
        · nlinarith [ show 0 < ρ * N ^ 2 by positivity ];
        · exact mul_pos ( mul_pos two_pos ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) ) ) ( sq_pos_of_pos ( by positivity ) );
      have hR2 : (2 * u + 2)^2 ≤ 4 * (u^2 + 1) * 2 := by
        nlinarith only [ sq_nonneg ( u - 1 ), hu0 ];
      rw [ husq ] at hR2;
      field_simp at hR2;
      nlinarith [ show 0 < ρ * N ^ 2 by positivity, show 0 < R * X ^ 2 by exact mul_pos hR0 ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) ) ];
    rw [ ge_iff_le, div_le_div_iff₀ ] <;> try positivity;
    · rw [ ge_iff_le, le_div_iff₀ ] at hT;
      · field_simp at *;
        nlinarith [ show 0 < ρ * N ^ 2 by positivity ];
      · exact mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) );
    · exact mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) );
  have hX_pos : (0 : ℝ) < X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hlogX)
  -- The numerical cutoff and comparison losses enter only through their product.
  have hR2_sq : R^2 ≥ cE * ρ^5 * N^6 / ((256 * 512) * X^4) :=
    cutoff_energy_quadratic_lower_bound cE 256 512 ρ R X N
      (by norm_num) (by norm_num) hρ hX_pos hNpos hR2
  -- Substitute only the density estimate `N ≥ X/(2 log X)`.
  have hR2_sq_final : R^2 ≥
      cE * ρ^5 * X^2 / ((64 * 256 * 512) * (Real.log X)^6) := by
    -- From hN: N^6 ≥ (X/(2 log X))^6 = X^6/(64*(log X)^6).
    have hN6 : N^6 ≥ X^6 / (64 * (Real.log X)^6) := by
      exact le_trans ( by rw [ div_pow ] ; ring_nf; norm_num ) ( pow_le_pow_left₀ ( by positivity ) hN 6 );
    refine le_trans ?_ hR2_sq;
    convert mul_le_mul_of_nonneg_left hN6
      (show 0 ≤ cE * ρ ^ 5 / ((256 * 512) * X ^ 4) by positivity) using 1 ; ring_nf;
    · grind;
    · ring;
  refine' le_of_pow_le_pow_left₀ ( by positivity ) ( by positivity ) ( le_trans _ hR2_sq_final );
  field_simp;
  rw [ Real.sq_sqrt ( by positivity ) ] ; nlinarith [ show 0 ≤ ρ * cE * X ^ 2 by positivity ]

/-
**Right-disjunct chase.**  Pure algebra: the tiny-mass disjunct of the covering
    dichotomy forces `R ≳ X/log³X`.
-/
lemma high_cutoff_energy_bound (ρ : ℝ) (hρ : 0 < ρ) (_hρ4 : ρ ≤ 1/4)
    (X : ℕ) (N R u : ℝ)
    (hlogX : 0 < Real.log X) (hN : (X:ℝ)/(2*Real.log X) ≤ N) (hNpos : 0 < N)
    (_hR0 : 0 < R) (_hu0 : 0 ≤ u)
    (husq : u^2 = (256/ρ)*R*(X:ℝ)^2/N^2)
    (hbigN : 2304/ρ ≤ N)
    (hdisj : ρ*N/4 < (2*u+2)*(32*(u+1)+8)) :
    ρ^2 / (4718592) * (X:ℝ)/(Real.log X)^3 ≤ R := by
  rw [ div_le_iff₀ ( by positivity ) ] at *;
  have h_combined : ρ^2 * N^3 / 8 < 73728 * R * X^2 := by
    field_simp at *;
    nlinarith [ sq_nonneg ( u - 1 ), mul_le_mul_of_nonneg_left hbigN hρ.le, mul_le_mul_of_nonneg_left hbigN hNpos.le ];
  have h_combined : N^3 ≥ X^3 / (8 * (Real.log X)^3) := by
    rw [ ge_iff_le, div_le_iff₀ ];
    · convert pow_le_pow_left₀ ( by positivity ) hN 3 using 1 ; ring;
    · positivity;
  rw [ ge_iff_le, div_le_iff₀ ] at h_combined <;> nlinarith [ pow_pos hlogX 3 ]

/-
**Get the dichotomy in `u = B/X` form.**  Picks the base point `p0` and threshold
    `B = √(A²R)·X²/N` (so the exception count is `≤ ρN/8`), and packages the covering
    dichotomy with `u := B/X`.
-/
set_option maxHeartbeats 1000000 in
lemma nondominant_energy_dichotomy
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hcard2 : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (hnd : ¬ HasDominantLabel X P a ρ)
    (R : ℝ) (hR0 : 0 < R) (hQ : QP P a ≤ R)
    (hAR : (256/ρ)*R ≤ ((P.card:ℝ))^2/16)
    (h1 : 1 ≤ ρ*(P.card:ℝ)/8)
    (cE : ℝ) (hcE0 : 0 < cE)
    (hcE : ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1]
        (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 →
        ∀ (C C' : Finset Q),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) →
          Disjoint C C' →
          (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) →
          cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2) :
    ∃ u : ℝ, 0 ≤ u ∧ u^2 = (256/ρ)*R*(X:ℝ)^2/(P.card:ℝ)^2 ∧
      (cE*(ρ*(P.card:ℝ)/2)^4/(2*(X:ℝ)^2*(2*u+2)^2) ≤ R ∨
        ρ*(P.card:ℝ)/4 < (2*u+2)*(32*(u+1)+8)) := by
  refine' ⟨ Real.sqrt ( 256 / ρ * R * X ^ 2 / P.card ^ 2 ), _, _, _ ⟩;
  · positivity;
  · rw [ Real.sq_sqrt ( by positivity ) ];
  · obtain ⟨p0, hp0mem, hp0⟩ : ∃ p0 : P, p0 ∈ P.attach ∧ ((P.attach.filter (fun q => q ≠ p0 ∧ Real.sqrt ((256 / ρ) * R) * (X : ℝ) ^ 2 / P.card < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) ≤ ρ * P.card / 8 := by
      have := exists_sparse_crt_basepoint X hX P hP (by linarith) a R hR0.le hQ (Real.sqrt ((256 / ρ) * R) * (X : ℝ) ^ 2 / P.card) (by
      positivity);
      convert this using 4;
      field_simp;
      rw [ Real.sq_sqrt ( by positivity ), mul_div_cancel₀ _ ( by positivity ) ] ; ring;
    convert label_covering_energy_dichotomy X hX P hP hcard2 ρ hρ hρ4 a hnd R hR0 hQ p0 ( Real.sqrt ( 256 / ρ * R ) * X ^ 2 / P.card ) _ _ _ _ cE hcE0 hcE using 2 <;> norm_num [ hR0.le, hρ.le, hX ];
    any_goals assumption;
    · field_simp;
    · field_simp;
    · positivity;
    · rw [ div_le_iff₀ ];
      · convert mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt hAR ) ( show ( 0 : ℝ ) ≤ X ^ 2 by positivity ) using 1 ; ring_nf;
        · norm_num [ hρ.le, hR0.le ] ; ring;
        · norm_num ; ring;
      · positivity;
    · convert hp0 using 4 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hR0.le, hρ.le ]

/-
For `X ≥ 3`, `1 ≤ Real.log X`.
-/
lemma one_le_log_of_large (X : ℕ) (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] ) )

/-
When `1 ≤ Real.log X`, `X/ log X ≤ X· log X`.
-/
lemma self_div_log_le_self (X : ℕ) (h : 1 ≤ Real.log X) :
    (X:ℝ)/Real.log X ≤ (X:ℝ)*Real.log X := by
  rw [ div_le_iff₀ ] <;> nlinarith [ show ( X : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at h ) ), mul_le_mul_of_nonneg_left h ( show ( 0 : ℝ ) ≤ X by positivity ) ]

/-
Combine `R ≤ c2·X/log³X` with the threshold `64·A²·c2 ≤ X·log X` to get `A²R ≤ N²/16`.
-/
lemma nondominant_auxiliary_range_bound (ρ c2 : ℝ) (hρ : 0 < ρ) (_hc2 : 0 ≤ c2)
    (X : ℕ) (N R : ℝ) (hlog0 : 0 < Real.log X)
    (hN : (X:ℝ)/(2*Real.log X) ≤ N)
    (hR : R ≤ c2*(X:ℝ)/(Real.log X)^3)
    (hThr1 : 64*(256/ρ)*c2 ≤ (X:ℝ)*Real.log X) :
    (256/ρ)*R ≤ N^2/16 := by
  have hXpos : (0 : ℝ) < X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hlog0)
  refine le_trans ( mul_le_mul_of_nonneg_left hR ( by positivity ) ) ?_;
  rw [ ← mul_div_assoc, div_le_iff₀ ] at *;
  · ring_nf at *;
    nlinarith [ sq_nonneg ( N * Real.log X - X ), mul_le_mul_of_nonneg_left hN hlog0.le, mul_le_mul_of_nonneg_left hN hXpos.le, Real.log_le_sub_one_of_pos hXpos, Real.log_le_sub_one_of_pos hlog0 ];
  · positivity;
  · positivity

/-
Combine `R ≤ c2·X/log³X` with `8192·c2/(cEρ⁴) ≤ X/log X` to bound `R` by the
    case-B threshold.
-/
lemma cutoff_energy_upper_bound (cE ρ c2 : ℝ) (hcE0 : 0 < cE) (hρ : 0 < ρ)
    (X : ℕ) (R : ℝ) (hlog0 : 0 < Real.log X)
    (hR : R ≤ c2*(X:ℝ)/(Real.log X)^3)
    (hThr2 : 8192*c2/(cE*ρ^4) ≤ (X:ℝ)/Real.log X) :
    R ≤ cE*ρ^4*(X:ℝ)^2/(8192*(Real.log X)^4) := by
  rw [ div_le_div_iff₀ ] at * <;> try positivity;
  rw [ le_div_iff₀ ] at * <;> nlinarith [ pow_pos hlog0 3, pow_pos hlog0 4 ]

/-
**Theorem B** (`29 §6`).  For `ρ ∈ (0,1/4]` and `X` large: any low-energy
    assignment that is **not** dominant forces `R ≫ X/log³X`.  Concretely there is
    `c₂ > 0` with: if `QP P a ≤ R` and `a` is not `ρ`-dominant then
    `R ≥ c₂ · X / (Real.log X)^3`.

    Proof (`29 §6`): the covering construction (`29 §4`) produces `≥ 2` substantial
    classes; Lemma E across them, with the mass accounting (`M₂ ≥ ρN/2`), forces
    `R² ≫ N⁴/(X²log²X)`, i.e. `R ≫ N²/(X log X) ≫ X/log³X`.

    **Status**: fully proved (no `sorry`).  Decomposed into the covering helpers
    (`large_crt_pair_count`, `exists_sparse_crt_basepoint`, `crt_label_shortlist_bound`), the energy
    core (`class_partition_energy_lower_bound`, `crossLabel_energy_sum_le`), the covering
    dichotomy (`label_covering_energy_dichotomy`) with the mass accounting, and the
    parameter chase (`nondominant_energy_dichotomy`, `low_cutoff_energy_bound`,
    `high_cutoff_energy_bound`).
-/
theorem nondominant_energy_lower_bound
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (a : BlockAssignment P) (R : ℝ),
          QP P a ≤ R → ¬ HasDominantLabel X P a ρ →
            c2 * (X:ℝ) / (Real.log X)^3 ≤ R := by
  revert ρ hρ hρ4;
  obtain ⟨cE, hcE0, hcE⟩ : ∃ cE : ℝ, 0 < cE ∧ ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1] (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ), n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 → ∀ (C C' : Finset Q), (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) → (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) → Disjoint C C' → (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card → (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) → (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) → cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤ ∑ p ∈ C, ∑ q ∈ C', ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2 := by
    apply crossLabel_energy_lower_bound;
  intro ρ hρ hρ4
  set c2 := min (ρ^2 * Real.sqrt (cE*ρ) / 10^6) (ρ^2/4718592) with hc2def
  have hc2pos : 0 < c2 := by
    exact lt_min ( by positivity ) ( by positivity )
  generalize_proofs at *;
  set K := max (max 4 (16/ρ)) (max (4608/ρ) (max (64*(256/ρ)*c2) (8192*c2/(cE*ρ^4)))) with hKdef
  obtain ⟨X0', hX0'0, hK⟩ := exists_logarithmic_threshold K
  use c2, ⌈X0'⌉₊ + 3, hc2pos, by positivity
  intro X hX P inst hP hN a R hQ hnd
  have hX3 : 3 ≤ X := by
    exact_mod_cast hX.trans' ( le_add_of_nonneg_left <| Nat.cast_nonneg _ )
  have hX1 : 1 ≤ X := by
    linarith
  generalize_proofs at *;
  have hlog1 : 1 ≤ Real.log X := by
    exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] ) )
  have hlog0 : 0 < Real.log X := by
    linarith
  have hXpos : (0:ℝ) < X := by positivity
  have hKX : K ≤ (X:ℝ)/Real.log X := by
    exact hK X ( by linarith [ Nat.le_ceil X0' ] )
  have hself := self_div_log_le_self X hlog1
  set N := (P.card:ℝ) with hNdef
  have hNK : K/2 ≤ N := by
    have h1 : K / 2 ≤ (X:ℝ)/(2*Real.log X) := by
      convert div_le_div_of_nonneg_right hKX zero_le_two using 1
      all_goals first | rfl | ring_nf
    generalize_proofs at *;
    linarith [hN]
  have hNpos : 0 < N := by
    exact lt_of_lt_of_le ( by positivity ) hNK
  have hcard2 : 2 ≤ P.card := by
    have h1 : K/2 ≥ 2 := by
      exact le_trans ( by norm_num ) ( div_le_div_of_nonneg_right ( le_max_left _ _ |> le_trans ( le_max_left _ _ ) ) zero_le_two )
    generalize_proofs at *;
    exact_mod_cast h1.trans hNK |> le_trans <| hNdef.le
  generalize_proofs at *;
  by_cases hRbig : c2 * (X:ℝ)/(Real.log X)^3 ≤ R;
  · exact hRbig;
  · have hRle' : R ≤ c2 * (X:ℝ)/(Real.log X)^3 := by
      exact le_of_not_ge hRbig
    have hR0 : 0 < R := by
      by_contra hRneg
      push Not at hRneg
      exact hnd (zero_label_dominant_of_large_class X hX1 P hP hcard2 a ρ hρ.le (le_antisymm (le_trans hQ hRneg) (QP_nonneg P a)))
    generalize_proofs at *;
    have hThr1 : 64*(256/ρ)*c2 ≤ (X:ℝ)*Real.log X := by
      grind +splitImp
    have hThr2 : 8192*c2/(cE*ρ^4) ≤ (X:ℝ)/Real.log X := by
      exact le_trans ( le_max_of_le_right <| le_max_of_le_right <| le_max_right _ _ ) hKX
    have hAR : (256/ρ)*R ≤ N^2/16 := by
      apply nondominant_auxiliary_range_bound ρ c2 hρ hc2pos.le X N R hlog0 hN hRle' hThr1
    have h1 : 1 ≤ ρ*N/8 := by
      have h16 : 16 / ρ ≤ K := by
        exact le_max_of_le_left ( le_max_right _ _ )
      generalize_proofs at *;
      nlinarith [ mul_div_cancel₀ 16 hρ.ne' ]
    generalize_proofs at *;
    obtain ⟨u, hu0, husq, hdisj⟩ := nondominant_energy_dichotomy X hX1 P hP hcard2 ρ hρ hρ4 a hnd R hR0 hQ hAR h1 cE hcE0 hcE
    rcases hdisj with hL | hRgt
    · have hRle : R ≤ cE*ρ^4*(X:ℝ)^2/(8192*(Real.log X)^4) := cutoff_energy_upper_bound cE ρ c2 hcE0 hρ X R hlog0 hRle' hThr2
      have hcl := low_cutoff_energy_bound cE ρ hcE0 hρ hρ4 X N R u hlog0 hN hNpos hR0 hu0 husq hRle hL
      refine le_trans ?_ hcl
      have hcle : c2 ≤ ρ^2 * Real.sqrt (cE*ρ) / 10^6 := min_le_left _ _
      gcongr
    · have hbigN : 2304/ρ ≤ N := by
        grind
      have hcr := high_cutoff_energy_bound ρ hρ hρ4 X N R u hlog0 hN hNpos hR0 hu0 husq hbigN hRgt
      refine le_trans ?_ hcr
      have hcr2 : c2 ≤ ρ^2/4718592 := min_le_right _ _
      gcongr

/-! ## Low-energy level-set bound

The nondominant energy lower bound makes every assignment below
`c'X/log³X` dominant, where the dominant level-set estimate applies. -/

/-
**Corollary** (`29 §7`).  For `ε > 0` there are `c', X₀` so that for `X ≥ X₀`
    and all `R ≤ c'·X/log³X`,
    `#{a : QP P a ≤ R} ≤ exp(εR)·(1 + 20√R/σ_P)`.

    **Status**: fully proved — direct combination of `nondominant_energy_lower_bound`
    (all such assignments are dominant) and `dominant_level_set_bound`.
-/
theorem low_energy_level_set_bound
    (eps : ℝ) (hε : 0 < eps) (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (cp X0 : ℝ), 0 < cp ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R → R ≤ cp * (X:ℝ) / (Real.log X)^3 →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ Real.exp (eps * R) * (1 + 20 * Real.sqrt R / sigmaP P) := by
  obtain ⟨X0A, hX0A, HA⟩ := dominant_level_set_bound eps hε ρ hρ hρ4
  obtain ⟨c2, X0B, hc2, hX0B, HB⟩ := nondominant_energy_lower_bound ρ hρ hρ4
  use c2 / 2, max X0A X0B;
  refine' ⟨ by positivity, by positivity, fun X hX P hP hN R hR₁ hR₂ => _ ⟩;
  intro hR₃
  have h_dom : ∀ a : BlockAssignment P, QP P a ≤ hR₁ → HasDominantLabel X P a ρ := by
    intro a ha;
    contrapose! HB;
    refine' ⟨ X, _, P, hP, hN, R, a, hR₁, ha, HB, _ ⟩;
    · exact le_trans ( le_max_right _ _ ) hX;
    · grind;
  refine' le_trans _ ( le_trans ( HA X ( le_trans ( le_max_left _ _ ) hX ) P hN R hR₁ hR₂ ) _ );
  · exact_mod_cast Finset.card_le_card fun x hx => by aesop;
  · gcongr;
    · exact Real.sqrt_nonneg _;
    · rw [ div_le_iff₀ ] <;> linarith

/-
**Lemma L2u (dominant label uniqueness, note 38 §3).**  Two integer labels
    `m, m'`, each agreeing with `a` on a `(1-ρ)`-fraction of the primes of a
    block `P ⊆ [X, 2X]` (with `|m|,|m'| ≤ X²/2`), must coincide.  Two-prime
    argument: the two label classes intersect in `≥ |P|/2 ≥ 2` primes; any two
    distinct such primes `p, q` divide `m - m'`, so `pq ∣ m - m'`; but
    `pq ≥ X(X+1) > X² ≥ |m - m'|`, forcing `m = m'`.
-/
lemma dominant_label_unique (X : ℕ) (hX : 4 ≤ X) (P : Finset ℕ)
    [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) (hN : 4 ≤ P.card)
    (ρ : ℝ) (_hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (a : BlockAssignment P) (m m' : ℤ)
    (hm : |m| ≤ (X : ℤ) ^ 2 / 2) (hm' : |m'| ≤ (X : ℤ) ^ 2 / 2)
    (hclass : (1 - ρ) * (P.card : ℝ) ≤ ((P.attach.filter
        (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))
    (hclass' : (1 - ρ) * (P.card : ℝ) ≤ ((P.attach.filter
        (fun p => a p = ((m' : ℤ) : ZMod (p : ℕ)))).card : ℝ)) :
    m = m' := by
  -- By Lemma L1u, the intersection of these two subsets has at least two elements.
  have h_inter : ∃ p q : P, p.1 ≠ q.1 ∧ a p = (m : ZMod p.1) ∧ a p = (m' : ZMod p.1) ∧ a q = (m : ZMod q.1) ∧ a q = (m' : ZMod q.1) := by
    have h_inter : (Finset.filter (fun p : P => a p = (m : ZMod p.1)) (Finset.univ : Finset P)).card + (Finset.filter (fun p : P => a p = (m' : ZMod p.1)) (Finset.univ : Finset P)).card ≥ (3 / 2 : ℝ) * P.card := by
      norm_num [ Finset.filter_attach ] at * ; nlinarith [ ( by norm_cast : ( 4 :ℝ ) ≤ P.card ) ] ;
    have h_inter : (Finset.filter (fun p : P => a p = (m : ZMod p.1)) (Finset.univ : Finset P) ∩ Finset.filter (fun p : P => a p = (m' : ZMod p.1)) (Finset.univ : Finset P)).card ≥ 2 := by
      have h_inter : Finset.card (Finset.filter (fun p : P => a p = (m : ZMod p.1)) Finset.univ ∩ Finset.filter (fun p : P => a p = (m' : ZMod p.1)) Finset.univ) ≥ Finset.card (Finset.filter (fun p : P => a p = (m : ZMod p.1)) Finset.univ) + Finset.card (Finset.filter (fun p : P => a p = (m' : ZMod p.1)) Finset.univ) - P.card := by
        rw [ ← Finset.card_union_add_card_inter ];
        exact Nat.sub_le_of_le_add <| by linarith [ show Finset.card ( Finset.filter ( fun p : P => a p = ( m : ZMod p.1 ) ) Finset.univ ∪ Finset.filter ( fun p : P => a p = ( m' : ZMod p.1 ) ) Finset.univ ) ≤ P.card from le_trans ( Finset.card_le_univ _ ) ( by simp ) ] ;
      exact le_trans ( Nat.le_sub_of_add_le ( by rw [ ← @Nat.cast_le ℝ ] ; push_cast; linarith [ show ( P.card : ℝ ) ≥ 4 by norm_cast ] ) ) h_inter;
    obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.mp h_inter; use p, q; aesop;
  obtain ⟨ p, q, hpq, hp, hp', hq, hq' ⟩ := h_inter; have := hP p p.2; have := hP q q.2; simp_all +decide [ ZMod.intCast_eq_intCast_iff' ] ;
  -- Since $p$ and $q$ are distinct primes, their product $pq$ divides $m - m'$.
  have h_div : (p.1 * q.1 : ℤ) ∣ (m - m') := by
    convert Int.coe_lcm_dvd ( Int.modEq_iff_dvd.mp hp ) ( Int.modEq_iff_dvd.mp hq ) using 1;
    exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| by have := Nat.coprime_primes ( hP p p.2 |>.1 ) ( hP q q.2 |>.1 ) ; aesop );
  -- Since $p$ and $q$ are distinct primes, their product $pq$ is greater than $X^2$.
  have h_prod_gt_X2 : (p.1 * q.1 : ℤ) > X^2 := by
    by_cases hpq_eq : p.1 = q.1;
    · exact False.elim <| hpq <| Subtype.ext hpq_eq;
    · cases lt_or_gt_of_ne hpq_eq <;> nlinarith [ hP p p.2, hP q q.2 ];
  contrapose! h_prod_gt_X2;
  exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr h_prod_gt_X2 ) ) ( by simpa using h_div ) |> le_trans <| by cases abs_cases ( m - m' ) <;> cases abs_cases m <;> cases abs_cases m' <;> linarith [ Int.mul_ediv_add_emod ( X^2 ) 2, Int.emod_nonneg ( X^2 ) two_ne_zero, Int.emod_lt_of_pos ( X^2 ) two_pos ] ;

/-
**Lemma L5 (fixed-label fiber bound, note 38 §3).**  For a fixed label `m`
    of size `|m| ≤ N·X/16`, the number of assignments with `QP ≤ R` whose
    `m`-class covers `≥ (1-ρ)N` primes is `≤ exp(εR)`.  This is the `hfibcard`
    block of `dominant_level_set_bound`, with the label-size bound taken as a
    hypothesis.
-/
lemma fixed_label_level_set_bound (eps ρ : ℝ) (hε : 0 < eps) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1],
          (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) →
          (X : ℝ) / (2 * Real.log X) ≤ P.card →
          ∀ (m : ℤ), |(m : ℝ)| ≤ (P.card : ℝ) * (X : ℝ) / 16 →
          ∀ (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter (fun a : BlockAssignment P =>
                QP P a ≤ R ∧
                (1 - ρ) * (P.card : ℝ) ≤ ((P.attach.filter
                  (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
              ≤ Real.exp (eps * R) := by
  revert eps ρ hε hρ hρ4;
  intro eps ρ hε hρ hρ4
  obtain ⟨X0e, hX0e, Hent⟩ := dominant_encoding_entropy_bound eps ρ hε hρ hρ4
  obtain ⟨X0c, hX0c, Hlog⟩ := RequestProject.eventually_const_mul_log_le_nat 64
  use max (max X0e X0c) 16;
  refine' ⟨ by positivity, fun X hX P _hP hN m hmabs R hR => _ ⟩;
  intro hR1
  set N := P.card
  have hN32 : 32 ≤ N := by
    have hN32 : 32 ≤ X / (2 * Real.log X) := by
      rw [ le_div_iff₀ ] <;> nlinarith [ Hlog X ( by linarith [ le_max_left ( max X0e X0c ) 16, le_max_right ( max X0e X0c ) 16, le_max_left X0e X0c, le_max_right X0e X0c ] ), Real.log_pos ( show ( X : ℝ ) > 1 by linarith [ le_max_left ( max X0e X0c ) 16, le_max_right ( max X0e X0c ) 16, le_max_left X0e X0c, le_max_right X0e X0c ] ) ];
    exact_mod_cast hN32.trans m
  have hN2X : N ≤ 2 * X := by
    convert RequestProject.card_le_upper_bound_of_pos P (2 * X)
      (fun p hp => (hN p hp).1.pos) (fun p hp => (hN p hp).2.2) using 1
  set Hr := 2^15 * hR * (X:ℝ)^2 / ((1-ρ)*(N:ℝ)^3) with hHr_def
  have hHr0 : 0 ≤ Hr := by
    exact div_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) ( by positivity ) ) ( sq_nonneg _ ) ) ( mul_nonneg ( by linarith ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) )
  set h_floor := Nat.floor Hr with h_floor_def
  have h_floor_le_Hr : (h_floor : ℝ) ≤ Hr := by
    exact Nat.floor_le hHr0
  have h_filter_subset : Finset.filter (fun a => QP P a ≤ hR ∧ (1 - ρ) * (N : ℝ) ≤ ((P.attach.filter (fun p => a p = ((hmabs : ℤ) : ZMod (p : ℕ)))).card : ℝ)) Finset.univ ⊆ Finset.filter (fun a => (P.attach.filter (fun q => a q ≠ ((hmabs : ℤ) : ZMod (q : ℕ)))).card ≤ h_floor) Finset.univ := by
    intro a ha
    simp [h_floor_def] at *;
    have := dominant_exception_count_bound X ( by linarith ) P hN ( by linarith ) ρ hρ ( by linarith ) a hmabs hR hR1 ha.1 R ha.2; norm_num at *;
    exact Nat.le_floor <| by aesop;
  refine' le_trans _ ( Hent X N h_floor hR _ _ _ _ _ _ );
  any_goals assumption;
  · refine' le_trans _ ( dominant_assignment_encoding_bound X ( by linarith [ show X ≥ 16 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ) P ( fun p hp => hN p hp ) hmabs h_floor );
    exact_mod_cast Finset.card_le_card h_filter_subset;
  · exact le_trans ( le_max_of_le_left ( le_max_left _ _ ) ) hX;
  · linarith

/-
**Lemma L4c (cold exception bound, note 38 §3).**  For a cold block
    (`R ≤ c₂·X/log³X`) the dominant-label exception set has *absolutely* bounded
    size `e0 = 2^18·c₂/(1-ρ)`, uniformly in `X ≥ X0`.  Corollary of
    `dominant_exception_count_bound` with the density `N ≥ X/(2 log X)` and the cold range
    inserted.
-/
lemma cold_exception_count_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ (e0 X0 : ℝ), 0 < e0 ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1],
          (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) →
          (X : ℝ) / (2 * Real.log X) ≤ P.card →
          ∀ (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
          QP P a ≤ R → R ≤ c2 * X / (Real.log X) ^ 3 →
          |(m : ℝ)| ≤ (P.card : ℝ) * (X : ℝ) / 16 →
          (1 - ρ) * (P.card : ℝ) ≤ ((P.attach.filter
              (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
            ((P.attach.filter (fun q => a q ≠ ((m : ℤ) : ZMod (q : ℕ)))).card : ℝ) ≤ e0 := by
  obtain ⟨X0c, hX0c⟩ := RequestProject.eventually_const_mul_log_le_nat 64
  refine' ⟨ 2 ^ 18 * c2 / ( 1 - ρ ), Max.max X0c 16, _, _, _ ⟩ <;> norm_num;
  · exact div_pos ( by positivity ) ( by linarith );
  · intro X hX1 hX2 P _ hP hN a m R hR1 hQ hRcold hmsmall hclass
    have hN32 : 32 ≤ P.card := by
      exact_mod_cast ( by nlinarith [ hX0c.2 X hX1, show ( X : ℝ ) ≥ 16 by exact_mod_cast hX2, Real.log_pos ( show ( X : ℝ ) > 1 by exact_mod_cast by linarith ), mul_div_cancel₀ ( X : ℝ ) ( show ( 2 * Real.log X ) ≠ 0 by exact mul_ne_zero two_ne_zero <| ne_of_gt <| Real.log_pos <| show ( X : ℝ ) > 1 by exact_mod_cast by linarith ) ] : ( 32 : ℝ ) ≤ P.card );
    refine' le_trans _ ( _ : 2 ^ 15 * R * X ^ 2 / ( ( 1 - ρ ) * P.card ^ 3 ) ≤ _ );
    · convert dominant_exception_count_bound X hX2 P hP hN32 ρ hρ hρ4 a m R hR1 hQ hmsmall hclass using 1;
      exact fun p => by have := hP p p.2; exact ⟨ Nat.Prime.ne_zero this.1 ⟩ ;
    · rw [ div_le_div_iff₀ ] <;> try nlinarith [ show ( P.card : ℝ ) ≥ 32 by norm_cast ];
      · -- Substitute $N \geq X / (2 \log X)$ into the inequality.
        have hN_sub : (P.card : ℝ) ^ 3 ≥ (X / (2 * Real.log X)) ^ 3 := by
          exact pow_le_pow_left₀ ( by positivity ) hN 3;
        refine' le_trans _ ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left hN_sub <| sub_nonneg.mpr <| by linarith ) <| by positivity );
        convert mul_le_mul_of_nonneg_right hRcold ( show 0 ≤ 2 ^ 15 * ( 1 - ρ ) * X ^ 2 by exact mul_nonneg ( mul_nonneg ( by norm_num ) ( by linarith ) ) ( by positivity ) ) using 1 ; ring;
        ring;
      · exact mul_pos ( by linarith ) ( by positivity )

/-
**Lemma L3c (cold-label size chain, note 38 §3).**  For a *cold* block
    (`R ≤ c₂·X/log³X`) with a dominant label `m`, the label is small:
    `|m| ≤ N·X/16`, uniformly in `X ≥ X0(c₂)`.  This feeds both `fixed_label_level_set_bound`
    / `cold_exception_count_bound` (which require `|m| ≤ N·X/16`) and the `hm`-type
    hypotheses of `mismatch_penalty_with_exceptions`.

    Proof: `dominant_label_bound` gives `|m| ≤ (5/(1-ρ))·√R/σ_P`; the cold range
    `R ≤ c₂·X/log³X` together with the density `N ≥ X/(2 log X)` implies the
    polynomial bound `R ≤ N⁴(1-ρ)²/(409600·X²)` for `X ≥ X0(c₂)` (a `K·log X ≤ X`
    threshold from `Core.Asymptotics`), and then `dominant_label_linear_bound`
    converts `(5/(1-ρ))·√R/σ_P ≤ N·X/16`.
-/
lemma cold_label_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (c2 : ℝ) (_hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1],
          (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) →
          (X : ℝ) / (2 * Real.log X) ≤ P.card →
          ∀ (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
          |m| ≤ (X : ℤ) ^ 2 / 2 →
          (1 - ρ) * (P.card : ℝ) ≤ ((P.attach.filter
              (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
          QP P a ≤ R → R ≤ c2 * X / (Real.log X) ^ 3 →
            |(m : ℝ)| ≤ (P.card : ℝ) * (X : ℝ) / 16 := by
  -- Choose thresholds for the two log-vs-linear estimates used below.
  obtain ⟨X0K, hX0K_pos, hX0K⟩ := RequestProject.eventually_const_mul_log_le_nat
    (6553600 * c2 / (1 - ρ)^2)
  obtain ⟨X0d, hX0d_pos, hX0d⟩ := RequestProject.eventually_const_mul_log_le_nat 64
  refine' ⟨ Max.max 16 ( Max.max X0K X0d ), _, _ ⟩;
  · positivity;
  · intro X hX P _ hP hN a m R hR hm hclass hQ hRcold
    have hN_ge_2 : 2 ≤ P.card := by
      have hN_ge_2 : (X : ℝ) / (2 * Real.log X) ≥ 2 := by
        rw [ ge_iff_le, le_div_iff₀ ] <;> norm_num at *;
        · linarith [ hX0d X hX.2.2 ];
        · exact Real.log_pos ( by norm_cast; linarith );
      exact_mod_cast hN_ge_2.trans hN
    have hN_ge_8 : 8 ≤ P.card := by
      rw [ div_le_iff₀ ] at hN <;> norm_num at *;
      · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ hX0d X hX.2.2, Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith ] ;
      · exact Real.log_pos ( by norm_cast; linarith )
    have hlogX_pos : 0 < Real.log X := by
      exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ show X ≥ 16 by exact_mod_cast le_trans ( le_max_left _ _ ) hX ] ;
    have hRpoly : R ≤ (P.card : ℝ)^4 * (1 - ρ)^2 / (409600 * X^2) := by
      have hRpoly : R ≤ c2 * X / (Real.log X)^3 ∧ c2 * X / (Real.log X)^3 ≤ (X / (2 * Real.log X))^4 * (1 - ρ)^2 / (409600 * X^2) := by
        have := hX0K X ( by linarith [ le_max_left 16 ( max X0K X0d ), le_max_right 16 ( max X0K X0d ), le_max_left X0K X0d, le_max_right X0K X0d ] );
        rw [ div_pow, div_mul_eq_mul_div, div_div, div_le_div_iff₀ ] <;> try positivity;
        · rw [ div_mul_eq_mul_div, div_le_iff₀ ] at this <;> try nlinarith;
          exact ⟨ hRcold, by nlinarith [ show 0 < ( X : ℝ ) ^ 3 * Real.log X ^ 3 by exact mul_pos ( pow_pos ( Nat.cast_pos.mpr ( by linarith [ show X ≥ 16 by exact_mod_cast le_trans ( le_max_left _ _ ) hX ] ) ) 3 ) ( pow_pos hlogX_pos 3 ) ] ⟩;
        · exact mul_pos ( pow_pos ( mul_pos zero_lt_two hlogX_pos ) 4 ) ( mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) ) );
      refine le_trans hRpoly.1 <| hRpoly.2.trans ?_;
      gcongr;
    convert dominant_label_bound X ( by norm_num at hX; linarith ) P hP hN_ge_8 ρ hρ hρ4 a m R ( by
      exact hm ) hclass hQ |> le_trans <| dominant_label_linear_bound X ( by norm_num at hX; linarith ) P hP hN_ge_2 ρ hρ hρ4 R ( by positivity ) hRpoly using 1

end LocalEnergy
