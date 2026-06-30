import RequestProject.LocalEnergy.CRTModel
import RequestProject.LocalEnergy.ReciprocalDispersion

/-!
# Cross-label energy

Congruence counting bounds close CRT representatives from two distinct residue
classes, forcing a quantitative quadratic-energy contribution between them.
-/

open Finset

namespace LocalEnergy

open scoped Classical

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
For distinct integer labels `n ≠ n'` with
    `|n|, |n'| ≤ B ≤ X²/4`, and disjoint prime sets `C, C' ⊆ [X,2X]` on which `a`
    has constant residues `n`, `n'` respectively, with `|C| ≥ 32(B/X+1)` and
    `|C'| ≥ 8`:
    `∑_{p∈C, q∈C'} (H_{pq}/pq)² ≥ c·|C|³|C'|/X²` for an absolute `c > 0`.

    Reduce to `LocalEnergy.linearCongruence_pair_count` with `w = n'-n`; at most `2`
    primes divide `d = n'-n`; for the rest, `≤ 8δX+4B/X+2` cross pairs are close,
    so `≥ |C||C'|/2` pairs carry energy `≥ δ²`.

    **Verification finding (statement fix).**  The V5 statement omitted the
    hypotheses that the elements of `C` and `C'` are primes in `[X, 2X]`.  Without
    them the lemma is **false**: `crtRepr p q · ·` returns `0` whenever `p, q` are
    not coprime, so taking `C, C'` to consist of (say) even composite numbers
    makes every cross term `0` and the left sum `0`, while the right-hand side
    `c·|C|³|C'|/X²` is strictly positive.  The paper (`29 §5`) explicitly takes
    `C, C'` to be "sets of primes in `[X,2X]`", and Lemma D needs `q` prime with
    `X ≤ q`. The hypotheses `hCp`, `hC'p` below restore this.

    The constant `1/8192` follows from `crossLabel_close_fiber_bound`,
    `crossLabel_close_pair_count`, the choice `δ = |C|/(64X)`, and quadratic
    energy accounting.
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


end LocalEnergy
