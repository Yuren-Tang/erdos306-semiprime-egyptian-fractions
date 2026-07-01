import RequestProject.Core.SmallBallEnergy
import RequestProject.Core.ShortIntervalCongruence
import RequestProject.Core.UnitCircleResidue
import RequestProject.LocalEnergy.CRTModel

/-!
# Adjacent-scale reciprocal dispersion

Reciprocal phases over a prime interval are dispersed when the outer prime is
at the next dyadic scale. The resulting phase separation gives a lower bound
for CRT energy at a fixed outer prime.
-/

open Finset BigOperators Classical

noncomputable section

namespace LocalEnergy

/-
**Small reciprocal-phase count.**
    The number of `p ∈ P` whose reciprocal phase `‖d·p̄/q‖` is `≤ δ := |P|/(32X)`
    is at most `|P|/4 + 1`.
-/
lemma adjacent_scale_small_phase_count (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    ((P.filter (fun p =>
        (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ)
      ≤ (P.card : ℝ) / 4 + 1 := by
  -- Set δ := (P.card : ℝ)/(32*X).
  set δ := (P.card : ℝ) / (32 * X);
  -- Step 1 (witness): If p ∈ P and (norm ∘ ((↑) : ℝ → UnitAddCircle))((d:ℝ)*(pinv p:ℝ)/q) ≤ δ, then there is an integer u with |u| ≤ δ*q and (q:ℤ) ∣ (d * pinv p - u).
  have h_witness : ∀ p ∈ P, (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((d : ℝ) * (pinv p : ℝ) / q) ≤ δ → ∃ u : ℤ, |(u : ℝ)| ≤ δ * q ∧ (q : ℤ) ∣ (d - u * p) := by
    intro p hp hδ
    obtain ⟨u, hu⟩ : ∃ u : ℤ, |(u : ℝ)| ≤ δ * q ∧ (q : ℤ) ∣ (d * pinv p - u) := by
      apply RequestProject.exists_centered_residue_of_unitCircle_norm_le
        (d * pinv p) q hq.pos δ
      simpa [Function.comp_def] using hδ
    have h_div : (q : ℤ) ∣ (p * pinv p - 1) := by
      exact ⟨ p * pinv p / q - 1 / q, by linarith [ Nat.mod_add_div ( p * pinv p ) q, Nat.mod_add_div 1 q, hpinv p hp ] ⟩;
    exact ⟨ u, hu.1, by convert hu.2.mul_left p |> Int.dvd_sub <| h_div.mul_left d using 1; ring ⟩;
  -- Step 3 (cover): The filtered set is contained in the union over integers u ∈ Icc (-m) m (where m := ⌊δ*q⌋ ≥ 0) of {p ∈ P : (q:ℤ) ∣ (d - u*p)}.
  have h_cover : {p ∈ P | (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((d : ℝ) * (pinv p : ℝ) / q) ≤ δ} ⊆ Finset.biUnion (Finset.Icc (-⌊δ * q⌋) ⌊δ * q⌋) (fun u => {p ∈ P | (q : ℤ) ∣ (d - u * p)}) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨u, hu_abs, hu_dvd⟩ := h_witness p hp.1 hp.2
    rw [Finset.mem_biUnion]
    refine ⟨u, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_filter.mpr ⟨hp.1, hu_dvd⟩⟩
    · exact Int.le_of_lt_add_one <| by
        rw [← @Int.cast_lt ℝ]
        push_cast
        have hu_lower : -(δ * q) ≤ (u : ℝ) :=
          (neg_le_neg hu_abs).trans (neg_abs_le (u : ℝ))
        linarith [Int.floor_le (δ * q), Int.lt_floor_add_one (δ * q)]
    · exact Int.le_floor.mpr <| by
        exact (le_abs_self (u : ℝ)).trans hu_abs
  -- Step 4 (fiber ≤ 1): For each fixed u, the set {p ∈ P : (q:ℤ) ∣ (d - u*p)} has at most 1 element.
  have h_fiber : ∀ u : ℤ, (Finset.filter (fun p : ℕ => (q : ℤ) ∣ (d - u * p)) P).card ≤ 1 := by
    intros u
    have h_fiber : ∀ p p' : ℕ, p ∈ P → p' ∈ P → (q : ℤ) ∣ (d - u * p) → (q : ℤ) ∣ (d - u * p') → p = p' := by
      intros p p' hp hp' hdiv hdiv'
      have h_eq : (q : ℤ) ∣ u * (p - p') := by
        rw [show u * ((p : ℤ) - p') = (d - u * p') - (d - u * p) by ring]
        exact dvd_sub hdiv' hdiv
      by_cases hu : (q : ℤ) ∣ u <;>
        simp_all +decide [dvd_sub_left, dvd_mul_of_dvd_left]
      have hdiff : (q : ℤ) ∣ (p : ℤ) - p' := (Int.Prime.dvd_mul' hq h_eq).resolve_left hu
      exact RequestProject.eq_of_dvd_sub_of_mem_Ico X (2 * X) q p p'
        (by omega) (Finset.mem_Ico.mpr ⟨(hP p hp).2.1, (hP p hp).2.2⟩)
        (Finset.mem_Ico.mpr ⟨(hP p' hp').2.1, (hP p' hp').2.2⟩) hdiff
    exact Finset.card_le_one.mpr fun p hp q hq => h_fiber p q ( Finset.mem_filter.mp hp |>.1 ) ( Finset.mem_filter.mp hq |>.1 ) ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_filter.mp hq |>.2 );
  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_cover ) _;
  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun u hu => h_fiber u ) _ ; norm_num;
  have h_floor : ⌊δ * q⌋ ≤ (P.card : ℝ) / 8 := by
    refine' le_trans ( Int.floor_le _ ) _;
    rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
  rw [ div_add_one, le_div_iff₀ ] at * <;> norm_cast at *;
  linarith [ Int.toNat_of_nonneg ( by linarith [ show ⌊δ * q⌋ ≥ 0 by exact Int.floor_nonneg.mpr ( by positivity ) ] : 0 ≤ ⌊δ * q⌋ + 1 + ⌊δ * q⌋ ) ]

/-
**Adjacent-scale reciprocal dispersion.**  For `P ⊆ primes ∩ [X, 2X)`, a prime
    `q ∈ [2X, 4X)`, and `q ∤ d`, the reciprocal-phase energy
    `∑_{p∈P} ‖d·p⁻¹/q‖²` is bounded below by `|P|³/(2¹¹X²)`.

    `pinv p` denotes the inverse of `p` modulo `q` (as an integer in `[0,q)`).

-/
theorem adjacent_scale_reciprocal_energy_lower_bound (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    (P.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ^ 2 := by
  by_cases hP_card : P.card ≤ 11;
  · -- For each p ∈ P, (norm ∘ ((↑) : ℝ → UnitAddCircle))((d:ℝ)*(pinv p:ℝ)/q) ≥ 1/q.
    have h_term_ge : ∀ p ∈ P, ((norm ∘ ((↑) : ℝ → UnitAddCircle)) ((d : ℝ) * (pinv p : ℝ) / (q : ℝ))) ^ 2 ≥ (1 / (q : ℝ)) ^ 2 := by
      intro p hp
      have h_not_div : ¬(q : ℤ) ∣ (d * pinv p) := by
        haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
        intro H; specialize hpinv p hp; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      gcongr
      simpa only [Function.comp_apply, Int.cast_mul, Int.cast_natCast] using
        RequestProject.inv_natCast_le_unitCircle_norm_int_div_nat
          q (Nat.Prime.pos hq) (d * pinv p) h_not_div
    refine le_trans ?_ ( Finset.sum_le_sum h_term_ge ) ; norm_num;
    field_simp;
    rw [ le_div_iff₀ ] <;> norm_cast <;> try nlinarith only [ hqlb, hqub, hX ] ;
    nlinarith [ Nat.pow_le_pow_left hP_card 2, Nat.pow_le_pow_left hqlb 2, Nat.pow_le_pow_left hqub.le 2, Nat.mul_le_mul_left ( #P ) ( show #P ^ 2 ≤ 121 by nlinarith only [ hP_card ] ) ];
  · -- Convert the small-phase count into a quadratic-energy lower bound.
    set δ := (P.card : ℝ) / (32 * X)
    have hP12 : 12 ≤ P.card := by omega
    have h_residue_count : ((P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ δ)).card : ℝ) ≤ P.card / 4 + 1 := by
      convert adjacent_scale_small_phase_count X hX P hP q hq hqlb hqub d hqd pinv hpinv using 1;
    have hsmall : ((P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle))
        ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ δ)).card : ℝ) ≤ P.card / 2 := by
      linarith [show (P.card : ℝ) ≥ 12 by exact_mod_cast hP12]
    have henergy := RequestProject.sum_sq_lower_bound_of_small_ball P
      (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle))
        ((d : ℝ) * (pinv p : ℝ) / (q : ℝ))) δ (P.card / 2)
      (by positivity) hsmall
    calc
      (P.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) =
          ((P.card : ℝ) - P.card / 2) * δ ^ 2 := by
        dsimp [δ]
        ring
      _ ≤ ∑ p ∈ P, (norm ∘ ((↑) : ℝ → UnitAddCircle))
          ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ^ 2 := henergy

/-
**CRT phase bridge (modulus `q`).**  For distinct primes `p ≠ q`, an inverse
    `pinv` of `p` mod `q`, and `H := crtRepr p q (m mod p) (m' mod q)`, the
    reciprocal phase `‖(m'-m)·p̄/q‖` is controlled by `|H|/(pq) + |m|/(pq)`.

    Proof: `H ≡ m (mod p)` so `v := (H-m)/p ∈ ℤ`; `v·p ≡ m'-m (mod q)` with
    `p·pinv ≡ 1` give `v ≡ (m'-m)·pinv (mod q)`, so
    `(norm ∘ ((↑) : ℝ → UnitAddCircle))((m'-m)·pinv/q) = (norm ∘ ((↑) : ℝ → UnitAddCircle))(v/q) ≤ |v|/q = |H-m|/(pq) ≤ (|H|+|m|)/(pq)`.
-/
lemma crt_representative_controls_reciprocal_phase (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m m' : ℤ) (pinv : ℕ) (hpinv : (p * pinv) % q = 1 % q) :
    (norm ∘ ((↑) : ℝ → UnitAddCircle)) (((m' - m : ℤ) : ℝ) * (pinv : ℝ) / (q : ℝ))
      ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ))
        + |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
  have h_coprime : Nat.Coprime p q := by
    simpa [ hpq ] using Nat.coprime_primes hp hq;
  obtain ⟨v, hv⟩ : ∃ v : ℤ, (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) - m = p * v := by
    have h_cong : (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) ≡ m [ZMOD p] := by
      have := crtRepr_congr_left p q ( m : ZMod p ) ( m' : ZMod q ) h_coprime; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    exact h_cong.symm.dvd;
  have h_div : (q : ℤ) ∣ ((m' - m) * pinv - v) := by
    have h_div : (q : ℤ) ∣ (p * v - (m' - m)) := by
      have h_div : (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) ≡ m' [ZMOD q] := by
        convert crtRepr_congr_right p q ( m : ZMod p ) ( m' : ZMod q ) h_coprime using 1;
        norm_num [ ← ZMod.intCast_eq_intCast_iff ];
      convert h_div.symm.dvd using 1 ; linarith;
    have h_div : (q : ℤ) ∣ (p * pinv - 1) := by
      exact ⟨ p * pinv / q - 1 / q, by linarith [ Nat.mod_add_div ( p * pinv ) q, Nat.mod_add_div 1 q ] ⟩;
    rw [show (m' - m) * (pinv : ℤ) - v =
        (p * pinv - 1) * v - (p * v - (m' - m)) * pinv by ring]
    exact dvd_sub (h_div.mul_right v)
      (‹(q : ℤ) ∣ p * v - (m' - m)›.mul_right pinv)
  have h_norm' :
      ‖((((m' - m) * pinv : ℤ) : ℝ) / (q : ℝ) : UnitAddCircle)‖ =
        ‖((v : ℝ) / (q : ℝ) : UnitAddCircle)‖ := by
    obtain ⟨ k, hk ⟩ := h_div;
    convert RequestProject.unitCircle_norm_add_intCast (v / q : ℝ) k using 1;
    have hreal : (((m' - m) * pinv : ℤ) : ℝ) / (q : ℝ) =
        (v : ℝ) / q + k := by
      rw [div_add', div_eq_div_iff] <;> norm_cast <;> nlinarith [hq.two_le]
    exact congr_arg norm (congr_arg (fun x : ℝ => (x : UnitAddCircle)) hreal)
  have h_norm : (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * pinv / (q : ℝ)) = (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((v : ℝ) / (q : ℝ)) := by
    simpa only [Function.comp_apply, Int.cast_sub, Int.cast_mul, Int.cast_natCast] using h_norm'
  have h_abs : |(v : ℝ) / (q : ℝ)| ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) - m| / (p * q) := by
    rw [ show ( crtRepr p q m m' : ℝ ) - m = p * v by exact_mod_cast hv ] ; norm_num [ abs_div, abs_mul, hp.ne_zero, hq.ne_zero ] ; ring_nf ;
    norm_num [ hp.ne_zero ];
  have h_abs : |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) - m| ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| + |(m : ℝ)| := by
    exact abs_sub _ _;
  exact h_norm.symm ▸ le_trans (RequestProject.unitCircle_norm_coe_le_abs _)
    (by convert le_trans ‹_› (div_le_div_of_nonneg_right h_abs (by positivity)) using 1; ring)

/-
**Fixed outer-prime CRT energy bound.**  For a single good prime `q ∈ [2X,4X)` (with
    `q ∤ m'-m`), the cross energy over `P ⊆ primes ∩ [X,2X)` against `q` is at
    least `|P|³/(2¹³X²)`.

    Proof: by `adjacent_scale_small_phase_count` at least `|P|/2` of the `p` have
    `‖(m'-m)·p̄/q‖ > δ = |P|/(32X)`; for each the phase bridge plus
    `|m| ≤ δ·pq/2` (from `hm`) gives `|H_{pq}|/(pq) ≥ δ/2`, hence the squared
    term `≥ δ²/4`; summing `≥ (|P|/2)(δ²/4) = |P|³/(2¹³X²)`.
-/
lemma crt_energy_lower_bound_for_fixed_outer_prime (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X) (hNk : 12 ≤ P.card)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (m m' : ℤ) (hqd : ¬ (q : ℤ) ∣ (m' - m))
    (hm : (32 : ℤ) * |m| ≤ (X : ℤ) * P.card) :
    (P.card : ℝ) ^ 3 / (2 ^ 13 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 := by
  set pinv : ℕ → ℕ := fun p => ((p : ZMod q)⁻¹).val;
  -- By adjacent_scale_small_phase_count, at least P.card/2 of the p have (norm ∘ ((↑) : ℝ → UnitAddCircle))((m'-m)·p̄/q) > δ = P.card/(32X).
  have h_residue_count : ((P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X))).card : ℝ) ≥ (P.card : ℝ) / 2 := by
    have h_residue_count : ((P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ) ≤ (P.card : ℝ) / 4 + 1 := by
      convert adjacent_scale_small_phase_count X hX P hP q hq hqlb hqub (m' - m) hqd pinv _ using 1;
      intro p hp; haveI := Fact.mk hq; simp +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      simp +zetaDelta at *;
      rw [ mul_inv_cancel₀ ] ; exact by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( hP p hp |>.1 ) ) ( by linarith [ hP p hp |>.2 ] ) ;
    have h_residue_count : ((P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X))).card : ℝ) = (P.card : ℝ) - ((P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ) := by
      rw [ eq_sub_iff_add_eq, ← Nat.cast_add, ← Finset.card_union_of_disjoint ];
      · congr with p ; by_cases hp : (norm ∘ ((↑) : ℝ → UnitAddCircle)) ( ( m' - m : ℤ ) * ( pinv p : ℝ ) / q ) ≤ ( P.card : ℝ ) / ( 32 * X ) <;> aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith [ show ( P.card : ℝ ) ≥ 12 by norm_cast ];
  -- For each p in the set where (norm ∘ ((↑) : ℝ → UnitAddCircle))((m'-m)·p̄/q) > δ, we have |H p|/(pq) ≥ δ/2.
  have h_phase_bound : ∀ p ∈ P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X)), |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) ≥ (P.card : ℝ) / (64 * X) := by
    intro p hp
    have h_phase : (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) + |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
      convert crt_representative_controls_reciprocal_phase p q ( hP p ( Finset.filter_subset _ _ hp ) |>.1 ) hq ( by
        linarith [ hP p ( Finset.filter_subset _ _ hp ) ] ) m m' ( pinv p ) ( by
        haveI := Fact.mk hq; simp +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
        simp +zetaDelta at *;
        rw [ mul_inv_cancel₀ ] ; norm_num [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( hP p hp.1 |>.1 ) ) ( by linarith [ hP p hp.1 |>.2.2 ] ) ) using 1;
    have h_abs_m : |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) ≤ (P.card : ℝ) / (64 * X) := by
      rw [ div_le_div_iff₀ ] <;> norm_cast at * <;> try nlinarith;
      · norm_num at *;
        nlinarith [ abs_nonneg m, show ( p : ℤ ) * q ≥ 2 * X ^ 2 by norm_cast; nlinarith [ hP p hp.1 ] ];
      · exact mul_pos ( Nat.Prime.pos ( hP p ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ) hq.pos;
    norm_num at *;
    ring_nf at *; linarith;
  -- Therefore, $\sum_{p \in P} \left(\frac{H_{pq}}{pq}\right)^2 \geq \sum_{p \in S} \left(\frac{\delta}{2}\right)^2$.
  have h_sum_bound : ∑ p ∈ P, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * (q : ℝ))) ^ 2 ≥ ∑ p ∈ P.filter (fun p => (norm ∘ ((↑) : ℝ → UnitAddCircle)) ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X)), ((P.card : ℝ) / (64 * X)) ^ 2 := by
    refine' le_trans ( Finset.sum_le_sum fun p hp => pow_le_pow_left₀ ( by positivity ) ( h_phase_bound p hp ) 2 ) _;
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _ ) _;
    norm_num [ div_pow, abs_div, abs_mul, abs_of_nonneg, Nat.cast_nonneg ];
  refine le_trans ?_ h_sum_bound ; norm_num at *;
  convert mul_le_mul_of_nonneg_right h_residue_count ( show ( 0 : ℝ ) ≤ ( #P : ℝ ) ^ 2 / ( 64 * X ) ^ 2 by positivity ) using 1 ; ring;
  rw [ div_pow ]

end LocalEnergy

end
