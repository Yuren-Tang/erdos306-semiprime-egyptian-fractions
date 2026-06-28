/-
# Cross-block energy

Deterministic reciprocal-phase dispersion and the energy penalty forced by a
label mismatch between consecutive prime blocks.
-/
import RequestProject.GlobalControl.Basic

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ## G2. Cross-block dispersion (note 34 G2)

The deterministic dispersion engine, one level up.  Because the window `[X,2X)`
has length `≤ q/2`, each residue class mod `q` meets it in at most one prime, so
the "fiber ≤ 1" form of `lemmaD` applies directly. -/

/-
**Phase lower bound.**  If `q ∤ n` then the distance from `n/q` to the
    nearest integer is at least `1/q` (the numerator is a nonzero residue).
-/
lemma nndist1_ratio_ge (q : ℕ) (hq0 : 0 < q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    1 / (q : ℝ) ≤ nndist1 ((n : ℝ) / (q : ℝ)) := by
  -- Let $k = \text{round}(n/q)$, then $n - kq \neq 0$ since $q \nmid n$.
  set k := round ((n : ℝ) / q)
  have hk_ne_zero : n - k * q ≠ 0 := by
    exact fun h => hn <| ⟨ k, by linarith ⟩;
  -- Since $|n - kq| \geq 1$, we have $|(n : ℝ) / q - k| \geq 1 / q$.
  have h_abs : |(n : ℝ) / q - k| ≥ 1 / q := by
    rw [ div_sub', abs_div ] <;> norm_cast;
    · simp +decide [Rat.divInt_eq_div];
      exact le_mul_of_one_le_left ( by positivity ) ( mod_cast abs_pos.mpr ( show ( n - q * k : ℤ ) ≠ 0 from by simpa [ mul_comm ] using hk_ne_zero ) );
    · linarith;
  exact h_abs

/-
**G2 residue count** (the `dispersion_residue_count` analog, fiber ≤ 1).
    The number of `p ∈ P` whose reciprocal phase `‖d·p̄/q‖` is `≤ δ := |P|/(32X)`
    is at most `|P|/4 + 1`.
-/
lemma crossblock_residue_count (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    ((P.filter (fun p =>
        nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ)
      ≤ (P.card : ℝ) / 4 + 1 := by
  -- Set δ := (P.card : ℝ)/(32*X).
  set δ := (P.card : ℝ) / (32 * X);
  -- Step 1 (witness): If p ∈ P and nndist1((d:ℝ)*(pinv p:ℝ)/q) ≤ δ, then there is an integer u with |u| ≤ δ*q and (q:ℤ) ∣ (d * pinv p - u).
  have h_witness : ∀ p ∈ P, nndist1 ((d : ℝ) * (pinv p : ℝ) / q) ≤ δ → ∃ u : ℤ, |u| ≤ δ * q ∧ (q : ℤ) ∣ (d - u * p) := by
    intro p hp hδ
    obtain ⟨u, hu⟩ : ∃ u : ℤ, |u| ≤ δ * q ∧ (q : ℤ) ∣ (d * pinv p - u) := by
      refine' ⟨ d * pinv p - round ( ( d : ℝ ) * pinv p / q ) * q, _, _ ⟩ <;> norm_num [ nndist1 ] at *;
      convert mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg q) using 1 <;> try rfl
      rw [div_sub', abs_div] <;> norm_num [hq.ne_zero]
      ring_nf
    have h_div : (q : ℤ) ∣ (p * pinv p - 1) := by
      exact ⟨ p * pinv p / q - 1 / q, by linarith [ Nat.mod_add_div ( p * pinv p ) q, Nat.mod_add_div 1 q, hpinv p hp ] ⟩;
    exact ⟨ u, hu.1, by convert hu.2.mul_left p |> Int.dvd_sub <| h_div.mul_left d using 1; ring ⟩;
  -- Step 3 (cover): The filtered set is contained in the union over integers u ∈ Icc (-m) m (where m := ⌊δ*q⌋ ≥ 0) of {p ∈ P : (q:ℤ) ∣ (d - u*p)}.
  have h_cover : {p ∈ P | nndist1 ((d : ℝ) * (pinv p : ℝ) / q) ≤ δ} ⊆ Finset.biUnion (Finset.Icc (-⌊δ * q⌋) ⌊δ * q⌋) (fun u => {p ∈ P | (q : ℤ) ∣ (d - u * p)}) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨u, hu_abs, hu_dvd⟩ := h_witness p hp.1 hp.2
    rw [Finset.mem_biUnion]
    refine ⟨u, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_filter.mpr ⟨hp.1, hu_dvd⟩⟩
    · exact Int.le_of_lt_add_one <| by
        rw [← @Int.cast_lt ℝ]
        push_cast
        rw [Int.cast_abs] at hu_abs
        have hu_lower : -(δ * q) ≤ (u : ℝ) :=
          (neg_le_neg hu_abs).trans (neg_abs_le (u : ℝ))
        linarith [Int.floor_le (δ * q), Int.lt_floor_add_one (δ * q)]
    · exact Int.le_floor.mpr <| by
        rw [Int.cast_abs] at hu_abs
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
      have := Int.Prime.dvd_mul' hq h_eq
      simp_all +decide
      obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith [ hP p hp, hP p' hp' ] ] ;
    exact Finset.card_le_one.mpr fun p hp q hq => h_fiber p q ( Finset.mem_filter.mp hp |>.1 ) ( Finset.mem_filter.mp hq |>.1 ) ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_filter.mp hq |>.2 );
  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_cover ) _;
  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun u hu => h_fiber u ) _ ; norm_num;
  have h_floor : ⌊δ * q⌋ ≤ (P.card : ℝ) / 8 := by
    refine' le_trans ( Int.floor_le _ ) _;
    rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
  rw [ div_add_one, le_div_iff₀ ] at * <;> norm_cast at *;
  linarith [ Int.toNat_of_nonneg ( by linarith [ show ⌊δ * q⌋ ≥ 0 by exact Int.floor_nonneg.mpr ( by positivity ) ] : 0 ≤ ⌊δ * q⌋ + 1 + ⌊δ * q⌋ ) ]

/-
**G2 (cross-block dispersion).**  For `P ⊆ primes ∩ [X, 2X)`, a prime
    `q ∈ [2X, 4X)`, and `q ∤ d`, the reciprocal-phase energy
    `∑_{p∈P} ‖d·p⁻¹/q‖²` is bounded below by `|P|³/(2¹¹X²)`.

    `pinv p` denotes the inverse of `p` modulo `q` (as an integer in `[0,q)`).

    **Status**: proved deterministically by the `lemmaD` pattern, with fiber
    size at most one (interval length at most half the modulus).
-/
theorem crossblock_dispersion (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    (P.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ^ 2 := by
  by_cases hP_card : P.card ≤ 11;
  · -- For each p ∈ P, nndist1((d:ℝ)*(pinv p:ℝ)/q) ≥ 1/q.
    have h_term_ge : ∀ p ∈ P, (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ))) ^ 2 ≥ (1 / (q : ℝ)) ^ 2 := by
      intro p hp
      have h_not_div : ¬(q : ℤ) ∣ (d * pinv p) := by
        haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
        intro H; specialize hpinv p hp; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      gcongr;
      simpa only [Int.cast_mul, Int.cast_natCast] using
        nndist1_ratio_ge q (Nat.Prime.pos hq) (d * pinv p) h_not_div
    refine le_trans ?_ ( Finset.sum_le_sum h_term_ge ) ; norm_num;
    field_simp;
    rw [ le_div_iff₀ ] <;> norm_cast <;> try nlinarith only [ hqlb, hqub, hX ] ;
    nlinarith [ Nat.pow_le_pow_left hP_card 2, Nat.pow_le_pow_left hqlb 2, Nat.pow_le_pow_left hqub.le 2, Nat.mul_le_mul_left ( #P ) ( show #P ^ 2 ≤ 121 by nlinarith only [ hP_card ] ) ];
  · -- By crossblock_residue_count, the number of p ∈ P with nndist1(...) ≤ δ is ≤ P.card/4 + 1.
    set δ := (P.card : ℝ) / (32 * X)
    have h_residue_count : ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ δ)).card : ℝ) ≤ P.card / 4 + 1 := by
      convert crossblock_residue_count X hX P hP q hq hqlb hqub d hqd pinv hpinv using 1;
    -- For each p ∈ S, term p = nndist1(...)² > δ².
    have h_term_bound : ∀ p ∈ P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ), (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2 ≥ δ^2 := by
      exact fun p hp => pow_le_pow_left₀ ( by positivity ) ( Finset.mem_filter.mp hp |>.2.le ) 2;
    -- Therefore, ∑ p ∈ P term p ≥ ∑ p ∈ S term p ≥ S.card * δ².
    have h_sum_bound : (∑ p ∈ P, (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2) ≥ ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) * δ^2 := by
      have h_sum_bound : (∑ p ∈ P, (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2) ≥ (∑ p ∈ P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ), (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _;
      exact le_trans ( by simpa using Finset.sum_le_sum h_term_bound ) h_sum_bound;
    -- Since $S.card \geq P.card / 2$, we have $S.card * δ^2 \geq (P.card / 2) * δ^2$.
    have h_card_bound : ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) ≥ (P.card : ℝ) / 2 := by
      have h_card_bound : ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) + ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ δ)).card : ℝ) = P.card := by
        rw_mod_cast [ Finset.card_filter, Finset.card_filter ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones P ▸ by congr; ext; split_ifs <;> linarith;
      linarith [ show ( P.card : ℝ ) ≥ 12 by norm_cast; linarith ];
    calc
      (P.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) =
          (P.card : ℝ) / 2 * δ ^ 2 := by
        dsimp [δ]
        ring
      _ ≤ ((P.filter (fun p => nndist1
          ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) * δ ^ 2 :=
        mul_le_mul_of_nonneg_right h_card_bound (sq_nonneg _)
      _ ≤ ∑ p ∈ P, nndist1
          ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ^ 2 := h_sum_bound

/-! ## G3. Mismatch penalty (note 34 G3)

**Faithfulness finding (the original statement is FALSE).**  The mismatch penalty
as first stated (kept below, commented out) omits the cold-label size hypotheses
`|m_j| ≤ X_j^{7/4}` of note 34 G3.  Without them it is false: take `m :=`
`∏_{p∈P k} p` and `m' := 0`.  Then `m ≠ m'`, while for every `p ∈ P k`,
`(m : ZMod p) = 0` and for every `q ∈ P (k+1)`, `(m' : ZMod q) = 0`, so every
control representative is `Hglob a p q = crtRepr p q 0 0 = 0` (verified) and the
bipartite energy is `0`, strictly below the positive left-hand side.

The corrected statement restores faithful label-size hypotheses (`hm`, `hm'`,
implied by note 34's L3 cold-label bound) plus block-density regularity used by
the dispersion count (`hNk`, `hNk1`, implied by `BS.hdensity` for large `k`).
-/

/-
The nearest-integer distance never exceeds the absolute value (`round` is
    nearest, so `|x - round x| ≤ |x - 0|`).
-/
lemma nndist1_le_abs (x : ℝ) : nndist1 x ≤ |x| := by
  unfold nndist1
  calc
    |x - (round x : ℝ)| ≤ |x - ((0 : ℤ) : ℝ)| := round_le x 0
    _ = |x| := by norm_num

/-
`nndist1` is invariant under integer translation.
-/
lemma nndist1_add_intCast (x : ℝ) (n : ℤ) : nndist1 (x + (n : ℝ)) = nndist1 x := by
  unfold nndist1; rw [ round_add_intCast ] ; ring_nf;
  grind +revert

/-
**G3 phase bridge** (modulus `q`).  For distinct primes `p ≠ q`, an inverse
    `pinv` of `p` mod `q`, and `H := crtRepr p q (m mod p) (m' mod q)`, the
    reciprocal phase `‖(m'-m)·p̄/q‖` is controlled by `|H|/(pq) + |m|/(pq)`.

    Proof: `H ≡ m (mod p)` so `v := (H-m)/p ∈ ℤ`; `v·p ≡ m'-m (mod q)` with
    `p·pinv ≡ 1` give `v ≡ (m'-m)·pinv (mod q)`, so
    `nndist1((m'-m)·pinv/q) = nndist1(v/q) ≤ |v|/q = |H-m|/(pq) ≤ (|H|+|m|)/(pq)`.
-/
lemma crossblock_phase_bridge (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m m' : ℤ) (pinv : ℕ) (hpinv : (p * pinv) % q = 1 % q) :
    nndist1 (((m' - m : ℤ) : ℝ) * (pinv : ℝ) / (q : ℝ))
      ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ))
        + |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
  have h_coprime : Nat.Coprime p q := by
    simpa [ hpq ] using Nat.coprime_primes hp hq;
  obtain ⟨v, hv⟩ : ∃ v : ℤ, (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) - m = p * v := by
    have h_cong : (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) ≡ m [ZMOD p] := by
      have := crtRepr_congr_left p q ( m : ZMod p ) ( m' : ZMod q ) h_coprime hp.pos hq.pos; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    exact h_cong.symm.dvd;
  have h_div : (q : ℤ) ∣ ((m' - m) * pinv - v) := by
    have h_div : (q : ℤ) ∣ (p * v - (m' - m)) := by
      have h_div : (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) ≡ m' [ZMOD q] := by
        convert crtRepr_congr_right p q ( m : ZMod p ) ( m' : ZMod q ) h_coprime hp.pos hq.pos using 1;
        norm_num [ ← ZMod.intCast_eq_intCast_iff ];
      convert h_div.symm.dvd using 1 ; linarith;
    have h_div : (q : ℤ) ∣ (p * pinv - 1) := by
      exact ⟨ p * pinv / q - 1 / q, by linarith [ Nat.mod_add_div ( p * pinv ) q, Nat.mod_add_div 1 q ] ⟩;
    rw [show (m' - m) * (pinv : ℤ) - v =
        (p * pinv - 1) * v - (p * v - (m' - m)) * pinv by ring]
    exact dvd_sub (h_div.mul_right v)
      (‹(q : ℤ) ∣ p * v - (m' - m)›.mul_right pinv)
  have h_nndist : nndist1 ((m' - m : ℤ) * pinv / (q : ℝ)) = nndist1 ((v : ℝ) / (q : ℝ)) := by
    obtain ⟨ k, hk ⟩ := h_div;
    convert nndist1_add_intCast ( v / q : ℝ ) k using 1;
    exact congr_arg _ ( by rw [ div_add', div_eq_div_iff ] <;> norm_cast <;> nlinarith [ hq.two_le ] );
  have h_abs : |(v : ℝ) / (q : ℝ)| ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) - m| / (p * q) := by
    rw [ show ( crtRepr p q m m' : ℝ ) - m = p * v by exact_mod_cast hv ] ; norm_num [ abs_div, abs_mul, hp.ne_zero, hq.ne_zero ] ; ring_nf ;
    norm_num [ hp.ne_zero ];
  have h_abs : |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) - m| ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| + |(m : ℝ)| := by
    exact abs_sub _ _;
  exact h_nndist.symm ▸ le_trans ( nndist1_le_abs _ ) ( by convert le_trans ‹_› ( div_le_div_of_nonneg_right h_abs ( by positivity ) ) using 1 ; ring )

/-
**G3 per-vertex bound.**  For a single good prime `q ∈ [2X,4X)` (with
    `q ∤ m'-m`), the cross energy over `P ⊆ primes ∩ [X,2X)` against `q` is at
    least `|P|³/(2¹³X²)`.

    Proof: by `crossblock_residue_count` at least `|P|/2` of the `p` have
    `‖(m'-m)·p̄/q‖ > δ = |P|/(32X)`; for each the phase bridge plus
    `|m| ≤ δ·pq/2` (from `hm`) gives `|H_{pq}|/(pq) ≥ δ/2`, hence the squared
    term `≥ δ²/4`; summing `≥ (|P|/2)(δ²/4) = |P|³/(2¹³X²)`.
-/
lemma mismatch_per_q (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X) (hNk : 12 ≤ P.card)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (m m' : ℤ) (hqd : ¬ (q : ℤ) ∣ (m' - m))
    (hm : (32 : ℤ) * |m| ≤ (X : ℤ) * P.card) :
    (P.card : ℝ) ^ 3 / (2 ^ 13 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 := by
  set pinv : ℕ → ℕ := fun p => ((p : ZMod q)⁻¹).val;
  -- By crossblock_residue_count, at least P.card/2 of the p have nndist1((m'-m)·p̄/q) > δ = P.card/(32X).
  have h_residue_count : ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X))).card : ℝ) ≥ (P.card : ℝ) / 2 := by
    have h_residue_count : ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ) ≤ (P.card : ℝ) / 4 + 1 := by
      convert crossblock_residue_count X hX P hP q hq hqlb hqub (m' - m) hqd pinv _ using 1;
      intro p hp; haveI := Fact.mk hq; simp +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      simp +zetaDelta at *;
      rw [ mul_inv_cancel₀ ] ; exact by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( hP p hp |>.1 ) ) ( by linarith [ hP p hp |>.2 ] ) ;
    have h_residue_count : ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X))).card : ℝ) = (P.card : ℝ) - ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ) := by
      rw [ eq_sub_iff_add_eq, ← Nat.cast_add, ← Finset.card_union_of_disjoint ];
      · congr with p ; by_cases hp : nndist1 ( ( m' - m : ℤ ) * ( pinv p : ℝ ) / q ) ≤ ( P.card : ℝ ) / ( 32 * X ) <;> aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith [ show ( P.card : ℝ ) ≥ 12 by norm_cast ];
  -- For each p in the set where nndist1((m'-m)·p̄/q) > δ, we have |H p|/(pq) ≥ δ/2.
  have h_phase_bound : ∀ p ∈ P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X)), |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) ≥ (P.card : ℝ) / (64 * X) := by
    intro p hp
    have h_phase : nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) + |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
      convert crossblock_phase_bridge p q ( hP p ( Finset.filter_subset _ _ hp ) |>.1 ) hq ( by
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
  have h_sum_bound : ∑ p ∈ P, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * (q : ℝ))) ^ 2 ≥ ∑ p ∈ P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X)), ((P.card : ℝ) / (64 * X)) ^ 2 := by
    refine' le_trans ( Finset.sum_le_sum fun p hp => pow_le_pow_left₀ ( by positivity ) ( h_phase_bound p hp ) 2 ) _;
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _ ) _;
    norm_num [ div_pow, abs_div, abs_mul, abs_of_nonneg, Nat.cast_nonneg ];
  refine le_trans ?_ h_sum_bound ; norm_num at *;
  convert mul_le_mul_of_nonneg_right h_residue_count ( show ( 0 : ℝ ) ≤ ( #P : ℝ ) ^ 2 / ( 64 * X ) ^ 2 by positivity ) using 1 ; ring;
  rw [ div_pow ]

/-
**G3 (mismatch penalty), corrected.**  Two consecutive blocks with *distinct*
    labels `m ≠ m'` contribute bipartite control energy at least
    `Πₖ = N_{k+1}·Nₖ³/(2¹⁶·Xₖ²)`.

    The original statement was false because it omitted these hypotheses:
    `hm`/`hm'` are the cold-label size bounds of note 34 G3 (L3), and
    `hNk`/`hNk1` are the block-density regularity used by the dispersion count.

    **Status**: proved from `mismatch_per_q`, summed over the
    `≥ N_{k+1}/2` good vertices `q ∤ m'-m`.
-/
set_option maxHeartbeats 1000000 in
theorem mismatch_penalty (BS : BlockSystem) (a : (p : ℕ) → ZMod p) (k : ℕ)
    (_hk1 : BS.k0 ≤ k) (_hk2 : k < BS.K)
    (m m' : ℤ) (hmm : m ≠ m')
    (hlabel : (∀ p ∈ BS.P k, (a p : ZMod p) = (m : ZMod p)) ∧
              (∀ q ∈ BS.P (k + 1), (a q : ZMod q) = (m' : ZMod q)))
    (hNk : 12 ≤ (BS.P k).card) (hNk1 : 2 ≤ (BS.P (k + 1)).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    ((BS.P (k + 1)).card : ℝ) * ((BS.P k).card : ℝ) ^ 3 /
        (2 ^ 16 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  -- By definition of $P_k$ and $P_{k+1}$, we know that $P_k \subseteq \{2^k, 2^k + 1, \ldots, 2^{k+1} - 1\}$ and $P_{k+1} \subseteq \{2^{k+1}, 2^{k+1} + 1, \ldots, 2^{k+2} - 1\}$.
  have hP_k_subset : BS.P k ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
    exact fun p hp => Finset.mem_Ico.mpr <| BS.hwindow k p hp
  have hP_k1_subset : BS.P (k + 1) ⊆ Finset.Ico (2 ^ (k + 1)) (2 ^ (k + 2)) := by
    exact fun p hp => Finset.mem_Ico.mpr <| BS.hwindow _ _ hp;
  have h_good_set : ∃ Q : Finset ℕ, Q ⊆ BS.P (k + 1) ∧ Q.card ≥ (BS.P (k + 1)).card / 2 ∧ ∀ q ∈ Q, ¬(q : ℤ) ∣ (m' - m) := by
    have h_bad_set : (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card ≤ 1 := by
      have h_pair : ∀ q q' : ℕ, q ∈ BS.P (k + 1) → q' ∈ BS.P (k + 1) → q ≠ q' → ¬((q : ℤ) ∣ (m' - m)) ∨ ¬((q' : ℤ) ∣ (m' - m)) := by
        intros q q' hq hq' hneq
        by_contra h_contra
        push Not at h_contra
        have h_div : (q * q' : ℤ) ∣ (m' - m) := by
          convert Int.coe_lcm_dvd h_contra.1 h_contra.2 using 1;
          exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( BS.hprime ( k + 1 ) q hq ) ( BS.hprime ( k + 1 ) q' hq' ) ; aesop )
        have h_abs : |m' - m| ≥ (q * q' : ℤ) := by
          exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( Ne.symm hmm ) ) ) ( by simpa )
        have h_abs_le : |m' - m| ≤ |m| + |m'| := by
          cases abs_cases ( m' - m ) <;> cases abs_cases m <;> cases abs_cases m' <;> linarith
        have h_abs_le' : |m| + |m'| < (q * q' : ℤ) := by
          have h_abs_le' : (BS.P k).card ≤ 2 ^ k ∧ (BS.P (k + 1)).card ≤ 2 ^ (k + 1) := by
            have := Finset.card_le_card hP_k_subset; have := Finset.card_le_card hP_k1_subset; simp_all +decide [ pow_succ' ] ;
            exact ⟨ by omega, by omega ⟩;
          have h_abs_le' : (q : ℤ) ≥ 2 ^ (k + 1) ∧ (q' : ℤ) ≥ 2 ^ (k + 1) := by
            exact ⟨ mod_cast Finset.mem_Ico.mp ( hP_k1_subset hq ) |>.1, mod_cast Finset.mem_Ico.mp ( hP_k1_subset hq' ) |>.1 ⟩;
          norm_num [ pow_succ' ] at *;
          nlinarith [ pow_pos ( zero_lt_two' ℤ ) k, Int.mul_ediv_add_emod ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) 32, Int.emod_nonneg ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) ( by norm_num : ( 32 : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) ( by norm_num : ( 32 : ℤ ) > 0 ) ]
        linarith [h_abs, h_abs_le, h_abs_le'];
      refine Finset.card_le_one.mpr ?_
      intro q hq q' hq'
      by_contra hne
      rcases h_pair q q' (Finset.mem_filter.mp hq).1
          (Finset.mem_filter.mp hq').1 hne with hq_bad | hq'_bad
      · exact hq_bad (Finset.mem_filter.mp hq).2
      · exact hq'_bad (Finset.mem_filter.mp hq').2
    have h_good_set : (Finset.filter (fun q : ℕ => ¬(q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card = (BS.P (k + 1)).card - (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card := by
      have h_partition := Finset.card_filter_add_card_filter_not
        (s := BS.P (k + 1)) (fun q : ℕ => (q : ℤ) ∣ (m' - m))
      omega
    simp_all +decide
    grind +qlia;
  obtain ⟨ Q, hQ₁, hQ₂, hQ₃ ⟩ := h_good_set;
  have h_sum_bound : ∑ pq ∈ bipartitePairs BS k, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 ≥ ∑ q ∈ Q, ∑ p ∈ BS.P k, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 := by
    have h_sum_bound : ∑ pq ∈ bipartitePairs BS k, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 ≥ ∑ pq ∈ (BS.P k) ×ˢ Q, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.product_subset_product ( Finset.Subset.refl _ ) hQ₁ ) fun _ _ _ => sq_nonneg _;
    convert h_sum_bound using 1;
    rw [ Finset.sum_product, Finset.sum_comm ];
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [ Hglob, hlabel.1 x hx, hlabel.2 y ( hQ₁ hy ) ] ;
  have h_sum_bound : ∑ q ∈ Q, ∑ p ∈ BS.P k, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 ≥ ∑ q ∈ Q, ((BS.P k).card : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2) := by
    apply Finset.sum_le_sum;
    intro q hq;
    convert mismatch_per_q ( 2 ^ k ) ( by positivity ) ( BS.P k ) ( fun p hp => ?_ ) hNk q ( ?_ ) ( ?_ ) ( ?_ ) m m' ( ?_ ) ( ?_ ) using 1;
    all_goals norm_cast;
    any_goals tauto;
    · exact ⟨ BS.hprime k p hp, by linarith [ Finset.mem_Ico.mp ( hP_k_subset hp ) ], by linarith [ Finset.mem_Ico.mp ( hP_k_subset hp ), pow_succ' 2 k ] ⟩;
    · exact BS.hprime _ _ ( hQ₁ hq );
    · have := hP_k1_subset ( hQ₁ hq ) ; norm_num [ pow_succ' ] at * ; linarith;
    · have := hP_k1_subset ( hQ₁ hq ) ; norm_num [ pow_succ' ] at * ; linarith;
  refine le_trans ?_ ( le_trans h_sum_bound ‹_› );
  norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  field_simp;
  norm_cast ; linarith [ Nat.div_add_mod ( BS.P ( k + 1 ) |> Finset.card ) 2, Nat.mod_lt ( BS.P ( k + 1 ) |> Finset.card ) two_pos ]

/-
**G3 (mismatch penalty) with exceptions** (note 36 §0).  The cold blocks of the
    global level-set argument carry a *bounded* exception set `Eₖ` of vertices
    where the dominant label fails.  Reusing `mismatch_per_q` over the reduced
    sets `Pₖ \ Eₖ` and `Pₖ₊₁ \ Eₖ₊₁` gives the same bipartite penalty with the
    reduced cardinalities.  The no-exception `mismatch_penalty` is the special
    case `Eₖ = Eₖ₊₁ = ∅`.

    Proof: identical to `mismatch_penalty`, with `Pₖ` replaced by `Pₖ \ Eₖ` (the
    dispersion vertex set) and the "good" outer vertices drawn from
    `Pₖ₊₁ \ Eₖ₊₁`; at most one of those divides `m'-m`, so at least
    `(Pₖ₊₁ \ Eₖ₊₁).card - 1` are good.

    (The hypothesis `hEk1 : Eₖ₊₁ ⊆ Pₖ₊₁` is part of note 36's requested
    interface; the finished proof does not actually use it.)
-/
set_option maxHeartbeats 1000000 in
theorem mismatch_penalty_with_exceptions (BS : BlockSystem)
    (a : (p : ℕ) → ZMod p) (k : ℕ)
    (m m' : ℤ) (hmm : m ≠ m')
    (Ek Ek1 : Finset ℕ) (hEk : Ek ⊆ BS.P k) (_hEk1 : Ek1 ⊆ BS.P (k + 1))
    (hlabel_k : ∀ p ∈ BS.P k \ Ek, (a p : ZMod p) = (m : ZMod p))
    (hlabel_k1 : ∀ q ∈ BS.P (k + 1) \ Ek1, (a q : ZMod q) = (m' : ZMod q))
    (hNk : 12 ≤ (BS.P k \ Ek).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k \ Ek).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    (((BS.P (k + 1) \ Ek1).card : ℝ) - 1) * ((BS.P k \ Ek).card : ℝ) ^ 3 /
        (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
  rotate_left;
  exact Finset.biUnion ( BS.P ( k + 1 ) \ Ek1 ) fun q => Finset.image ( fun p => ( p, q ) ) ( BS.P k \ Ek ) |> Finset.filter fun pq => ¬ ( q : ℤ ) ∣ ( m' - m );
  · simp +decide [ Finset.subset_iff, bipartitePairs ];
    grind;
  · exact fun _ _ _ => sq_nonneg _;
  · rw [ Finset.sum_biUnion ];
    · refine' le_trans _ ( Finset.sum_le_sum fun q hq => _ );
      rotate_left;
      use fun q => if ¬ ( q : ℤ ) ∣ m' - m then ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) else 0;
      · split_ifs <;> simp_all +decide [ Finset.sum_image ];
        rw [ ← Finset.sum_sdiff hEk ];
        have := mismatch_per_q ( 2 ^ k ) ( by positivity ) ( BS.P k \ Ek ) ?_ ?_ q ?_ ?_ ?_ m m' ?_ ?_ <;> norm_num at *;
        any_goals assumption;
        · convert this using 2
          all_goals try rfl
          unfold Hglob
          aesop
        · exact fun p hp hp' => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
        · exact BS.hprime _ _ hq.1;
        · have := BS.hwindow ( k + 1 ) q hq.1; norm_num [ pow_succ' ] at *; linarith;
        · have := BS.hwindow ( k + 1 ) q hq.1; norm_num [ pow_succ' ] at *; linarith;
      · have h_card : (Finset.filter (fun q : ℕ => ¬(q : ℤ) ∣ (m' - m)) (BS.P (k + 1) \ Ek1)).card ≥ (BS.P (k + 1) \ Ek1).card - 1 := by
          have hQ_card : (Finset.filter (fun q : ℕ => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1) \ Ek1)).card ≤ 1 := by
            have h_good_outer : ∀ q ∈ (BS.P (k + 1)) \ Ek1, ∀ q' ∈ (BS.P (k + 1)) \ Ek1, q ≠ q' → ¬((q : ℤ) ∣ (m' - m) ∧ (q' : ℤ) ∣ (m' - m)) := by
              intros q hq q' hq' hneq hdiv
              have hprod : (q * q' : ℤ) ∣ (m' - m) := by
                convert Int.coe_lcm_dvd hdiv.1 hdiv.2 using 1;
                exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( BS.hprime ( k + 1 ) q <| Finset.mem_sdiff.mp hq |>.1 ) ( BS.hprime ( k + 1 ) q' <| Finset.mem_sdiff.mp hq' |>.1 ) ; aesop );
              have hprod_le : (q * q' : ℤ) ≤ |m' - m| := by
                exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr hmm.symm ) ) ( by simpa );
              have hprod_ge : (q * q' : ℤ) ≥ 2 ^ (2 * k + 2) := by
                have hprod_ge : (q : ℤ) ≥ 2 ^ (k + 1) ∧ (q' : ℤ) ≥ 2 ^ (k + 1) := by
                  exact ⟨ mod_cast BS.hwindow ( k + 1 ) q ( Finset.mem_sdiff.mp hq |>.1 ) |>.1, mod_cast BS.hwindow ( k + 1 ) q' ( Finset.mem_sdiff.mp hq' |>.1 ) |>.1 ⟩;
                exact le_trans ( by ring_nf; norm_num ) ( mul_le_mul hprod_ge.1 hprod_ge.2 ( by positivity ) ( by positivity ) );
              have hprod_le : (BS.P k \ Ek).card ≤ 2 ^ k ∧ (BS.P (k + 1)).card ≤ 2 ^ (k + 1) := by
                have hprod_le : ∀ k, (BS.P k).card ≤ 2 ^ k := by
                  intros k
                  have hprod_le : (BS.P k).card ≤ Finset.card (Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
                    exact Finset.card_le_card fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx;
                  exact hprod_le.trans ( by norm_num [ pow_succ' ] ; linarith );
                exact ⟨ le_trans ( Finset.card_le_card ( Finset.sdiff_subset ) ) ( hprod_le k ), hprod_le ( k + 1 ) ⟩;
              norm_num [ pow_add, pow_mul' ] at *;
              nlinarith [ abs_sub m' m, pow_pos ( zero_lt_two' ℤ ) k ];
            refine Finset.card_le_one.mpr ?_
            intro q hq q' hq'
            by_contra hne
            exact h_good_outer q (Finset.mem_filter.mp hq).1 q'
              (Finset.mem_filter.mp hq').1 hne
              ⟨(Finset.mem_filter.mp hq).2, (Finset.mem_filter.mp hq').2⟩
          have h_partition := Finset.card_filter_add_card_filter_not
            (s := BS.P (k + 1) \ Ek1) (fun q : ℕ => (q : ℤ) ∣ (m' - m))
          omega
        simp_all +decide [ Finset.sum_ite ];
        convert mul_le_mul_of_nonneg_right ( sub_le_sub_right ( Nat.cast_le.mpr h_card ) 1 ) ( by positivity : 0 ≤ ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) ) using 1 ; ring;
        norm_num [ Finset.filter_image ];
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;

end GlobalControl

end
