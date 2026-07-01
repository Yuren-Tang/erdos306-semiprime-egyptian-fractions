import RequestProject.LocalEnergy.DominantLabel.Counting
import RequestProject.LocalEnergy.DominantLabel.Forcing

/-!
# Cold dominant-label bounds

Below the nondominant energy scale, the forcing and counting branches combine
to control the full level set, the label, and its exceptional coordinates.
-/

open Finset

namespace LocalEnergy

open scoped Classical

/-! ## Low-energy level-set bound

The nondominant energy lower bound makes every assignment below
`c'X/log³X` dominant, where the dominant level-set estimate applies. -/

/-
**Corollary** (`29 §7`).  For `ε > 0` there are `c', X₀` so that for `X ≥ X₀`
    and all `R ≤ c'·X/log³X`,
    `#{a : QP P a ≤ R} ≤ exp(εR)·(1 + 20√R/σ_P)`.

    This directly combines `nondominant_energy_lower_bound` with
    `dominant_level_set_bound`.
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
Two integer labels
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
For a fixed label `m`
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
For a cold block
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
For a *cold* block
    (`R ≤ c₂·X/log³X`) with a dominant label `m`, the label is small:
    `|m| ≤ N·X/16`, uniformly in `X ≥ X0(c₂)`.  This feeds both `fixed_label_level_set_bound`
    / `cold_exception_count_bound` (which require `|m| ≤ N·X/16`) and the `hm`-type
    hypotheses of `GlobalControl.consecutive_block_mismatch_energy_lower_bound`.

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
