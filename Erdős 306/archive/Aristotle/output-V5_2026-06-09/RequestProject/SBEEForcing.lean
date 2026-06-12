/-
# SBEE Forcing: Theorem A (dominant), Lemma E (cross-label energy), Theorem B

This file formalizes **P2** of the SBEE single-block counting proof, following
`29 SBEE Master …md` §3 (Theorem A), §5 (Lemma E), §6 (Theorem B).

It is stated against the faithful CRT energy encoding (`QP`, `sigmaP`,
`BlockAssignment`) of `BlockCRTEnergy.lean`.

## Status overview (the deliverable is the pattern of sorries)

* `IsDominant` — dominance predicate (a label class covers `≥ (1-ρ)·N` primes).
* `lemma_E_cross_label_energy` — **Lemma E.  Fully proved, no sorry.**  Decomposed
  into `lemmaE_fiber` (the per-`q` reduction to `SBEEDispersion.lemmaD`) and
  `lemmaE_close_count` (the total close-pair count via the `≤2`-divisor discard),
  then the `δ = |C|/(64X)` choice and the sum-of-squares energy accounting.
  (A statement bug was fixed first — see the lemma's docstring.)
* `theorem_A_dominant_count` — Theorem A.  `sorry`: combines label uniqueness
  (A1), label range (A2), per-exception energy via Lemma D (A3), the count (A4).
  The entropy bookkeeping (A4) and exception-set encoding remain unformalized.
* `theorem_B_nondominant_forcing` — Theorem B.  `sorry`: the covering construction
  (`29 §4`) + Lemma E + mass accounting force `R ≫ X/log³X`.  The covering
  construction (base-point averaging, short list, class mass accounting) remains
  unformalized.

All reduce, mathematically, to `SBEEDispersion.lemmaD` (proved) plus the
covering/entropy bookkeeping; the remaining gaps (A, B) are exactly the
covering/entropy estimates flagged as the soft spots in the task and note 29 §6,
§9.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEDispersion

open Finset

namespace SBEEForcing

open scoped Classical

/-! ## Dominance -/

/-- `a` is **`m`-dominant** (parameter `ρ`) if the residue label `m` agrees with
    `a_p (mod p)` on at least a `(1-ρ)` fraction of the primes `p ∈ P`, with
    `|m| ≤ X²/2` (so that the in-class CRT representatives equal `m` exactly).
    (`29 §3`.) -/
def IsDominant (X : ℕ) (P : Finset ℕ) (a : BlockAssignment P) (ρ : ℝ) : Prop :=
  ∃ m : ℤ, |m| ≤ (X:ℤ)^2 / 2 ∧
    (1 - ρ) * (P.card : ℝ) ≤
      ((P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))).card : ℝ)

/-! ## Theorem A — the dominant case (`29 §3`) -/

/-- **Theorem A** (`29 §3`).  For `ε > 0`, `ρ ∈ (0, 1/4]`, and `X` large, the
    number of *dominant* low-energy assignments is at most
    `exp(ε R) · (1 + (10/(1-ρ))·√R/σ_P)`.

    Proof ingredients (all in `29 §3`): (A1) the dominant label is unique; (A2) the
    label range `|m| ≤ (5/(1-ρ))·√R/σ_P`; (A3) each exception carries energy
    `≥ N³/2¹⁵X²` via `SBEEDispersion.lemmaD`; (A4) the exception entropy
    `3e log X ≤ εR`.

    **Status**: `sorry` — the entropy bookkeeping (A4) and the per-exception energy
    accounting (A3) over the concrete CRT energy `QP`. -/
theorem theorem_A_dominant_count
    (eps : ℝ) (hε : 0 < eps) (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter
                (fun a : BlockAssignment P => QP P a ≤ R ∧ IsDominant X P a ρ)).card : ℝ)
              ≤ Real.exp (eps * R) *
                  (1 + (10/(1-ρ)) * Real.sqrt R / sigmaP P) := by
  sorry

/-! ## Lemma E — cross-label energy (`29 §5`) -/

set_option maxHeartbeats 1600000 in
open SBEEDispersion in
/-- **Lemma E, per-`q` fiber bound.**  Fix a prime `q ∈ [X,2X]` carrying residue
    `n'`, with `q ∤ (n'-n)`.  The primes `p ∈ C` (residue `n`) whose cross
    representative `H_{pq}` is `δ`-small inject into `lemmaD_set X q U (n'-n)` via
    `p ↦ (u, p)` with `H_{pq} - n = u·p`; hence by `lemmaD` their number is
    `≤ 2·(2·U+1) ≤ 2·(2·(2δX + B/X) + 1)`.

    Here `H_{pq} ≡ n (mod p)` (so `p ∣ H-n`, giving the integer `u`), and
    `H_{pq} ≡ n' (mod q)`, so `u·p = H-n ≡ n'-n (mod q)`; the size bound
    `|u| ≤ δq + |n|/p ≤ 2δX + B/X` uses `|H| ≤ δpq`, `q ≤ 2X`, `X ≤ p`. -/
lemma lemmaE_fiber (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (a : BlockAssignment P) (n n' : ℤ) (B : ℝ) (hB : 0 ≤ B) (hX : 1 ≤ X)
    (C : Finset P)
    (hCp : ∀ p ∈ C, Nat.Prime (p:ℕ) ∧ X ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*X)
    (hCa : ∀ p ∈ C, a p = ((n:ℤ) : ZMod (p:ℕ)))
    (hnB : |(n:ℝ)| ≤ B) (hBX : B ≤ (X:ℝ)^2/4)
    (q : P) (hq : Nat.Prime (q:ℕ)) (hXq : X ≤ (q:ℕ)) (hq2X : (q:ℕ) ≤ 2*X)
    (hqa : a q = ((n':ℤ) : ZMod (q:ℕ)))
    (hqd : ¬ ((q:ℕ):ℤ) ∣ (n' - n))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : δ ≤ 1/4) :
    ((C.filter (fun p : P => |(crtRepr (p:ℕ) (q:ℕ) (a p) (a q) : ℝ)|
        ≤ δ * ((p:ℕ) * (q:ℕ)))).card : ℝ)
      ≤ 2 * (2 * (2*δ*X + B/X) + 1) := by
  have h_filter : ∀ p ∈ C, |(crtRepr p.1 q.1 (a p) (a q) : ℝ)| ≤ δ * (p.1 * q.1) → ∃ u : ℤ, |u| ≤ Nat.floor (2 * δ * X + B / X) ∧ (q : ℤ) ∣ (u * p.1 - (n' - n)) := by
    intro p hp h_abs
    obtain ⟨u, hu⟩ : ∃ u : ℤ, (crtRepr p.val q.val (a p) (a q) : ℤ) - n = u * p.val := by
      have h_div : (crtRepr p.val q.val (a p) (a q) : ZMod p.val) = n := by
        have := crtRepr_congr_left p.1 q.1 ( a p ) ( a q ) ?_ ?_ ?_ <;> simp_all +decide [ Nat.coprime_primes ];
        · rintro rfl; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
        · exact Nat.Prime.pos ( hCp _ _ hp |>.1 );
        · exact hq.pos;
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
        convert crtRepr_congr_right p.val q.val ( a p ) ( a q ) _ _ _ using 1 <;> norm_num [ hqa ];
        · by_cases h : p = q <;> simp_all +decide [ Nat.coprime_primes ];
          simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
        · exact Nat.Prime.pos ( hCp p hp |>.1 );
        · exact hq.pos;
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
  exact_mod_cast SBEEDispersion.lemmaD X q ⌊2 * δ * X + B / X⌋₊ hq hXq ( show ⌊2 * δ * X + B / X⌋₊ < X from Nat.floor_lt' ( by positivity ) |>.2 <| by nlinarith [ show ( X : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ B ( by positivity : ( X : ℝ ) ≠ 0 ) ] ) ( n' - n ) hqd

open SBEEDispersion in
/-- **Lemma E, total close-pair count.**  The number of cross pairs `(p,q) ∈ C×C'`
    whose representative is `δ`-small is `≤ 2|C| + |C'|·2(2(2δX+B/X)+1)`.

    The `≤ 2` primes `q ∈ C'` dividing `d = n'-n` contribute `≤ |C|` pairs each
    (`card_prime_factors_dyadic_le_two`, valid as `0 < |d| ≤ 2B ≤ X²/2 < X³`); each
    remaining `q` has `q ∤ d`, so `lemmaE_fiber` bounds its close fiber. -/
lemma lemmaE_close_count (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
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
    convert SBEEDispersion.card_prime_factors_dyadic_le_two X ( n' - n ) ( sub_ne_zero.mpr ( Ne.symm hd ) ) _ using 1;
    rw [ ← @Int.cast_lt ℝ ] ; norm_num ; cases abs_cases ( n' - n : ℝ ) <;> cases abs_cases ( n : ℝ ) <;> cases abs_cases ( n' : ℝ ) <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ X ) ] ;
  have h_card_bad : (Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C').card ≤ 2 := by
    refine le_trans ?_ h_card_prime_factors;
    have h_image : Finset.image (fun q : P => q.1) (Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C') ⊆ Finset.filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (n' - n)) (Finset.Icc X (2 * X)) := by
      grind;
    exact le_trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ] ) ( Finset.card_mono h_image );
  have h_card_good : ∀ q ∈ C' \ Finset.filter (fun q : P => (q : ℤ) ∣ (n' - n)) C', (Finset.filter (fun p : P => |(crtRepr (p : ℕ) (q : ℕ) (a p) (a q) : ℝ)| ≤ δ * ((p : ℕ) * (q : ℕ))) C).card ≤ 2 * (2 * (2 * δ * X + B / X) + 1) := by
    intros q hq;
    convert lemmaE_fiber X P a n n' B hB hX C hCp hCa hnB hBX q ( hC'p q ( Finset.mem_sdiff.mp hq |>.1 ) |>.1 ) ( hC'p q ( Finset.mem_sdiff.mp hq |>.1 ) |>.2.1 ) ( hC'p q ( Finset.mem_sdiff.mp hq |>.1 ) |>.2.2 ) ( hC'a q ( Finset.mem_sdiff.mp hq |>.1 ) ) ( by aesop ) δ hδ0 hδ4 using 1;
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

    Proof (`29 §5`): reduce to `SBEEDispersion.lemmaD` with `w = n'-n`; at most `2`
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

    **Status**: proved (`c = 1/8192`), via `lemmaE_fiber` + `lemmaE_close_count`,
    the choice `δ = |C|/(64X)`, and the sum-of-squares energy accounting.
-/
theorem lemma_E_cross_label_energy :
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
    -- Count: by `lemmaE_close_count` (with this `δ`), `(Close.card:ℝ) ≤ 2*N + N'*(2*(2*(2*δ*X + B/X)+1))`.
    have h_close_count : (Close.card : ℝ) ≤ 2 * (C.card : ℝ) + (C'.card : ℝ) * (2 * (2 * (2 * δ * X + B / X) + 1)) := by
      convert lemmaE_close_count X P a n n' B ( show 0 ≤ B by linarith [ abs_le.mp hnB ] ) hX hn C C' hCp hC'p hCa hC'a hnB hn'B hBX δ hδ0 hδ4 using 1;
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

/-! ## Theorem B — non-dominant forcing (`29 §6`) -/

/-- **Theorem B** (`29 §6`).  For `ρ ∈ (0,1/4]` and `X` large: any low-energy
    assignment that is **not** dominant forces `R ≫ X/log³X`.  Concretely there is
    `c₂ > 0` with: if `QP P a ≤ R` and `a` is not `ρ`-dominant then
    `R ≥ c₂ · X / (Real.log X)^3`.

    Proof (`29 §6`): the covering construction (`29 §4`) produces `≥ 2` substantial
    classes; Lemma E across them, with the mass accounting (`M₂ ≥ ρN/2`), forces
    `R² ≫ N⁴/(X²log²X)`, i.e. `R ≫ N²/(X log X) ≫ X/log³X`.

    **Status**: `sorry` — the covering bookkeeping and tiny-mass accounting
    (the soft spot flagged in the task), on top of `lemma_E_cross_label_energy`. -/
theorem theorem_B_nondominant_forcing
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (a : BlockAssignment P) (R : ℝ),
          QP P a ≤ R → ¬ IsDominant X P a ρ →
            c2 * (X:ℝ) / (Real.log X)^3 ≤ R := by
  sorry

/-! ## Corollary — SBEE below the window (`29 §7`)

Combining Theorem B (every `R ≤ c'X/log³X` low-energy assignment is dominant) with
Theorem A gives the level-set bound for all `R ≤ c'X/log³X`.  Stated as
`corollary_SBEE_below_window`; `sorry` — it is the direct A+B combination. -/

/-
**Corollary** (`29 §7`).  For `ε > 0` there are `c', X₀` so that for `X ≥ X₀`
    and all `R ≤ c'·X/log³X`,
    `#{a : QP P a ≤ R} ≤ exp(εR)·(1 + 20√R/σ_P)`.

    **Status**: `sorry` — direct combination of `theorem_B_nondominant_forcing`
    (all such assignments are dominant) and `theorem_A_dominant_count`.
-/
theorem corollary_SBEE_below_window
    (eps : ℝ) (hε : 0 < eps) (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (cp X0 : ℝ), 0 < cp ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R → R ≤ cp * (X:ℝ) / (Real.log X)^3 →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ Real.exp (eps * R) * (1 + 20 * Real.sqrt R / sigmaP P) := by
  obtain ⟨X0A, hX0A, HA⟩ := theorem_A_dominant_count eps hε ρ hρ hρ4
  obtain ⟨c2, X0B, hc2, hX0B, HB⟩ := theorem_B_nondominant_forcing ρ hρ hρ4
  use c2 / 2, max X0A X0B;
  refine' ⟨ by positivity, by positivity, fun X hX P hP hN R hR₁ hR₂ => _ ⟩;
  intro hR₃
  have h_dom : ∀ a : BlockAssignment P, QP P a ≤ hR₁ → IsDominant X P a ρ := by
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

end SBEEForcing