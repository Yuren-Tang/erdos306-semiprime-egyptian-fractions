/-
# SBEE Fingerprint: Theorem C via its decomposition (note 32)

This file formalizes the decomposition of **Theorem C** (`fingerprint_count`)
described in `32 Theorem C Decomposition - Phase Identity and Cold Rigidity.md`.

The deterministic dispersion engine is already fully machine-verified in
`LocalEnergy.ReciprocalDispersion` (`linearCongruence_pair_count`, `reciprocalPhase_smallBall_count`,
`reciprocalPhase_energy_lower_bound`, `reciprocalPhase_sub_le`, …).  Here we build, in order:

* `tEnergy` — the per-vertex fingerprint energy `t_q(w) = ∑_{p∈F} (H_{pq}/pq)²`.
* `phaseP1`  — **Lemma P1** (reciprocalPhase identity / the bridge `crtRepr ↔ reciprocalPhase`).
* `phase_sq_bound` — the squared triangle bound combining P1 with `reciprocalPhase_sub_le`.
* `coldRigidity` — **Lemma P2** (cold rigidity): for `q ∉ F`, at most one residue
  `w` has `t_q(w) < G_F/7`.  This is the novel analytic core.

Notation (note 32): for primes `p, q`, an assignment `a : (p:ℕ) → ZMod p`, and a
candidate residue `w : ZMod q`, the centered integer representatives are
`ZMod.valMinAbs` (the rep in `(-n/2, n/2]`), and `H_{pq}(a_p, w) = crtRepr p q (a p) w`.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import RequestProject.BlockCRTEnergy
import RequestProject.LocalEnergy.ReciprocalDispersion

open Finset
open LocalEnergy

namespace SBEEFingerprint

/-! ## The per-vertex fingerprint energy -/

/-- The per-prime term of the vertex–fingerprint energy:
    `t^{(p)}_q(w) = (H_{pq}(a_p, w) / (p q))²`. -/
noncomputable def tterm (a : (p : ℕ) → ZMod p) (q : ℕ) (w : ZMod q) (p : ℕ) : ℝ :=
  ((crtRepr p q (a p) w : ℝ) / ((p : ℝ) * q)) ^ 2

/-- The vertex–fingerprint energy `t_q(w) = ∑_{p∈F} (H_{pq}(a_p, w)/(pq))²`. -/
noncomputable def tEnergy (F : Finset ℕ) (a : (p : ℕ) → ZMod p)
    (q : ℕ) (w : ZMod q) : ℝ :=
  ∑ p ∈ F, tterm a q w p

lemma tterm_nonneg (a : (p : ℕ) → ZMod p) (q : ℕ) (w : ZMod q) (p : ℕ) :
    0 ≤ tterm a q w p := by
  unfold tterm; positivity

lemma tEnergy_nonneg (F : Finset ℕ) (a : (p : ℕ) → ZMod p)
    (q : ℕ) (w : ZMod q) : 0 ≤ tEnergy F a q w :=
  Finset.sum_nonneg fun _ _ => tterm_nonneg _ _ _ _

/-! ## Lemma P1 — the reciprocalPhase identity (`32` Sub-lemma 1)

For primes `p ≠ q`, with centered integer reps `ã_p = valMinAbs (a p)` and
`w̃ = valMinAbs w`, the reciprocal phase of `ã_p − w̃` is controlled by
`|H_{pq}|/(pq)`:
`reciprocalPhase (ã_p − w̃) q p ≤ |H_{pq}(a_p,w)|/(pq) + 1/(2p)`.

Proof (note 32): `H := crtRepr p q (a p) w` satisfies `H ≡ w̃ (mod q)`, so
`H = w̃ + v q` for an integer `v`; and `H ≡ ã_p (mod p)`, giving
`v ≡ (ã_p − w̃) q̄ (mod p)`.  Since `reciprocalPhase E q p = ‖E q̄ / p‖` depends only on
`E mod p`, `reciprocalPhase (ã_p − w̃) q p = ‖v/p‖`.  Finally
`v/p = H/(pq) − w̃/(pq)`, so `‖v/p‖ ≤ |H|/(pq) + |w̃|/(pq) ≤ |H|/(pq) + 1/(2p)`
using `|w̃| ≤ q/2`. -/

lemma phaseP1 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a : (p : ℕ) → ZMod p) (w : ZMod q) :
    reciprocalPhase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w) q p
      ≤ |(crtRepr p q (a p) w : ℝ)| / ((p : ℝ) * q) + 1 / (2 * p) := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq;
  -- Let H := crtRepr p q (a p) w, ãp := ZMod.valMinAbs (a p), w̃ := ZMod.valMinAbs w, E := ãp - w̃, and q̄ := ((q : ZMod p)⁻¹).val.
  set H := crtRepr p q (a p) w
  set ap := (a p).valMinAbs
  set wtilde := w.valMinAbs
  set E := ap - wtilde
  set qbar := ((q : ZMod p)⁻¹).val;
  -- From v*q ≡ E (mod p): multiply both sides by (q:ZMod p)⁻¹: v ≡ E * (q:ZMod p)⁻¹ (mod p).
  obtain ⟨k, hk⟩ : ∃ k : ℤ, E * qbar - (H - wtilde) / q = p * k := by
    have h_mod : (H - wtilde) / q * q ≡ E [ZMOD p] := by
      have h_mod : (H : ZMod p) = ap := by
        convert crtRepr_congr_left p q ( a p ) w _;
        · convert ZMod.coe_valMinAbs ( a p );
        · exact hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h;
      rw [ Int.ediv_mul_cancel ];
      · simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        grind;
      · have h_mod : (H : ZMod q) = w := by
          convert crtRepr_congr_right p q ( a p ) w _ using 1;
          · exact hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h;
        rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
    have h_mod : (H - wtilde) / q ≡ E * qbar [ZMOD p] := by
      simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
      simp +zetaDelta at *;
      rw [ ← h_mod, mul_assoc, mul_inv_cancel₀ ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact fun h => hpq <| by have := Nat.prime_dvd_prime_iff_eq hp hq; tauto ), mul_one ];
    exact h_mod.dvd;
  -- So |x - round x| = |(v:ℝ)/p - round ((v:ℝ)/p)|.
  have h_abs : reciprocalPhase E q p = |(H - wtilde : ℝ) / (p * q) - round ((H - wtilde : ℝ) / (p * q))| := by
    -- Substitute hk into the expression for x - round x.
    have h_subst : (E : ℝ) * qbar / p = (H - wtilde : ℝ) / (p * q) + k := by
      rw [ div_add', div_eq_div_iff ] <;> norm_cast <;> simp_all +decide [ hp.ne_zero, hq.ne_zero ];
      rw [ ← Int.ediv_mul_cancel ( show ( q : ℤ ) ∣ H - wtilde from ?_ ) ] ; linear_combination hk * p * q;
      have h_div : (crtRepr p q (a p) w : ZMod q) = w := by
        convert crtRepr_congr_right p q ( a p ) w _ using 1;
        · exact hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h;
      haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
      aesop;
    unfold reciprocalPhase
    rw [h_subst]
    simp [UnitAddCircle.norm_eq]
  -- So |(v:ℝ)/p - round ((v:ℝ)/p)| ≤ |(v:ℝ)/p|.
  have h_abs_le : |(H - wtilde : ℝ) / (p * q) - round ((H - wtilde : ℝ) / (p * q))| ≤ |(H - wtilde : ℝ) / (p * q)| := by
    simpa using (round_le ((H - wtilde : ℝ) / (p * q)) 0)
  -- So |(H - w̃)/(p*q)| ≤ |H|/(p*q) + |w̃|/(p*q).
  have h_abs_le' : |(H - wtilde : ℝ) / (p * q)| ≤ |(H : ℝ)| / (p * q) + |(wtilde : ℝ)| / (p * q) := by
    rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ p * q ) ];
    rw [ ← add_div ] ; gcongr ; exact abs_sub _ _;
  -- Since |w̃| ≤ q/2, we have |w̃|/(p*q) ≤ 1/(2*p).
  have h_wtilde_le : |(wtilde : ℝ)| / (p * q) ≤ 1 / (2 * p) := by
    have h_wtilde_le : |(wtilde : ℝ)| ≤ q / 2 := by
      have := ZMod.valMinAbs_mem_Ioc w;
      rw [ le_div_iff₀ ] <;> norm_cast;
      grind;
    rw [ div_le_div_iff₀ ] <;> nlinarith [ show ( p : ℝ ) > 0 by exact Nat.cast_pos.mpr hp.pos, show ( q : ℝ ) > 0 by exact Nat.cast_pos.mpr hq.pos ];
  linarith

/-! ## The squared triangle bound

Combining `reciprocalPhase_sub_le` with `phaseP1` applied to `w` and `w'`:
`reciprocalPhase (w̃' − w̃) q p ≤ |H_w|/(pq) + |H_{w'}|/(pq) + 1/p`, and then
`(α+β+γ)² ≤ 3(α²+β²+γ²)` gives the per-prime squared bound. -/

lemma phase_sq_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a : (p : ℕ) → ZMod p) (w w' : ZMod q) :
    (reciprocalPhase (ZMod.valMinAbs w' - ZMod.valMinAbs w) q p) ^ 2
      ≤ 3 * tterm a q w p + 3 * tterm a q w' p + 3 / (p : ℝ) ^ 2 := by
  -- Apply `reciprocalPhase_sub_le` with A := ZMod.valMinAbs (a p) - ZMod.valMinAbs w and B := ZMod.valMinAbs (a p) - ZMod.valMinAbs w'.
  have h_reciprocalPhase_sub_le : reciprocalPhase (w'.valMinAbs - w.valMinAbs) q p ≤ reciprocalPhase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w) q p + reciprocalPhase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w') q p := by
    convert reciprocalPhase_sub_le ((a p).valMinAbs - w.valMinAbs)
      ((a p).valMinAbs - w'.valMinAbs) q p using 1
    ring_nf
  -- Apply `phaseP1` to w and w'.
  have h_phaseP1_w : reciprocalPhase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w) q p ≤ |(crtRepr p q (a p) w : ℝ)| / ((p : ℝ) * q) + 1 / (2 * p) := by
    exact phaseP1 p q hp hq hpq a w
  have h_phaseP1_w' : reciprocalPhase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w') q p ≤ |(crtRepr p q (a p) w' : ℝ)| / ((p : ℝ) * q) + 1 / (2 * p) := by
    exact phaseP1 p q hp hq hpq a w'
  -- Set bw := |(crtRepr p q (a p) w : ℝ)|/((p:ℝ)*q) and bw' := |(crtRepr p q (a p) w' : ℝ)|/((p:ℝ)*q).
  set bw := |(crtRepr p q (a p) w : ℝ)| / ((p : ℝ) * q)
  set bw' := |(crtRepr p q (a p) w' : ℝ)| / ((p : ℝ) * q);
  -- By definition of $tterm$, we have $tterm a q w p = bw^2$ and $tterm a q w' p = bw'^2$.
  have htterm : tterm a q w p = bw^2 ∧ tterm a q w' p = bw'^2 := by
    constructor <;> simp only [tterm, bw, bw'] <;>
      rw [div_pow, div_pow, sq_abs]
  -- By combining the inequalities from `reciprocalPhase_sub_le`, `phaseP1_w`, and `phaseP1_w'`, we get:
  have h_combined : reciprocalPhase (w'.valMinAbs - w.valMinAbs) q p ≤ bw + bw' + 1 / (p : ℝ) := by
    calc
      reciprocalPhase (w'.valMinAbs - w.valMinAbs) q p
          ≤ (bw + 1 / (2 * p)) + (bw' + 1 / (2 * p)) :=
        h_reciprocalPhase_sub_le.trans (add_le_add h_phaseP1_w h_phaseP1_w')
      _ = bw + bw' + 1 / (p : ℝ) := by
        field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]
        ring
  -- By squaring both sides of the inequality from `h_combined`, we get:
  have h_squared : reciprocalPhase (w'.valMinAbs - w.valMinAbs) q p ^ 2 ≤ (bw + bw' + 1 / (p : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ ( reciprocalPhase_nonneg _ _ _ ) h_combined 2;
  refine le_trans h_squared ?_;
  rw [htterm.1, htterm.2]
  simp only [div_eq_mul_inv, one_mul]
  rw [← inv_pow]
  nlinarith only [ sq_nonneg ( bw - bw' ), sq_nonneg ( bw - ( p : ℝ ) ⁻¹ ), sq_nonneg ( bw' - ( p : ℝ ) ⁻¹ ) ]

/-! ## Lemma P2 — cold rigidity (`32` Sub-lemma 2)

For `q ∉ F`, at most one residue `w` has `t_q(w) < G_F/7` where
`G_F = |F|³/(2¹¹ X²)`.  The contradiction (using `reciprocalPhase_energy_lower_bound`)
requires `|F|` larger than an absolute constant; `43008 ≤ |F|²`
(i.e. `|F| ≥ 208`) is what the `(α+β+γ)²≤3(α²+β²+γ²)` step needs. -/

lemma coldRigidity (X : ℕ) (hX : 1 ≤ X) (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X)
    (hFcard : 208 ≤ F.card)
    (a : (p : ℕ) → ZMod p)
    (q : ℕ) (hq : q.Prime) (hqF : q ∉ F) (hq2X : q ≤ 2 * X)
    (w w' : ZMod q)
    (hw : tEnergy F a q w < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7)
    (hw' : tEnergy F a q w' < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7) :
    w = w' := by
  by_contra h_neq
  set E := (ZMod.valMinAbs w' - ZMod.valMinAbs w) with hE_def
  have hE_zero : ¬ (q : ℤ) ∣ E := by
    haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
    exact sub_ne_zero_of_ne <| Ne.symm h_neq
  have hE_abs : 0 < |E| ∧ |E| < q := by
    have hE_abs : -(q : ℤ) < 2 * w'.valMinAbs ∧ 2 * w'.valMinAbs ≤ q ∧ -(q : ℤ) < 2 * w.valMinAbs ∧ 2 * w.valMinAbs ≤ q := by
      haveI := Fact.mk hq; exact ⟨ by linarith [ ZMod.valMinAbs_mem_Ioc w' |>.1 ], by linarith [ ZMod.valMinAbs_mem_Ioc w' |>.2 ], by linarith [ ZMod.valMinAbs_mem_Ioc w |>.1 ], by linarith [ ZMod.valMinAbs_mem_Ioc w |>.2 ] ⟩ ;
    exact ⟨ abs_pos.mpr ( show E ≠ 0 from sub_ne_zero.mpr <| by aesop ), abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩;
  have h_sum_bound : ∑ p ∈ F, (reciprocalPhase E q p) ^ 2 ≤ 3 * tEnergy F a q w + 3 * tEnergy F a q w' + 3 * (F.card : ℝ) / (X : ℝ) ^ 2 := by
    have h_sum_bound : ∀ p ∈ F, (reciprocalPhase E q p) ^ 2 ≤ 3 * tterm a q w p + 3 * tterm a q w' p + 3 / (p : ℝ) ^ 2 := by
      grind +suggestions;
    refine le_trans ( Finset.sum_le_sum h_sum_bound ) ?_;
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, tEnergy ];
    exact le_trans ( Finset.sum_le_sum fun x hx => show ( 3 : ℝ ) / x ^ 2 ≤ 3 / X ^ 2 by gcongr ; linarith [ hF x hx ] ) ( by norm_num; ring_nf; norm_num );
  have h_sum_bound : (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) ≤ 3 * tEnergy F a q w + 3 * tEnergy F a q w' + 3 * (F.card : ℝ) / (X : ℝ) ^ 2 := by
    convert reciprocalPhase_energy_lower_bound X F hF ( by linarith ) q hq hqF hq2X E hE_zero hE_abs.1 hE_abs.2 |> le_trans <| h_sum_bound using 1;
  -- Simplify the inequality obtained from the sum bound.
  have h_simplified : (F.card : ℝ) ^ 2 < 3 * 7 * 2 ^ 11 := by
    ring_nf at *;
    nlinarith [ show ( 0 : ℝ ) < ( X : ℝ ) ⁻¹ ^ 2 by positivity, show ( 0 : ℝ ) < ( F.card : ℝ ) * ( X : ℝ ) ⁻¹ ^ 2 by positivity ];
  exact absurd h_simplified ( by norm_cast; nlinarith only [ hFcard ] )

/-! ## Lemma P3 — the decoding injection (`32` Sub-lemma 3)

The map `a ↦ (a|_F, Hot(a), residues on Hot)` is injective on the level set:
cold vertices (those `q ∉ F` with `t_q(a_q) < T`) are decoded uniquely via
`coldRigidity`, since `t_q(·)` is a function of `a|_F` alone. -/

/-- `tEnergy F a q w` depends only on the values of `a` on `F`. -/
lemma tEnergy_congr_on_F (F : Finset ℕ) (a b : (p : ℕ) → ZMod p) (q : ℕ)
    (w : ZMod q) (h : ∀ p ∈ F, a p = b p) :
    tEnergy F a q w = tEnergy F b q w := by
  unfold tEnergy tterm
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [h p hp]

/-- **Cold-decoding uniqueness** — the substance of Lemma P3, the place where
    `coldRigidity` (Lemma P2) is used.  Suppose two assignments `a, b` agree on
    the fingerprint `F`, have the *same* hot set `Hot = {q ∈ P\F : T ≤ t_q(a_q)}`,
    and agree on that hot set.  Then they agree on all of `P \ F`: every cold
    vertex `q` (with `t_q(a_q) < T`) has `a q` recovered as the unique residue
    with `t_q(·) < T`, a function of `a|_F` alone. -/
lemma cold_decoding_unique (X : ℕ) (hX : 1 ≤ X) (P F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) (hFcard : 208 ≤ F.card)
    (hPF : ∀ q ∈ P \ F, Nat.Prime q ∧ X ≤ q ∧ q ≤ 2 * X)
    (T : ℝ) (hT : T = (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7)
    (a b : (p : ℕ) → ZMod p)
    (hab : ∀ p ∈ F, a p = b p)
    (hHot : (P \ F).filter (fun q => T ≤ tEnergy F a q (a q))
              = (P \ F).filter (fun q => T ≤ tEnergy F b q (b q)))
    (hres : ∀ q ∈ (P \ F).filter (fun q => T ≤ tEnergy F a q (a q)), a q = b q) :
    ∀ q ∈ P \ F, a q = b q := by
  intro q hq
  obtain ⟨hqprime, hqX, hq2X⟩ := hPF q hq
  have hqF : q ∉ F := (Finset.mem_sdiff.mp hq).2
  -- The F-energy of any residue `w` at `q` agrees for `a` and `b` (they agree on F).
  have hcongr : ∀ w : ZMod q, tEnergy F a q w = tEnergy F b q w :=
    fun w => tEnergy_congr_on_F F a b q w hab
  by_cases hhot : T ≤ tEnergy F a q (a q)
  · -- `q` is hot: residue given directly.
    exact hres q (Finset.mem_filter.mpr ⟨hq, hhot⟩)
  · -- `q` is cold: both `a q` and `b q` have F-energy `< T`; coldRigidity gives uniqueness.
    push Not at hhot
    have hcoldA : tEnergy F a q (a q) < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7 :=
      hT ▸ hhot
    -- `q ∉ Hot(b)` too, since the hot sets coincide.
    have hnotHotB : q ∉ (P \ F).filter (fun q => T ≤ tEnergy F b q (b q)) := by
      rw [← hHot]; exact fun hmem => hhot.not_ge (Finset.mem_filter.mp hmem).2
    have hcoldB : tEnergy F b q (b q) < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7 := by
      by_contra hc; push Not at hc
      exact hnotHotB (Finset.mem_filter.mpr ⟨hq, hT ▸ hc⟩)
    -- Recast `b q`'s energy through `a` (same on F): `tEnergy F a q (b q) < T`.
    have hcoldB' : tEnergy F a q (b q) < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7 := by
      rw [hcongr (b q)]; exact hcoldB
    exact coldRigidity X hX F hF hFcard a q hqprime hqF hq2X (a q) (b q) hcoldA hcoldB'

/-! ## Lemma P3' and Lemma P4 — remaining counting/entropy steps (`32` Sub-lemmas 3', 4)

These complete note 32's decomposition: the *combinatorial* hot-set bound
(`hot_count_bound`) and the *real-analytic* entropy inequality
(`entropy_inequality`).  Both are proved in full below. -/

/-- **Lemma P3' (hot-set bound)** — `32` Sub-lemma 3'.  If the total fingerprint
    energy over `P \ F` is `≤ R`, then the number of hot vertices (those with
    `T ≤ t_q(a_q)`) is at most `R / T`.  Combined with `∑_{q∉F} t_q ≤ Q_P(a) ≤ R`
    this gives `|Hot(a)| ≤ R/T = 7R/G_F`. -/
lemma hot_count_bound (P F : Finset ℕ) (a : (p : ℕ) → ZMod p) (T R : ℝ)
    (hT : 0 < T)
    (hR : ∑ q ∈ P \ F, tEnergy F a q (a q) ≤ R) :
    (((P \ F).filter (fun q => T ≤ tEnergy F a q (a q))).card : ℝ) ≤ R / T := by
  rw [le_div_iff₀ hT]
  set Hot := (P \ F).filter (fun q => T ≤ tEnergy F a q (a q)) with hHotdef
  have h1 : (Hot.card : ℝ) * T ≤ ∑ q ∈ Hot, tEnergy F a q (a q) := by
    have hc := Finset.card_nsmul_le_sum Hot (fun q => tEnergy F a q (a q)) T
      (fun q hq => (Finset.mem_filter.mp hq).2)
    simpa [nsmul_eq_mul] using hc
  have h2 : ∑ q ∈ Hot, tEnergy F a q (a q) ≤ ∑ q ∈ P \ F, tEnergy F a q (a q) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _ _ => tEnergy_nonneg _ _ _ _)
  calc (Hot.card : ℝ) * T ≤ ∑ q ∈ Hot, tEnergy F a q (a q) := h1
    _ ≤ ∑ q ∈ P \ F, tEnergy F a q (a q) := h2
    _ ≤ R := hR

/-- **Lemma P4 (entropy inequality)** — `32` Sub-lemma 4.  The real-analysis
    bound `(2X)^{|F|} · C(|P|,h) · (2X)^h ≤ |P| · e^{εR}` once `R ≥ R_C` and the
    fingerprint/hot sizes obey the window relations below.  Proved in full with
    `Ceps = max ((2²¹·7/ε⁴)^{1/3}) (8/ε)` and `X0 = 3`.

    The window relations encode the fingerprint choice `Fc = ⌈εR/(2 log 2X)⌉`
    (hence both `εR/(2 log 2X) ≤ Fc ≤ εR/(2 log 2X) + 1`; the lower bound is
    essential since `Fc³` controls the hot count `h`), `Fc ≥ 8`, the block size
    `1 ≤ NP = |P| ≤ 2X`, and the hot bound `h ≤ 7R·(2¹¹X²)/Fc³` (Lemma P3').
-/
lemma entropy_inequality (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ (Ceps X0 : ℝ), 0 < Ceps ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X → ∀ (NP Fc h : ℕ) (R : ℝ),
        Ceps * (X : ℝ) ^ ((2 : ℝ) / 3) * (Real.log X) ^ ((4 : ℝ) / 3) ≤ R →
        1 ≤ NP → NP ≤ 2 * X → 8 ≤ Fc →
        eps * R / (2 * Real.log (2 * X)) ≤ (Fc : ℝ) →
        (Fc : ℝ) ≤ eps * R / (2 * Real.log (2 * X)) + 1 →
        (h : ℝ) ≤ 7 * R * (2 ^ 11 * (X : ℝ) ^ 2) / (Fc : ℝ) ^ 3 →
        (2 * (X : ℝ)) ^ Fc * (Nat.choose NP h : ℝ) * (2 * (X : ℝ)) ^ h
          ≤ (NP : ℝ) * Real.exp (eps * R) := by
  -- Choose X0 := 3 and Ceps := max ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3)) (8/eps).
  use max ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3)) (8/eps), 3;
  refine' ⟨ by positivity, by positivity, fun X hX NP Fc h R hR hNP hNP' hFc hFc' hFc'' hh => _ ⟩;
  -- Now use the provided inequalities to bound the terms.
  have h_bound : (Fc : ℝ) * Real.log (2 * X) + 2 * h * Real.log (2 * X) ≤ eps * R := by
    -- Use the provided inequalities to bound the terms.
    have h_bound : (Fc : ℝ) * Real.log (2 * X) ≤ eps * R / 2 + Real.log (2 * X) := by
      rw [ div_add_one, le_div_iff₀ ] at hFc'' <;> nlinarith [ Real.log_pos ( show ( 2 * X : ℝ ) > 1 by linarith ) ]
    have h_bound' : 2 * h * Real.log (2 * X) ≤ 7 * 2^15 * X^2 * (Real.log (2 * X))^4 / (eps^3 * R^2) := by
      have h_bound' : (h : ℝ) ≤ 7 * R * (2^11 * X^2) / (eps^3 * R^3 / (8 * (Real.log (2 * X))^3)) := by
        have h_bound' : (Fc : ℝ) ^ 3 ≥ (eps * R / (2 * Real.log (2 * X))) ^ 3 := by
          exact pow_le_pow_left₀ ( div_nonneg ( mul_nonneg hε0.le ( show 0 ≤ R by exact le_trans ( by positivity ) hR ) ) ( mul_nonneg zero_le_two ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ) hFc' 3;
        refine le_trans hh ?_;
        gcongr;
        · exact mul_nonneg ( mul_nonneg ( by norm_num ) ( le_trans ( by positivity ) hR ) ) ( by positivity );
        · refine' div_pos ( mul_pos ( pow_pos hε0 3 ) ( pow_pos _ 3 ) ) ( mul_pos ( by norm_num ) ( pow_pos ( Real.log_pos ( by linarith ) ) 3 ) );
          exact lt_of_lt_of_le ( by exact mul_pos ( mul_pos ( lt_max_of_lt_left ( by positivity ) ) ( by positivity ) ) ( by exact Real.rpow_pos_of_pos ( Real.log_pos ( by linarith ) ) _ ) ) hR;
        · convert h_bound'.le using 1
          all_goals first | rfl | ring_nf
      convert mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h_bound' zero_le_two)
        (Real.log_nonneg <| show (2 * X : ℝ) ≥ 1 by linarith) using 1
      all_goals first | rfl | ring_nf
      grind;
    -- Use the provided inequalities to bound the terms further.
    have h_bound'' : R^3 ≥ 2^21 * 7 * X^2 * (Real.log X)^4 / eps^4 := by
      have h_bound'' : R^3 ≥ ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) * X^(2/3 : ℝ) * (Real.log X)^(4/3 : ℝ))^3 := by
        gcongr;
        exact le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) ( by exact Real.rpow_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) _ ) ) hR;
      convert h_bound'' using 1 ; ring_nf;
      repeat rw [ ← Real.rpow_natCast ] ; repeat rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf;
    have h_bound''' : Real.log (2 * X) ≤ 2 * Real.log X := by
      rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith only [ hX, show X ≥ 3 by exact_mod_cast hX ];
    have h_bound'''' : 7 * 2^15 * X^2 * (Real.log (2 * X))^4 / (eps^3 * R^2) ≤ eps * R / 4 := by
      rw [ div_le_iff₀ ];
      · have h_bound'''' : 7 * 2^15 * X^2 * (2 * Real.log X)^4 ≤ eps^4 * R^3 / 4 := by
          rw [ ge_iff_le, div_le_iff₀ ] at h_bound'' <;> first | positivity | linarith;
        exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Real.log_nonneg ( by linarith ) ) h_bound''' 4 ) ( by positivity ) ) ( by linarith );
      · exact mul_pos ( pow_pos hε0 3 ) ( sq_pos_of_pos ( lt_of_lt_of_le ( by exact mul_pos ( mul_pos ( lt_max_of_lt_left ( by positivity ) ) ( by positivity ) ) ( Real.rpow_pos_of_pos ( Real.log_pos ( by norm_cast at *; linarith ) ) _ ) ) hR ) );
    have h_bound''''' : R ≥ 8 * Real.log X / eps := by
      refine le_trans ?_ hR;
      refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) <| by positivity ) <| by exact Real.rpow_nonneg ( Real.log_nonneg <| by linarith ) _ );
      rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right ] <;> try positivity;
      rw [ mul_assoc ];
      gcongr;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith ) <| show ( 4 : ℝ ) / 3 ≥ 1 by norm_num ) <| by positivity ) ; norm_num;
      exact le_mul_of_one_le_left ( Real.log_nonneg ( by linarith ) ) ( Real.one_le_rpow ( by linarith ) ( by norm_num ) );
    rw [ ge_iff_le, div_le_iff₀ ] at h_bound''''' <;> nlinarith [ Real.log_pos ( show ( X : ℝ ) > 1 by linarith ) ];
  -- Use the provided inequalities to bound the terms.
  have h_bound : (Nat.choose NP h : ℝ) ≤ NP ^ h := by
    exact_mod_cast Nat.choose_le_pow _ _;
  refine le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_bound <| by positivity ) <| by positivity ) ?_;
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( show eps * R ≥ Fc * Real.log ( 2 * X ) + h * Real.log ( 2 * X ) + h * Real.log NP by
                                                                          nlinarith [ Real.log_nonneg ( show ( NP : ℝ ) ≥ 1 by norm_cast ), Real.log_le_log ( by positivity ) ( show ( NP : ℝ ) ≤ 2 * X by norm_cast ) ] ) ) ( by positivity ) );
  rw [ Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log ( by positivity ), Real.exp_nat_mul, Real.exp_log ( by positivity ), Real.exp_nat_mul, Real.exp_log ( by positivity ) ] ; ring_nf ; norm_num;
  exact mul_le_mul_of_nonneg_right ( le_mul_of_one_le_right ( by positivity ) ( by norm_cast ) ) ( by positivity )

/-
**Entropy inequality with the hot-count polynomial factor absorbed.**
    Strengthening of `entropy_inequality` that carries the extra `(h+1)` factor
    coming from summing over hot-set sizes `0 ≤ k ≤ h` (`∑_{k≤h} C(NP,k)(2X)^k ≤
    (h+1)·C(NP,h)(2X)^h`).  Obtained from `entropy_inequality` applied to `eps`
    (same window) and the bound `(h+1) ≤ exp(eps·R)` (since `h ≤ R/T` is
    polynomial in `X, R` while `R ≥ R_C` makes `exp(eps R)` dominate); the price
    is the doubled exponent `exp(2 eps R)`.
-/
set_option maxHeartbeats 1000000 in
lemma entropy_inequality2 (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ (Ceps X0 : ℝ), 0 < Ceps ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X → ∀ (NP Fc h : ℕ) (R : ℝ),
        Ceps * (X : ℝ) ^ ((2 : ℝ) / 3) * (Real.log X) ^ ((4 : ℝ) / 3) ≤ R →
        1 ≤ NP → NP ≤ 2 * X → 8 ≤ Fc →
        eps * R / (2 * Real.log (2 * X)) ≤ (Fc : ℝ) →
        (Fc : ℝ) ≤ eps * R / (2 * Real.log (2 * X)) + 1 →
        (h : ℝ) ≤ 7 * R * (2 ^ 11 * (X : ℝ) ^ 2) / (Fc : ℝ) ^ 3 →
        (2 * (X : ℝ)) ^ Fc * ((h : ℝ) + 1) * (Nat.choose NP h : ℝ) * (2 * (X : ℝ)) ^ h
          ≤ (NP : ℝ) * Real.exp (2 * eps * R) := by
  obtain ⟨C2, X02, hC2, hX02, Hent⟩ := entropy_inequality eps hε0 hε1
  use max C2 ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) + 1), max X02 3;
  refine' ⟨ by positivity, by positivity, fun X hX NP Fc h R hR hNP hNP' hFc hFc' hFc'' hh => _ ⟩;
  -- Now show `(h:ℝ)+1 ≤ exp(eps*R)` (★).
  have h_exp : (h : ℝ) + 1 ≤ Real.exp (eps * R) := by
    -- By `Real.add_one_le_exp`, `exp(eps R) ≥ eps*R + 1`. So it suffices `2^17*7*X^2*L^3/(eps^3 R^2) ≤ eps*R`, i.e. `2^17*7*X^2*L^3 ≤ eps^4 * R^3`.
    have h_suff : 2^17 * 7 * (X : ℝ)^2 * (Real.log (2 * X))^3 ≤ eps^4 * R^3 := by
      -- Using `L ≤ 2 log X` (so `L^3 ≤ 8 (log X)^3`) and `R ≥ Ceps*X^(2/3)(log X)^(4/3)` (so `R^3 ≥ Ceps^3 X^2 (log X)^4`), it suffices `2^17*7*8 X^2 (log X)^3 ≤ eps^4 Ceps^3 X^2 (log X)^4`, i.e. `2^20*7 ≤ eps^4 Ceps^3 (log X)`.
      have h_suff' : 2^20 * 7 ≤ eps^4 * (max C2 ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) + 1))^3 * Real.log X := by
        have h_suff' : eps^4 * (max C2 ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) + 1))^3 ≥ 2^21 * 7 := by
          have h_suff' : eps^4 * ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) + 1)^3 ≥ 2^21 * 7 := by
            ring_nf;
            rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf ; norm_num [ hε0.ne' ];
            exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( by linarith [ pow_pos hε0 4 ] ) ( by positivity ) ) ( by positivity );
          exact h_suff'.trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( le_max_right _ _ ) _ ) ( by positivity ) );
        have h_log_X : Real.log X ≥ 1 / 2 := by
          exact le_trans ( Real.log_two_gt_d9.le.trans' <| by norm_num ) ( Real.log_le_log ( by norm_num ) <| Nat.cast_le.mpr <| show X ≥ 2 by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] );
        nlinarith;
      -- Using `L ≤ 2 log X` (so `L^3 ≤ 8 (log X)^3`) and `R ≥ Ceps*X^(2/3)(log X)^(4/3)` (so `R^3 ≥ Ceps^3 X^2 (log X)^4`), we get:
      have h_bound : (Real.log (2 * X))^3 ≤ 8 * (Real.log X)^3 := by
        rw [ Real.log_mul ( by positivity ) ( by norm_cast; linarith [ show X > 0 from Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ] ) ];
        nlinarith only [ sq_nonneg ( Real.log 2 - Real.log X ), sq_nonneg ( Real.log 2 + Real.log X ), Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( show ( X : ℝ ) ≥ 2 by norm_cast; linarith [ show X ≥ 2 by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ] ) ]
      have h_bound_R : R^3 ≥ (max C2 ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) + 1))^3 * (X : ℝ)^2 * (Real.log X)^4 := by
        refine' le_trans _ ( pow_le_pow_left₀ _ hR 3 );
        · ring_nf;
          norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), ← Real.rpow_mul ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ show X ≥ 1 by linarith [ show X ≥ 1 by exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at * ) ] ] ) : 1 ≤ ( X : ℝ ) ) ) ];
          norm_cast;
        · exact mul_nonneg ( mul_nonneg ( le_max_of_le_left hC2.le ) ( by positivity ) ) ( Real.rpow_nonneg ( Real.log_nonneg ( by norm_cast; linarith [ show X ≥ 1 by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ] ) ) _ );
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_bound_R <| by positivity );
      refine le_trans ( mul_le_mul_of_nonneg_left h_bound <| by positivity ) ?_;
      convert mul_le_mul_of_nonneg_right h_suff' ( show 0 ≤ ( X : ℝ ) ^ 2 * Real.log X ^ 3 by positivity ) using 1 <;> ring;
    -- Using the window, `Fc ≥ eps*R/(2*L)`, so `Fc^3 ≥ (eps*R/(2L))^3`, hence `h ≤ 7*R*(2^11*X^2)/Fc^3 ≤ 7*R*2^11*X^2 / (eps*R/(2L))^3 = 2^17*7 * X^2 * L^3 / (eps^3 * R^2)`.
    have h_h_bound : (h : ℝ) ≤ 2^17 * 7 * (X : ℝ)^2 * (Real.log (2 * X))^3 / (eps^3 * R^2) := by
      have h_h_bound : (Fc : ℝ)^3 ≥ (eps * R / (2 * Real.log (2 * X)))^3 := by
        gcongr;
        exact div_nonneg ( mul_nonneg hε0.le ( le_trans ( by positivity ) hR ) ) ( mul_nonneg zero_le_two ( Real.log_nonneg ( by norm_cast; linarith [ show X ≥ 1 by linarith [ show X ≥ 1 by linarith [ show X ≥ 1 by exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at * ) ] ] ] ) ) );
      refine le_trans hh ?_;
      rw [ div_le_div_iff₀ ];
      · refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_h_bound ?_ );
        · ring_nf;
          norm_num [ show Real.log ( X * 2 ) ≠ 0 by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ];
          exact mul_le_mul_of_nonneg_left ( by norm_num ) ( by exact mul_nonneg ( mul_nonneg ( pow_nonneg ( show 0 ≤ R by exact le_trans ( by positivity ) hR ) _ ) ( sq_nonneg _ ) ) ( pow_nonneg hε0.le _ ) );
        · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) ( by norm_num ) ) ( sq_nonneg _ ) ) ( pow_nonneg ( Real.log_nonneg ( by norm_cast; linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ) ) _ );
      · positivity;
      · exact mul_pos ( pow_pos hε0 3 ) ( sq_pos_of_pos ( lt_of_lt_of_le ( by exact mul_pos ( mul_pos ( lt_max_of_lt_left hC2 ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ) ) _ ) ) ( Real.rpow_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ) ) ) _ ) ) hR ) );
    -- Using the window, `Fc ≥ eps*R/(2*L)`, so `Fc^3 ≥ (eps*R/(2L))^3`, hence `h ≤ 7*R*(2^11*X^2)/Fc^3 ≤ 7*R*2^11*X^2 / (eps*R/(2L))^3 = 2^17*7 * X^2 * L^3 / (eps^3 * R^2)`. Therefore, `h + 1 ≤ eps * R + 1`.
    have h_h_bound : (h : ℝ) ≤ eps * R := by
      refine le_trans h_h_bound ?_;
      rw [ div_le_iff₀ ];
      · linarith;
      · refine' mul_pos ( pow_pos hε0 3 ) ( sq_pos_of_pos _ );
        exact lt_of_lt_of_le ( by exact mul_pos ( mul_pos ( lt_max_of_lt_left hC2 ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ) ) _ ) ) ( Real.rpow_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_right _ _ ) hX ] ) ) ) _ ) ) hR;
    linarith [ Real.add_one_le_exp ( eps * R ) ];
  have hR_C2 : C2 * (X : ℝ) ^ ((2 : ℝ) / 3) *
      (Real.log X) ^ ((4 : ℝ) / 3) ≤ R := by
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C2 _) (by positivity))
        (Real.rpow_nonneg (Real.log_nonneg (by
          norm_cast
          linarith [show X ≥ 3 by exact_mod_cast le_trans (le_max_right X02 3) hX])) _))
      hR
  have hmul := mul_le_mul h_exp
    (Hent X (le_trans (le_max_left _ _) hX) NP Fc h R hR_C2
      hNP hNP' hFc hFc' hFc'' hh)
    (by positivity) (by positivity)
  calc
    (2 * (X : ℝ)) ^ Fc * ((h : ℝ) + 1) * (Nat.choose NP h : ℝ) *
        (2 * (X : ℝ)) ^ h =
      ((h : ℝ) + 1) *
        ((2 * (X : ℝ)) ^ Fc * (Nat.choose NP h : ℝ) *
          (2 * (X : ℝ)) ^ h) := by ring
    _ ≤ Real.exp (eps * R) * ((NP : ℝ) * Real.exp (eps * R)) := hmul
    _ = (NP : ℝ) * Real.exp (2 * eps * R) := by
      rw [show 2 * eps * R = (2 : ℕ) * (eps * R) by ring, Real.exp_nat_mul]
      ring

/-! ## Theorem C (fingerprint count) — final assembly (`30 §1`, note `32` assembly)

This section assembles `fingerprint_count` (Theorem C) from the verified pieces
of this file (`coldRigidity`, `cold_decoding_unique`, `hot_count_bound`,
`entropy_inequality`) together with the deterministic dispersion engine of
`LocalEnergy.ReciprocalDispersion`.  The `BlockAssignment`-level objects (`QP`,
`BlockAssignment`) live in `BlockCRTEnergy.lean`; the fingerprint machinery uses
total functions `(p : ℕ) → ZMod p`, so we bridge via `extendAssign`. -/

/-- Extend a block assignment `a : BlockAssignment P` to a total residue
    function `(p : ℕ) → ZMod p`, set to `0` outside `P`.  This is the bridge
    between the `BlockCRTEnergy` objects (`QP`, level sets) and the fingerprint
    energy `tEnergy` of this file. -/
noncomputable def extendAssign (P : Finset ℕ) (a : BlockAssignment P) :
    (p : ℕ) → ZMod p :=
  fun p => if h : p ∈ P then a ⟨p, h⟩ else 0

lemma extendAssign_mem (P : Finset ℕ) (a : BlockAssignment P) {p : ℕ}
    (hp : p ∈ P) : extendAssign P a p = a ⟨p, hp⟩ := by
  simp [extendAssign, hp]

/-- Two block assignments with equal extensions are equal. -/
lemma extendAssign_injective (P : Finset ℕ) :
    Function.Injective (extendAssign P) := by
  intro a b h
  funext p
  obtain ⟨p, hp⟩ := p
  simpa [extendAssign_mem P a hp, extendAssign_mem P b hp] using congrFun h p

/-
**Lower subset existence.**  Any `k ≤ |P|` elements can be chosen as the `k`
    smallest elements of `P`: there is `F ⊆ P` with `|F| = k` such that every
    element of `F` is strictly below every element of `P \ F`.  This is the
    fingerprint-selection step (`F` = the `k` smallest primes of `P`).
-/
lemma exists_lower_subset (P : Finset ℕ) (k : ℕ) (hk : k ≤ P.card) :
    ∃ F ⊆ P, F.card = k ∧ ∀ p ∈ F, ∀ q ∈ P \ F, p < q := by
  induction' k with k ih generalizing P;
  · exact ⟨ ∅, by norm_num ⟩;
  · -- Let $m$ be the smallest element in $P$.
    obtain ⟨m, hm⟩ : ∃ m ∈ P, ∀ p ∈ P, p ≥ m := by
      exact ⟨ Nat.find <| Finset.card_pos.mp <| pos_of_gt hk, Nat.find_spec <| Finset.card_pos.mp <| pos_of_gt hk, fun p hp => Nat.find_min' _ hp ⟩;
    obtain ⟨ F, hF₁, hF₂, hF₃ ⟩ := ih ( P.erase m ) ( by simpa [ Finset.card_erase_of_mem hm.1 ] using by omega ) ; use Insert.insert m F; simp_all +decide [ Finset.subset_iff ] ;
    exact ⟨ by rw [ Finset.card_insert_of_notMem ( fun h => hF₁ h |>.1 rfl ), hF₂ ], fun q hq hq' hq'' => lt_of_le_of_ne ( hm.2 q hq ) ( Ne.symm hq' ) ⟩

/-
**Energy relation** (`30 §1`).  The vertex–fingerprint energies over the
    complement of the fingerprint sum to at most the full CRT energy:
    `∑_{q ∈ P∖F} t_q(a_q) ≤ Q_P(a)`.  The pairs `{(p,q) : p ∈ F, q ∈ P∖F}` are
    distinct ordered pairs of `P` (each `p < q` since `F` is a lower set), hence a
    sub-family of the pairs summed in `Q_P`; all terms are `≥ 0`.
-/
lemma energy_relation (P F : Finset ℕ) [∀ p : P, NeZero p.1]
    (hFP : F ⊆ P) (hFmin : ∀ p ∈ F, ∀ q ∈ P \ F, p < q)
    (a : BlockAssignment P) :
    ∑ q ∈ P \ F, tEnergy F (extendAssign P a) q (extendAssign P a q) ≤ QP P a := by
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
  case refine'_2 => exact Finset.image ( fun pq : { p : P // p.1 ∈ F } × { q : P // q.1 ∈ P \ F } => ( ⟨ pq.1.1, by simp ⟩, ⟨ pq.2.1, by simp ⟩ ) ) ( Finset.univ );
  · rw [ Finset.sum_image ];
    · simp +decide [ tEnergy, extendAssign ];
      convert rfl.le using 1;
      rw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun x hx => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> simp +decide [ tterm ];
      · tauto;
      · aesop;
      · grind;
      · unfold extendAssign; aesop;
    · intro x hx y hy; aesop;
  · simp +decide [ Finset.subset_iff, orderedPrimePairsA ];
    aesop;
  · exact fun _ _ _ => sq_nonneg _

/-
**Decoding cardinality bound** (`30 §1` encoding, note `32` Lemma P3/P3').
    The level set `{a : Q_P(a) ≤ R}` injects (via `cold_decoding_unique`) into
    `{a|_F} × {(S, residues) : S ⊆ P∖F, |S| ≤ h_max}`, whose cardinality is
    `≤ (2X)^{|F|} · (h_max+1) · C(|P|, h_max) · (2X)^{h_max}`.

    This bundles the decoding injection (Lemma P3, using `cold_decoding_unique`),
    the hot-set bound (Lemma P3', `hot_count_bound`, via `energy_relation`), and
    the sub-set/residue counting `∑_{k ≤ h_max} C(|P∖F|,k)(2X)^k ≤
    (h_max+1)·C(|P|,h_max)(2X)^{h_max}`.
-/
set_option maxHeartbeats 2000000 in
lemma decoding_card_bound
    (X : ℕ) (hX : 1 ≤ X) (P F : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X)
    (hFP : F ⊆ P) (hFcard : 208 ≤ F.card)
    (hFmin : ∀ p ∈ F, ∀ q ∈ P \ F, p < q)
    (T R : ℝ) (hT : T = (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7) (hT0 : 0 < T)
    (hmax : ℕ) (hhmax : R / T < (hmax : ℝ) + 1) (hmaxP : hmax ≤ P.card) :
    ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
      ≤ (2 * (X : ℝ)) ^ F.card * ((hmax : ℝ) + 1)
          * (Nat.choose P.card hmax) * (2 * (X : ℝ)) ^ hmax := by
  have h_card_bound : ∀ a : BlockAssignment P, QP P a ≤ R → (Finset.filter (fun q => T ≤ tEnergy F (extendAssign P a) q (extendAssign P a q)) (P \ F)).card ≤ hmax := by
    intro a ha
    have h_card : (Finset.filter (fun q => T ≤ tEnergy F (extendAssign P a) q (extendAssign P a q)) (P \ F)).card ≤ R / T := by
      apply hot_count_bound P F (extendAssign P a) T R hT0 (by
      exact le_trans ( energy_relation P F hFP hFmin a ) ha);
    exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith );
  have h_card_bound : ∀ S : Finset ℕ, S ⊆ P \ F → S.card ≤ hmax → (Finset.filter (fun a : BlockAssignment P => Finset.filter (fun q => T ≤ tEnergy F (extendAssign P a) q (extendAssign P a q)) (P \ F) = S) (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R))).card ≤ (∏ p ∈ F, p) * (∏ q ∈ S, q) := by
    intros S hS_sub hS_card
    have h_card_bound : ∀ a b : BlockAssignment P, QP P a ≤ R → QP P b ≤ R → Finset.filter (fun q => T ≤ tEnergy F (extendAssign P a) q (extendAssign P a q)) (P \ F) = S → Finset.filter (fun q => T ≤ tEnergy F (extendAssign P b) q (extendAssign P b q)) (P \ F) = S → (∀ p ∈ F, extendAssign P a p = extendAssign P b p) → (∀ q ∈ S, extendAssign P a q = extendAssign P b q) → a = b := by
      intros a b ha hb hS_a hS_b hF_eq hS_eq;
      have := @cold_decoding_unique X hX P F ( fun p hp => hP p ( hFP hp ) ) hFcard ( fun q hq => hP q ( Finset.mem_sdiff.mp hq |>.1 ) ) T hT ( extendAssign P a ) ( extendAssign P b ) ?_ ?_ ?_ <;> simp_all +decide [ Finset.ext_iff ];
      ext ⟨ p, hp ⟩ ; by_cases hpF : p ∈ F <;> simp_all +decide [ extendAssign ] ;
      simpa [ hp ] using hF_eq p hpF;
    have h_card_bound : (Finset.image (fun a : BlockAssignment P => (fun p : F => a ⟨p.1, hFP p.2⟩, fun q : S => a ⟨q.1, Finset.mem_sdiff.mp (hS_sub q.2) |>.1⟩)) (Finset.filter (fun a : BlockAssignment P => Finset.filter (fun q => T ≤ tEnergy F (extendAssign P a) q (extendAssign P a q)) (P \ F) = S) (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)))).card ≤ (∏ p ∈ F, p) * (∏ q ∈ S, q) := by
      refine' le_trans ( Finset.card_le_univ _ ) _;
      simp +decide [ Fintype.card_pi ];
      congr! 1; all_goals conv_rhs => rw [ ← Finset.prod_attach ] ;
    rwa [ Finset.card_image_of_injOn ] at h_card_bound;
    intros a ha b hb hab;
    apply_assumption;
    grind +qlia;
    · grind +splitImp;
    · grind;
    · grind;
    · simp +zetaDelta at *;
      simp +decide [ funext_iff, extendAssign ] at hab ⊢;
      exact fun p hp => by simpa [ hFP hp ] using hab.1 p hp;
    · simp_all +decide [ funext_iff ];
      exact fun q hq => by rw [ extendAssign_mem P a ( Finset.mem_sdiff.mp ( hS_sub hq ) |>.1 ), extendAssign_mem P b ( Finset.mem_sdiff.mp ( hS_sub hq ) |>.1 ), hab.2 q hq ] ;
  have h_card_bound : (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card ≤ (∏ p ∈ F, p) * (∑ S ∈ Finset.powerset (P \ F), if S.card ≤ hmax then (∏ q ∈ S, q) else 0) := by
    have h_card_bound : (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card ≤ ∑ S ∈ Finset.powerset (P \ F), (Finset.filter (fun a : BlockAssignment P => Finset.filter (fun q => T ≤ tEnergy F (extendAssign P a) q (extendAssign P a q)) (P \ F) = S) (Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R))).card := by
      rw [ ← Finset.card_eq_sum_card_fiberwise ];
      exact fun x hx => Finset.mem_powerset.mpr <| Finset.filter_subset _ _;
    rw [ Finset.mul_sum _ _ _ ];
    refine le_trans h_card_bound <| Finset.sum_le_sum fun S hS => ?_;
    split_ifs <;> simp_all +decide [ Finset.subset_iff ];
    grind;
  have h_card_bound : (∑ S ∈ Finset.powerset (P \ F), if S.card ≤ hmax then (∏ q ∈ S, q) else 0) ≤ (∑ k ∈ Finset.range (hmax + 1), (Nat.choose (P.card) k) * (2 * X) ^ k) := by
    have h_card_bound : ∀ k ≤ hmax, (∑ S ∈ Finset.powersetCard k (P \ F), (∏ q ∈ S, q)) ≤ (Nat.choose (P.card) k) * (2 * X) ^ k := by
      intros k hk
      have h_card_bound : ∀ S ∈ Finset.powersetCard k (P \ F), (∏ q ∈ S, q) ≤ (2 * X) ^ k := by
        intros S hS;
        exact le_trans ( Finset.prod_le_prod' fun x hx => hP x ( Finset.mem_sdiff.mp ( Finset.mem_powersetCard.mp hS |>.1 hx ) |>.1 ) |>.2.2 ) ( by norm_num [ Finset.mem_powersetCard.mp hS |>.2 ] );
      refine' le_trans ( Finset.sum_le_sum h_card_bound ) _;
      simp +zetaDelta at *;
      exact Nat.mul_le_mul_right _ ( Nat.choose_le_choose _ ( Finset.card_le_card ( Finset.sdiff_subset ) ) );
    rw [ Finset.sum_ite ];
    rw [ show ( Finset.powerset ( P \ F ) |> Finset.filter fun x => #x ≤ hmax ) = Finset.biUnion ( Finset.range ( hmax + 1 ) ) fun k => Finset.powersetCard k ( P \ F ) from ?_, Finset.sum_biUnion ];
    · simpa using Finset.sum_le_sum fun i hi => h_card_bound i <| Finset.mem_range_succ_iff.mp hi;
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by rw [ Finset.mem_powersetCard ] at hx₁ hx₂; aesop;
    · ext; simp [Finset.mem_biUnion, Finset.mem_powersetCard];
      tauto;
  have h_card_bound : (∑ k ∈ Finset.range (hmax + 1), (Nat.choose (P.card) k) * (2 * X) ^ k) ≤ (hmax + 1) * (Nat.choose (P.card) hmax) * (2 * X) ^ hmax := by
    have h_card_bound : ∀ k ∈ Finset.range (hmax + 1), (Nat.choose (P.card) k) * (2 * X) ^ k ≤ (Nat.choose (P.card) hmax) * (2 * X) ^ hmax := by
      intros k hk
      have h_binom : Nat.choose (P.card) k ≤ Nat.choose (P.card) hmax * (2 * X) ^ (hmax - k) := by
        have h_binom : ∀ k < hmax, Nat.choose (P.card) k ≤ Nat.choose (P.card) (k + 1) * (2 * X) := by
          intros k hk_lt_hmax
          have h_binom : Nat.choose (P.card) k ≤ Nat.choose (P.card) (k + 1) * (k + 1) := by
            nlinarith [ Nat.add_one_mul_choose_eq ( P.card ) k, Nat.choose_succ_succ ( P.card ) k ];
          exact h_binom.trans ( Nat.mul_le_mul_left _ ( by linarith [ show k + 1 ≤ 2 * X from by linarith [ show #P ≤ 2 * X from by
                                                                                                              exact le_trans ( Finset.card_le_card ( show P ⊆ Finset.Icc X ( 2 * X ) from fun p hp => Finset.mem_Icc.mpr ⟨ hP p hp |>.2.1, hP p hp |>.2.2 ⟩ ) ) ( by simpa ) ] ] ) );
        have h_binom : ∀ m : ℕ, k + m ≤ hmax → Nat.choose (P.card) k ≤ Nat.choose (P.card) (k + m) * (2 * X) ^ m := by
          intro m hm
          induction' m with m ih;
          · norm_num;
          · exact le_trans ( ih ( by linarith ) ) ( by rw [ pow_succ' ] ; nlinarith! [ h_binom ( k + m ) ( by linarith ), pow_pos ( by linarith : 0 < 2 * X ) m ] );
        convert h_binom ( hmax - k ) ( by rw [ add_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hk ) ] ) using 1 ; rw [ add_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hk ) ];
      exact le_trans ( Nat.mul_le_mul_right _ h_binom ) ( by rw [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hk ) ] );
    simpa [ mul_assoc ] using Finset.sum_le_sum h_card_bound;
  have h_card_bound : (∏ p ∈ F, p) ≤ (2 * X) ^ F.card := by
    exact le_trans ( Finset.prod_le_prod' fun p hp => hP p ( hFP hp ) |>.2.2 ) ( by norm_num );
  norm_cast;
  nlinarith [ Nat.zero_le ( ∏ p ∈ F, p ), Nat.zero_le ( ∑ S ∈ Finset.powerset ( P \ F ), if #S ≤ hmax then ∏ q ∈ S, q else 0 ) ]

/-
**Trivial level-set bound.**  The level set is contained in the whole
    assignment space, so its cardinality is `≤ ∏_{p∈P} p ≤ (2X)^{|P|}`.
-/
lemma levelset_card_le_pow (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) (R : ℝ) :
    ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
      ≤ (2 * (X : ℝ)) ^ P.card := by
  refine' le_trans _ _;
  exact ( ∏ p ∈ P, p : ℝ );
  · refine' le_trans ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) _;
    simp +decide [ Fintype.card_pi ];
    conv_rhs => rw [ ← Finset.prod_attach ] ;
  · exact le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun _ _ => Nat.cast_le.mpr ( hP _ ‹_› |>.2.2 ) ) ( by norm_num )

/-
Auxiliary: a prime block in `[X,2X]` has at most `2X` elements.
-/
lemma block_card_le_two_mul (X : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) : P.card ≤ 2 * X := by
  exact le_trans ( Finset.card_le_card fun p hp => Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( hP p hp |>.1 ), hP p hp |>.2.2 ⟩ ) ( by simp +arith +decide )

/-
Auxiliary (trivial-case log trick): if `(2X)^N` exceeds `N·e^{εR}` then
    `εR < N·log(2X)`.
-/
lemma exp_card_trick (NP X : ℕ) (eps R : ℝ) (hNP : 1 ≤ NP) (hX : 1 < X)
    (h : ¬ (2 * (X : ℝ)) ^ NP ≤ (NP : ℝ) * Real.exp (eps * R)) :
    eps * R < (NP : ℝ) * Real.log (2 * X) := by
  contrapose! h;
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr h ) ( Nat.cast_nonneg _ ) );
  rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ), mul_comm ];
  exact le_mul_of_one_le_left ( Real.exp_nonneg _ ) ( mod_cast hNP )

/-
Auxiliary: the chosen `Ceps` satisfies the cube lower bound used for the
    fingerprint/hot thresholds.
-/
lemma cube_rpow_ge (eps : ℝ) (hε0 : 0 < eps) :
    (7 : ℝ) * 2 ^ 21 ≤ eps ^ 4 * (((7 * 2 ^ 21 / eps ^ 4) ^ ((1 : ℝ) / 3) + 1)) ^ 3 := by
  -- Let $a = \frac{7 \cdot 2^{21}}{\epsilon^4}$.
  set a : ℝ := 7 * 2 ^ 21 / eps ^ 4;
  -- Then $((a^{1/3} + 1))^3 \geq (a^{1/3})^3 = a$.
  have h_cube : ((a ^ (1 / 3 : ℝ) + 1) ^ 3 : ℝ) ≥ a := by
    exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_le_pow_left₀ ( by positivity ) ( le_add_of_nonneg_right zero_le_one ) _ );
  rw [ ge_iff_le, div_le_iff₀ ] at h_cube <;> first | positivity | linarith;

/-
Auxiliary (fingerprint size lower bound).  For `X` past the explicit
    threshold, `εR/(4 log 2X) ≥ 208`, so the fingerprint `⌈εR/(4 log 2X)⌉ ≥ 208`.
-/
lemma Fc_ge_helper (eps Ceps : ℝ) (hε0 : 0 < eps) (hCeps : 0 < Ceps)
    (X : ℕ) (hX3 : 3 ≤ X)
    (hXbig : (1664 / (eps * Ceps)) ^ ((3 : ℝ) / 2) ≤ X)
    (R : ℝ) (hR : Ceps * (X : ℝ) ^ ((2:ℝ)/3) * (Real.log X) ^ ((4:ℝ)/3) ≤ R) :
    (208 : ℝ) ≤ eps / 2 * R / (2 * Real.log (2 * X)) := by
  -- By simplifying, we can see that the inequality holds.
  have h_simplified : 208 ≤ (eps * Ceps / 8) * (X : ℝ) ^ (2 / 3 : ℝ) * (Real.log X) ^ (1 / 3 : ℝ) := by
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.one_le_rpow ( Real.le_log_iff_exp_le ( by positivity ) |>.2 _ ) ( by positivity ) ) ( by positivity ) );
    · have h_exp : (X : ℝ) ^ (2 / 3 : ℝ) ≥ (1664 / (eps * Ceps)) := by
        exact le_trans ( by rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) hXbig ( by positivity ) )
      generalize_proofs at *; (
      rw [ ge_iff_le, div_le_iff₀ ] at h_exp <;> first | positivity | linarith;);
    · exact le_trans ( Real.exp_one_lt_d9.le ) ( by norm_num; linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] );
  rw [ le_div_iff₀ ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ];
  rw [ Real.log_mul ( by positivity ) ( by positivity ) ];
  rw [ show ( 4 / 3 : ℝ ) = 1 + 1 / 3 by norm_num, Real.rpow_add ] at hR <;> norm_num at *;
  · nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by norm_cast; linarith : ( X : ℝ ) ≥ 2 ), mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by norm_cast; linarith : ( X : ℝ ) ≥ 2 ) ) hε0.le ];
  · exact Real.log_pos <| by norm_cast; linarith;

/-
Auxiliary (hot-count upper bound).  `R/T ≤ εR/log 2X`, where
    `T = Fc³/(2¹¹X²)/7` and `Fc ≥ εR/(4 log 2X)`, given the cube bound on `Ceps`.
-/
lemma hmax_bound_helper (eps Ceps : ℝ) (hε0 : 0 < eps)
    (hcube : (7 : ℝ) * 2 ^ 21 ≤ eps ^ 4 * Ceps ^ 3)
    (X : ℕ) (hX3 : 3 ≤ X) (R : ℝ)
    (hR : Ceps * (X : ℝ) ^ ((2:ℝ)/3) * (Real.log X) ^ ((4:ℝ)/3) ≤ R)
    (Fc : ℕ) (hFc : eps / 2 * R / (2 * Real.log (2 * X)) ≤ (Fc : ℝ)) :
    R / ((Fc : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7) ≤ eps * R / Real.log (2 * X) := by
  -- Using the bound from `Fc_ge_helper`, we know that `Fc ≥ (eps * R) / (4 * Real.log (2 * X))`.
  have hFc_bound : (Fc : ℝ) ≥ (eps * R) / (4 * Real.log (2 * X)) := by
    convert hFc.ge using 1 ; ring;
  by_cases hR_pos : 0 < R;
  · have hR_bound : R ^ 3 ≥ Ceps ^ 3 * (X : ℝ) ^ 2 * (Real.log X) ^ 4 := by
      have hR_bound : R ^ 3 ≥ (Ceps * (X : ℝ) ^ (2 / 3 : ℝ) * (Real.log X) ^ (4 / 3 : ℝ)) ^ 3 := by
        gcongr;
        by_cases hCeps_pos : 0 < Ceps;
        · exact mul_nonneg ( mul_nonneg hCeps_pos.le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) _ );
        · nlinarith [ pow_pos hε0 4, pow_nonneg ( neg_nonneg.mpr ( le_of_not_gt hCeps_pos ) ) 3 ];
      convert hR_bound using 1 ; ring_nf;
      norm_num only [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), ← Real.rpow_mul ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ];
    have hL_bound : (Real.log (2 * X)) ^ 4 ≤ 16 * (Real.log X) ^ 4 := by
      have hL_bound : Real.log (2 * X) ≤ 2 * Real.log X := by
        rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Nat.pow_le_pow_left hX3 2 ];
      exact le_trans ( pow_le_pow_left₀ ( Real.log_nonneg ( by norm_cast; linarith ) ) hL_bound 4 ) ( by ring_nf; norm_num );
    have h_final_bound : 7 * 2 ^ 17 * (X : ℝ) ^ 2 * (Real.log (2 * X)) ^ 4 ≤ eps ^ 4 * R ^ 3 := by
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left hR_bound <| by positivity );
      nlinarith [ show 0 < ( X : ℝ ) ^ 2 * Real.log X ^ 4 by exact mul_pos ( by positivity ) ( by exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _ ) ];
    rw [ div_div, div_le_div_iff₀ ];
    · rw [ mul_div, le_div_iff₀ ] <;> try positivity;
      have h_final_bound : (Fc : ℝ) ^ 3 ≥ (eps * R / (4 * Real.log (2 * X))) ^ 3 := by
        exact pow_le_pow_left₀ ( div_nonneg ( mul_nonneg hε0.le hR_pos.le ) ( mul_nonneg zero_le_four ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ) hFc_bound 3;
      refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_final_bound <| by positivity );
      field_simp;
      rw [ le_div_iff₀ ( pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _ ) ] ; nlinarith [ Real.log_pos ( by norm_cast; linarith : ( 1 :ℝ ) < 2 * X ) ];
    · rcases Fc with ( _ | Fc ) <;> norm_num at *;
      · exact not_le_of_gt ( div_pos ( mul_pos ( half_pos hε0 ) hR_pos ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ) hFc;
      · positivity;
    · exact Real.log_pos ( by norm_cast; linarith );
  · contrapose! hR;
    exact lt_of_le_of_lt ( le_of_not_gt hR_pos ) ( mul_pos ( mul_pos ( show 0 < Ceps by exact lt_of_not_ge fun h => by nlinarith [ pow_pos hε0 4, pow_nonneg ( neg_nonneg.mpr h ) 3 ] ) ( by positivity ) ) ( by exact Real.rpow_pos_of_pos ( Real.log_pos ( by norm_cast; linarith ) ) _ ) )

set_option maxHeartbeats 1000000 in
/-- **Theorem C** (`30 §1`).  For every `ε ∈ (0,1)` there are `Cε, X₀` such that
    for `X ≥ X₀`, any **nonempty** prime block `P ⊆ [X,2X]`, and any
    `R ≥ R_C := Cε · X^{2/3} · (log X)^{4/3}`, the full level set satisfies
    `#{a : Q_P(a) ≤ R} ≤ N · exp(ε R)` (`N = |P|`).

    **Faithfulness note (verification finding).**  The hypothesis `1 ≤ P.card`
    (i.e. `P` nonempty) is *necessary* and was missing from note 30's statement:
    for `P = ∅` the block has exactly one (empty) assignment with `Q_P = 0 ≤ R`,
    so the count is `1`, while the right-hand side `N · e^{εR} = 0 · e^{εR} = 0`.
    The paper tacitly works with substantial blocks (`N ≥ X/(2 log X) ≥ 2` in the
    Irving-good regime), so requiring `P` nonempty is faithful and minimal. -/
theorem fingerprint_count
    (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ (Ceps X0 : ℝ), 0 < Ceps ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (_hPne : 1 ≤ P.card)
          (R : ℝ), Ceps * (X:ℝ)^((2:ℝ)/3) * (Real.log X)^((4:ℝ)/3) ≤ R →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ (P.card : ℝ) * Real.exp (eps * R) := by
  obtain ⟨ C2, X02, hC2, hX02, Hent2 ⟩ := entropy_inequality2 ( eps / 2 ) ( by linarith ) ( by linarith );
  refine' ⟨ Max.max C2 ( ( 7 * 2 ^ 21 / eps ^ 4 ) ^ ( 1 / 3 : ℝ ) + 1 ), Max.max X02 ( Max.max 3 ( ( 1664 / ( eps * Max.max C2 ( ( 7 * 2 ^ 21 / eps ^ 4 ) ^ ( 1 / 3 : ℝ ) + 1 ) ) ) ^ ( 3 / 2 : ℝ ) ) ), _, _, _ ⟩;
  · positivity;
  · positivity;
  · intro X hX P _ hP hPne R hR;
    by_cases htriv : (2 * (X : ℝ)) ^ P.card ≤ (P.card : ℝ) * Real.exp (eps * R);
    · refine' le_trans _ htriv;
      convert levelset_card_le_pow X P hP R using 1;
    · obtain ⟨Fc, hFc⟩ : ∃ Fc : ℕ, 208 ≤ Fc ∧ eps / 2 * R / (2 * Real.log (2 * X)) ≤ Fc ∧ Fc ≤ eps / 2 * R / (2 * Real.log (2 * X)) + 1 ∧ Fc ≤ P.card := by
        refine' ⟨ Nat.ceil ( eps / 2 * R / ( 2 * Real.log ( 2 * X ) ) ), _, _, _, _ ⟩;
        · have := Fc_ge_helper eps ( Max.max C2 ( ( 7 * 2 ^ 21 / eps ^ 4 ) ^ ( 1 / 3 : ℝ ) + 1 ) ) hε0 ( by positivity ) X ( by
            exact_mod_cast le_trans ( le_max_left _ _ ) ( le_trans ( le_max_right _ _ ) hX ) ) ( by
            exact le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hX ) R ( by
            exact hR );
          exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( eps / 2 * R / ( 2 * Real.log ( 2 * X ) ) ) ] );
        · exact Nat.le_ceil _;
        · exact Nat.ceil_lt_add_one ( div_nonneg ( mul_nonneg ( by positivity ) ( by exact le_trans ( by positivity ) hR ) ) ( mul_nonneg zero_le_two ( Real.log_nonneg ( by norm_cast; linarith [ show X ≥ 1 by exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at * ) ] ) ) ) ) |> le_of_lt;
        · have h_ceil_le_P : eps * R < P.card * Real.log (2 * X) := by
            apply exp_card_trick P.card X eps R hPne (by
            norm_num +zetaDelta at *;
            linarith) htriv;
          exact Nat.ceil_le.mpr ( by rw [ div_le_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( 2 * X : ℝ ) > 1 by norm_cast; linarith [ show X > 0 from Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) hX ) ] ) ] );
      obtain ⟨F, hFP, hFcard, hFmin⟩ : ∃ F ⊆ P, F.card = Fc ∧ ∀ p ∈ F, ∀ q ∈ P \ F, p < q := exists_lower_subset P Fc (by
      linarith);
      obtain ⟨hmax, hhmax⟩ : ∃ hmax : ℕ, R / ((Fc : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7) < (hmax : ℝ) + 1 ∧ hmax ≤ P.card ∧ (hmax : ℝ) ≤ 7 * R * (2 ^ 11 * (X : ℝ) ^ 2) / (Fc : ℝ) ^ 3 := by
        refine' ⟨ Nat.floor ( R / ( ( Fc : ℝ ) ^ 3 / ( 2 ^ 11 * X ^ 2 ) / 7 ) ), _, _, _ ⟩;
        · exact Nat.lt_floor_add_one _;
        · refine' Nat.floor_le_of_le _;
          rw [ div_div_eq_mul_div, div_le_iff₀ ];
          · have := hmax_bound_helper eps ( Max.max C2 ( ( 7 * 2 ^ 21 / eps ^ 4 ) ^ ( 1 / 3 : ℝ ) + 1 ) ) hε0 ( by
              exact le_trans ( cube_rpow_ge eps hε0 ) ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( le_max_right _ _ ) _ ) ( by positivity ) ) ) X ( by
              exact_mod_cast le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hX ) R hR Fc ( by
              lia );
            rw [ div_div_eq_mul_div, div_le_iff₀ ] at this;
            · refine' le_trans this _;
              gcongr;
              rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_of_le_right <| le_max_left _ _ ) hX ] ) ];
              have := exp_card_trick P.card X eps R ( by linarith ) ( by linarith [ show X ≥ 3 by exact_mod_cast le_trans ( le_max_of_le_right <| le_max_left _ _ ) hX ] ) htriv;
              linarith;
            · exact div_pos ( pow_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ show X > 0 from Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) hX ) ] ) ) ) );
          · exact div_pos ( pow_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ show X > 0 from Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) hX ) ] ) ) ) );
        · have hratio_nonneg :
              0 ≤ R / ((Fc : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7) := by
            have hR_nonneg : 0 ≤ R := le_trans (by positivity) hR
            have hFc_pos : 0 < (Fc : ℝ) := by
              exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 208) hFc.1
            exact div_nonneg hR_nonneg (by positivity)
          calc
            (Nat.floor (R / ((Fc : ℝ) ^ 3 /
                (2 ^ 11 * (X : ℝ) ^ 2) / 7)) : ℝ)
                ≤ R / ((Fc : ℝ) ^ 3 /
                    (2 ^ 11 * (X : ℝ) ^ 2) / 7) := Nat.floor_le hratio_nonneg
            _ = 7 * R * (2 ^ 11 * (X : ℝ) ^ 2) / (Fc : ℝ) ^ 3 := by
              field_simp
      refine le_trans ( decoding_card_bound X ( by
        exact Nat.one_le_iff_ne_zero.mpr ( by rintro rfl; norm_num at * ) ) P F ( by
        exact hP ) hFP ( by
        grind +splitIndPred ) hFmin ( ( Fc : ℝ ) ^ 3 / ( 2 ^ 11 * ( X : ℝ ) ^ 2 ) / 7 ) R ( by
        rw [ hFcard ] ) ( by
        exact div_pos ( div_pos ( pow_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ show X > 0 from Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) hX ) ] ) ) ) ) ) ( by norm_num ) ) hmax ( by
        linarith ) ( by
        grind ) ) ?_;
      have hent := Hent2 X (by
        exact le_trans (le_max_left _ _) hX) P.card Fc hmax R (by
        exact le_trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            (by positivity)) hR) (by
        linarith) (block_card_le_two_mul X P hP) (by
        linarith) (by
        linarith) (by
        linarith) hhmax.2.2
      rw [hFcard]
      refine hent.trans_eq ?_
      congr 2
      ring

end SBEEFingerprint
