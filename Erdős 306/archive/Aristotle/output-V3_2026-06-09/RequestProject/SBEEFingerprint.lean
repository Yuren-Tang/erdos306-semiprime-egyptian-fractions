/-
# SBEE Fingerprint: Theorem C via its decomposition (note 32)

This file formalizes the decomposition of **Theorem C** (`fingerprint_count`)
described in `32 Theorem C Decomposition - Phase Identity and Cold Rigidity.md`.

The deterministic dispersion engine is already fully machine-verified in
`SBEEDispersion.lean` (`lemmaD`, `dispersion_residue_count`,
`dispersion_energy_bound`, `phase_sub_le`, …).  Here we build, in order:

* `tEnergy` — the per-vertex fingerprint energy `t_q(w) = ∑_{p∈F} (H_{pq}/pq)²`.
* `phaseP1`  — **Lemma P1** (phase identity / the bridge `crtRepr ↔ phase`).
* `phase_sq_bound` — the squared triangle bound combining P1 with `phase_sub_le`.
* `coldRigidity` — **Lemma P2** (cold rigidity): for `q ∉ F`, at most one residue
  `w` has `t_q(w) < G_F/7`.  This is the novel analytic core.

Notation (note 32): for primes `p, q`, an assignment `a : (p:ℕ) → ZMod p`, and a
candidate residue `w : ZMod q`, the centered integer representatives are
`ZMod.valMinAbs` (the rep in `(-n/2, n/2]`), and `H_{pq}(a_p, w) = crtRepr p q (a p) w`.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEDispersion

open Finset
open SBEEDispersion

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

/-! ## Lemma P1 — the phase identity (`32` Sub-lemma 1)

For primes `p ≠ q`, with centered integer reps `ã_p = valMinAbs (a p)` and
`w̃ = valMinAbs w`, the reciprocal phase of `ã_p − w̃` is controlled by
`|H_{pq}|/(pq)`:
`phase (ã_p − w̃) q p ≤ |H_{pq}(a_p,w)|/(pq) + 1/(2p)`.

Proof (note 32): `H := crtRepr p q (a p) w` satisfies `H ≡ w̃ (mod q)`, so
`H = w̃ + v q` for an integer `v`; and `H ≡ ã_p (mod p)`, giving
`v ≡ (ã_p − w̃) q̄ (mod p)`.  Since `phase E q p = ‖E q̄ / p‖` depends only on
`E mod p`, `phase (ã_p − w̃) q p = ‖v/p‖`.  Finally
`v/p = H/(pq) − w̃/(pq)`, so `‖v/p‖ ≤ |H|/(pq) + |w̃|/(pq) ≤ |H|/(pq) + 1/(2p)`
using `|w̃| ≤ q/2`. -/

lemma phaseP1 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a : (p : ℕ) → ZMod p) (w : ZMod q) :
    phase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w) q p
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
        convert crtRepr_congr_left p q ( a p ) w _ _ _;
        · convert ZMod.coe_valMinAbs ( a p );
        · exact hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h;
        · exact hp.pos;
        · exact hq.pos;
      rw [ Int.ediv_mul_cancel ];
      · simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        grind;
      · have h_mod : (H : ZMod q) = w := by
          convert crtRepr_congr_right p q ( a p ) w _ _ _ using 1;
          · exact hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h;
          · exact hp.pos;
          · exact hq.pos;
        rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop;
    have h_mod : (H - wtilde) / q ≡ E * qbar [ZMOD p] := by
      simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
      simp +zetaDelta at *;
      rw [ ← h_mod, mul_assoc, mul_inv_cancel₀ ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact fun h => hpq <| by have := Nat.prime_dvd_prime_iff_eq hp hq; tauto ), mul_one ];
    exact h_mod.dvd;
  -- So |x - round x| = |(v:ℝ)/p - round ((v:ℝ)/p)|.
  have h_abs : phase E q p = |(H - wtilde : ℝ) / (p * q) - round ((H - wtilde : ℝ) / (p * q))| := by
    -- Substitute hk into the expression for x - round x.
    have h_subst : (E : ℝ) * qbar / p = (H - wtilde : ℝ) / (p * q) + k := by
      rw [ div_add', div_eq_div_iff ] <;> norm_cast <;> simp_all +decide [ hp.ne_zero, hq.ne_zero ];
      rw [ ← Int.ediv_mul_cancel ( show ( q : ℤ ) ∣ H - wtilde from ?_ ) ] ; linear_combination hk * p * q;
      have h_div : (crtRepr p q (a p) w : ZMod q) = w := by
        convert crtRepr_congr_right p q ( a p ) w _ _ _ using 1;
        · exact hp.coprime_iff_not_dvd.mpr fun h => hpq <| Nat.prime_dvd_prime_iff_eq hp hq |>.1 h;
        · exact hp.pos;
        · exact hq.pos;
      haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
      aesop;
    unfold phase;
    simp +zetaDelta at *;
    rw [ h_subst, round_add_intCast ] ; norm_num;
  -- So |(v:ℝ)/p - round ((v:ℝ)/p)| ≤ |(v:ℝ)/p|.
  have h_abs_le : |(H - wtilde : ℝ) / (p * q) - round ((H - wtilde : ℝ) / (p * q))| ≤ |(H - wtilde : ℝ) / (p * q)| := by
    convert round_le _ 0 using 1;
    · norm_num;
    · infer_instance;
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

Combining `phase_sub_le` with `phaseP1` applied to `w` and `w'`:
`phase (w̃' − w̃) q p ≤ |H_w|/(pq) + |H_{w'}|/(pq) + 1/p`, and then
`(α+β+γ)² ≤ 3(α²+β²+γ²)` gives the per-prime squared bound. -/

lemma phase_sq_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (a : (p : ℕ) → ZMod p) (w w' : ZMod q) :
    (phase (ZMod.valMinAbs w' - ZMod.valMinAbs w) q p) ^ 2
      ≤ 3 * tterm a q w p + 3 * tterm a q w' p + 3 / (p : ℝ) ^ 2 := by
  -- Apply `phase_sub_le` with A := ZMod.valMinAbs (a p) - ZMod.valMinAbs w and B := ZMod.valMinAbs (a p) - ZMod.valMinAbs w'.
  have h_phase_sub_le : phase (w'.valMinAbs - w.valMinAbs) q p ≤ phase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w) q p + phase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w') q p := by
    convert phase_sub_le ( ( a p |> ZMod.valMinAbs ) - w.valMinAbs ) ( ( a p |> ZMod.valMinAbs ) - w'.valMinAbs ) q p using 1 ; ring;
  -- Apply `phaseP1` to w and w'.
  have h_phaseP1_w : phase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w) q p ≤ |(crtRepr p q (a p) w : ℝ)| / ((p : ℝ) * q) + 1 / (2 * p) := by
    convert phaseP1 p q hp hq hpq a w using 1
  have h_phaseP1_w' : phase (ZMod.valMinAbs (a p) - ZMod.valMinAbs w') q p ≤ |(crtRepr p q (a p) w' : ℝ)| / ((p : ℝ) * q) + 1 / (2 * p) := by
    convert phaseP1 p q hp hq hpq a w' using 1;
  -- Set bw := |(crtRepr p q (a p) w : ℝ)|/((p:ℝ)*q) and bw' := |(crtRepr p q (a p) w' : ℝ)|/((p:ℝ)*q).
  set bw := |(crtRepr p q (a p) w : ℝ)| / ((p : ℝ) * q)
  set bw' := |(crtRepr p q (a p) w' : ℝ)| / ((p : ℝ) * q);
  -- By definition of $tterm$, we have $tterm a q w p = bw^2$ and $tterm a q w' p = bw'^2$.
  have htterm : tterm a q w p = bw^2 ∧ tterm a q w' p = bw'^2 := by
    unfold tterm;
    grind;
  -- By combining the inequalities from `phase_sub_le`, `phaseP1_w`, and `phaseP1_w'`, we get:
  have h_combined : phase (w'.valMinAbs - w.valMinAbs) q p ≤ bw + bw' + 1 / (p : ℝ) := by
    convert le_trans h_phase_sub_le ( add_le_add h_phaseP1_w h_phaseP1_w' ) using 1 ; ring;
  -- By squaring both sides of the inequality from `h_combined`, we get:
  have h_squared : phase (w'.valMinAbs - w.valMinAbs) q p ^ 2 ≤ (bw + bw' + 1 / (p : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ ( phase_nonneg _ _ _ ) h_combined 2;
  refine le_trans h_squared ?_;
  rw [ htterm.1, htterm.2 ] ; ring_nf;
  nlinarith only [ sq_nonneg ( bw - bw' ), sq_nonneg ( bw - ( p : ℝ ) ⁻¹ ), sq_nonneg ( bw' - ( p : ℝ ) ⁻¹ ) ]

/-! ## Lemma P2 — cold rigidity (`32` Sub-lemma 2)

For `q ∉ F`, at most one residue `w` has `t_q(w) < G_F/7` where
`G_F = |F|³/(2¹¹ X²)`.  The contradiction (using `dispersion_energy_bound`)
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
  have h_sum_bound : ∑ p ∈ F, (phase E q p) ^ 2 ≤ 3 * tEnergy F a q w + 3 * tEnergy F a q w' + 3 * (F.card : ℝ) / (X : ℝ) ^ 2 := by
    have h_sum_bound : ∀ p ∈ F, (phase E q p) ^ 2 ≤ 3 * tterm a q w p + 3 * tterm a q w' p + 3 / (p : ℝ) ^ 2 := by
      grind +suggestions;
    refine le_trans ( Finset.sum_le_sum h_sum_bound ) ?_;
    norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul, tEnergy ];
    exact le_trans ( Finset.sum_le_sum fun x hx => show ( 3 : ℝ ) / x ^ 2 ≤ 3 / X ^ 2 by gcongr ; linarith [ hF x hx ] ) ( by norm_num; ring_nf; norm_num );
  have h_sum_bound : (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) ≤ 3 * tEnergy F a q w + 3 * tEnergy F a q w' + 3 * (F.card : ℝ) / (X : ℝ) ^ 2 := by
    convert dispersion_energy_bound X F hF ( by linarith ) q hq hqF hq2X E hE_zero hE_abs.1 hE_abs.2 |> le_trans <| h_sum_bound using 1;
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
    push_neg at hhot
    have hcoldA : tEnergy F a q (a q) < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7 :=
      hT ▸ hhot
    -- `q ∉ Hot(b)` too, since the hot sets coincide.
    have hnotHotB : q ∉ (P \ F).filter (fun q => T ≤ tEnergy F b q (b q)) := by
      rw [← hHot]; exact fun hmem => hhot.not_ge (Finset.mem_filter.mp hmem).2
    have hcoldB : tEnergy F b q (b q) < (F.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) / 7 := by
      by_contra hc; push_neg at hc
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
        · convert h_bound'.le using 1 ; ring;
      convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_bound' zero_le_two ) ( Real.log_nonneg <| show ( 2 * X : ℝ ) ≥ 1 by linarith ) using 1 ; ring;
      grind;
    -- Use the provided inequalities to bound the terms further.
    have h_bound'' : R^3 ≥ 2^21 * 7 * X^2 * (Real.log X)^4 / eps^4 := by
      have h_bound'' : R^3 ≥ ((2^21 * 7 / eps^4) ^ ((1:ℝ)/3) * X^(2/3 : ℝ) * (Real.log X)^(4/3 : ℝ))^3 := by
        gcongr;
        exact le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) ( by exact Real.rpow_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) _ ) ) hR;
      convert h_bound'' using 1 ; ring;
      repeat rw [ ← Real.rpow_natCast ] ; repeat rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring;
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

end SBEEFingerprint