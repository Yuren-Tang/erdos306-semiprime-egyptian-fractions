import RequestProject.BernoulliFourier
import RequestProject.GlobalControl
import RequestProject.GlobalControlG7

open Finset BigOperators Classical Real GlobalControl

noncomputable section

namespace CircleMethod

/-!
# Phase C arc energy: the C2 → Q_E bridge (note 35)

`product_charFun_bound` bounds the character product by
`exp(-c · ∑_e sin²(π h/e))`.  The minor-arc analysis needs this in terms of the
**quadratic CRT energy** `Q_E(h) = ∑_{e∈E} ‖h/e‖²` (nearest-integer distance),
because that is what couples to the global control energy `Qctrl` (via the CRT
bijection `h ↔ a`).  The bridge is the elementary pointwise inequality
`sin²(π x) ≥ 4 ‖x‖²` (Jordan), giving `∑ sin² ≥ 4 Q_E`.

`GlobalControl.nndist1 x = |x - round x| = ‖x‖` is reused as the nearest-integer
distance.
-/

/-- The quadratic CRT energy `Q_E(h) = ∑_{e∈E} ‖h/e‖²`, using the nearest-integer
distance `nndist1` (this is the faithful version; `BernoulliFourier`'s
`quadraticCRTEnergy` was a placeholder). -/
def QE (E : Finset ℕ) (h : ℕ) : ℝ :=
  ∑ e ∈ E, (GlobalControl.nndist1 ((h : ℝ) / (e : ℝ))) ^ 2

/-- **Jordan bridge (per term).**  `sin²(π x) ≥ 4 ‖x‖²` where `‖x‖ = |x - round x|`. -/
lemma sin_sq_pi_ge_four_nndist_sq (x : ℝ) :
    4 * (GlobalControl.nndist1 x) ^ 2 ≤ Real.sin (Real.pi * x) ^ 2 := by
  set n := round x with hn
  set d := x - (n : ℝ) with hd
  have hdabs : |d| ≤ 1 / 2 := by rw [hd, hn]; exact abs_sub_round x
  -- nndist1 x = |d|
  have hnd : GlobalControl.nndist1 x = |d| := by
    unfold GlobalControl.nndist1; rw [hd, hn]
  -- period: sin²(πx) = sin²(πd)
  have hper : Real.sin (Real.pi * x) ^ 2 = Real.sin (Real.pi * d) ^ 2 := by
    have key : ∀ θ : ℝ, 2 * Real.sin θ ^ 2 = 1 - Real.cos (2 * θ) := by
      intro θ; rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq θ]
    have hcos : Real.cos (2 * (Real.pi * x)) = Real.cos (2 * (Real.pi * d)) := by
      have hxd : 2 * (Real.pi * x) = 2 * (Real.pi * d) + (n : ℝ) * (2 * Real.pi) := by
        rw [hd]; ring
      rw [hxd, Real.cos_add_int_mul_two_pi]
    have e1 := key (Real.pi * x)
    have e2 := key (Real.pi * d)
    linarith [e1, e2, hcos]
  -- 4|d|² ≤ sin²(πd): from 2|d| ≤ |sin(πd)| (Jordan on |d| ∈ [0,1/2])
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi * |d|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos, hdabs])
  have hjbase : 2 * |d| ≤ Real.sin (Real.pi * |d|) := by
    have htpos : (0 : ℝ) ≤ Real.pi * |d| := by positivity
    have htle : Real.pi * |d| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hdabs]
    have hb := Real.mul_le_sin htpos htle
    have hsimp : (2 / Real.pi) * (Real.pi * |d|) = 2 * |d| := by field_simp
    rwa [hsimp] at hb
  have heq : Real.sin (Real.pi * |d|) = |Real.sin (Real.pi * d)| := by
    rcases abs_cases d with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1, abs_of_nonneg (h1 ▸ hsin_nonneg)]
    · rw [h1]
      have hneg : Real.pi * -d = -(Real.pi * d) := by ring
      have hle0 : Real.sin (Real.pi * d) ≤ 0 := by
        have h0 := hsin_nonneg; rw [h1, hneg, Real.sin_neg] at h0; linarith
      rw [hneg, Real.sin_neg, abs_of_nonpos hle0]
  have hjord : 2 * |d| ≤ |Real.sin (Real.pi * d)| := heq ▸ hjbase
  have hsabs : (Real.sin (Real.pi * d)) ^ 2 = |Real.sin (Real.pi * d)| ^ 2 := (sq_abs _).symm
  rw [hper, hnd, hsabs]
  nlinarith [hjord, abs_nonneg d, abs_nonneg (Real.sin (Real.pi * d))]

/-- **C2 in Q_E form.**  The Bernoulli character product decays as
`exp(-8 θ₀(1-θ₀) · Q_E(h))`. -/
theorem product_charFun_bound_QE (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ ≤ 1 / 2)
    (E : Finset ℕ) (θ : ℕ → ℝ)
    (hθ_lb : ∀ e ∈ E, θ₀ ≤ θ e) (hθ_ub : ∀ e ∈ E, θ e ≤ 1 - θ₀) (h : ℕ) :
    ‖∏ e ∈ E, bernoulliCharFun (θ e) (h / (e : ℝ))‖ ≤
      Real.exp (-(8 * θ₀ * (1 - θ₀)) * QE E h) := by
  refine le_trans (product_charFun_bound θ₀ hθ₀ hθ₀' E θ hθ_lb hθ_ub h) ?_
  apply Real.exp_le_exp.mpr
  have hc : 0 ≤ 2 * θ₀ * (1 - θ₀) := by nlinarith
  -- ∑ sin² ≥ 4 Q_E  ⇒  -(2c)∑sin² ≤ -(8c) Q_E
  have hsum : 4 * QE E h ≤ ∑ e ∈ E, Real.sin (Real.pi * (h : ℝ) / (e : ℝ)) ^ 2 := by
    rw [QE, Finset.mul_sum]
    refine Finset.sum_le_sum (fun e _ => ?_)
    have := sin_sq_pi_ge_four_nndist_sq ((h : ℝ) / (e : ℝ))
    calc 4 * (GlobalControl.nndist1 ((h : ℝ) / (e : ℝ))) ^ 2
        ≤ Real.sin (Real.pi * ((h : ℝ) / (e : ℝ))) ^ 2 := this
      _ = Real.sin (Real.pi * (h : ℝ) / (e : ℝ)) ^ 2 := by rw [mul_div_assoc]
  nlinarith [hsum, hc, mul_le_mul_of_nonneg_left hsum hc]

/-- The Fourier-identity product factor equals the Bernoulli characteristic
function at `h/e` (uses `e ∣ L` so `(L/e)/L = 1/e`). -/
lemma charfactor_eq (th : ℝ) (h e L : ℕ) (he0 : 0 < e) (heL : e ∣ L) (hL : 0 < L) :
    (th : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
        + (1 - th)
      = bernoulliCharFun th ((h : ℝ) / (e : ℝ)) := by
  unfold bernoulliCharFun
  have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hcast : ((L / e : ℕ) : ℂ) = (L : ℂ) / (e : ℂ) := by
    rw [Nat.cast_div heL heC]
  have harg : 2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ)
      = 2 * (Real.pi : ℂ) * (((h : ℝ) / (e : ℝ) : ℝ) : ℂ) * Complex.I := by
    rw [hcast]; push_cast; field_simp
  rw [harg]; push_cast; ring

/-- **C4 minor-arc norm bound.**  Over any frequency set `S`, the norm of the
Fourier-identity sum is bounded by the energy sum `∑ exp(-c·Q_E(h))`.  This is the
triangle-inequality half of the minor arc; the remaining step (bounding that
energy sum via the `h ↔ a` CRT bijection and `global_control_partition`) is C4's
arithmetic core. -/
theorem minor_arc_norm_le (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ ≤ 1 / 2)
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (hθ_lb : ∀ e ∈ E, θ₀ ≤ theta e) (hθ_ub : ∀ e ∈ E, theta e ≤ 1 - θ₀)
    (heL : ∀ e ∈ E, e ∣ L) (he0 : ∀ e ∈ E, 0 < e) (hL : 0 < L) (S : Finset ℕ) :
    ‖∑ h ∈ S,
        (∏ e ∈ E, ((theta e : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
            + (1 - theta e)))
        * Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖
      ≤ ∑ h ∈ S, Real.exp (-(8 * θ₀ * (1 - θ₀)) * QE E h) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum (fun h _ => ?_)
  rw [norm_mul]
  -- the target phase has norm 1 (purely imaginary exponent)
  have hphase : ‖Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ))).re = 0 := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hre, Real.exp_zero]
  rw [hphase, mul_one]
  -- rewrite the product factors as bernoulliCharFun, then apply the QE bound
  have hprod : (∏ e ∈ E, ((theta e : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
        + (1 - theta e)))
      = ∏ e ∈ E, bernoulliCharFun (theta e) ((h : ℝ) / (e : ℝ)) := by
    refine Finset.prod_congr rfl (fun e he => ?_)
    exact charfactor_eq (theta e) h e L (he0 e he) (heL e he) hL
  rw [hprod]
  exact product_charFun_bound_QE θ₀ hθ₀ hθ₀' E theta hθ_lb hθ_ub h

/-! ## Per-pair CRT energy bridge (C4 core)

The nearest-integer distance `‖h/(pq)‖` equals `|crtRepr(h mod p, h mod q)|/(pq)`.
This is the per-control-pair identity behind `Q_E(h) = Q_ctrl(a(h))` (note 35 C2/C4).
-/

/-- If an integer `t` is within `1/2` of `x`, then `‖x‖ = |x - t|`. -/
lemma nndist1_eq_of_int (x : ℝ) (t : ℤ) (hx : |x - (t : ℝ)| ≤ 1 / 2) :
    GlobalControl.nndist1 x = |x - (t : ℝ)| := by
  unfold GlobalControl.nndist1
  rcases eq_or_ne (round x) t with heq | hne
  · rw [heq]
  · -- round x ≠ t : both are within 1/2 of x, so x is equidistant and both = 1/2
    have ha : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have hge : (1 : ℝ) ≤ |((round x : ℝ)) - (t : ℝ)| := by
      have hz : ((round x - t : ℤ)) ≠ 0 := sub_ne_zero.mpr hne
      have h1 : (1 : ℤ) ≤ |round x - t| := Int.one_le_abs hz
      calc (1 : ℝ) ≤ |((round x - t : ℤ) : ℝ)| := by exact_mod_cast h1
        _ = |((round x : ℝ)) - (t : ℝ)| := by push_cast; ring_nf
    have htri : |((round x : ℝ)) - (t : ℝ)| ≤ |x - (round x : ℝ)| + |x - (t : ℝ)| := by
      have hh := abs_sub_le (round x : ℝ) x (t : ℝ)
      rw [abs_sub_comm (round x : ℝ) x] at hh
      linarith [hh]
    -- 1 ≤ a + b ≤ 1, a,b ≤ 1/2 ⟹ a = b = 1/2
    linarith [ha, hx, hge, htri]

/-- **Per-pair CRT energy identity.**  For distinct primes `p, q`,
`‖h/(pq)‖ = |crtRepr p q (h mod p) (h mod q)| / (pq)`. -/
lemma nndist1_eq_crtRepr_div (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (h : ℕ) :
    GlobalControl.nndist1 ((h : ℝ) / ((p : ℝ) * (q : ℝ)))
      = |(crtRepr p q (h : ZMod p) (h : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := hq.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  set m : ℤ := crtRepr p q (h : ZMod p) (h : ZMod q) with hm
  -- p ∣ (h - m) and q ∣ (h - m)
  have hdvdp : (p : ℤ) ∣ ((h : ℤ) - m) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcl : (m : ZMod p) = (h : ZMod p) := crtRepr_congr_left p q _ _ hcop hp0 hq0
    push_cast [hcl]
    rw [sub_eq_zero]
  have hdvdq : (q : ℤ) ∣ ((h : ℤ) - m) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcr : (m : ZMod q) = (h : ZMod q) := crtRepr_congr_right p q _ _ hcop hp0 hq0
    push_cast [hcr]
    rw [sub_eq_zero]
  have hcopZ : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
  have hdvd : ((p : ℤ) * q) ∣ ((h : ℤ) - m) := hcopZ.mul_dvd hdvdp hdvdq
  obtain ⟨t, ht⟩ := hdvd
  -- x - t = m / (pq), and |m| ≤ pq/2, so |x - t| ≤ 1/2
  have hpqR : (0 : ℝ) < (p : ℝ) * (q : ℝ) := by positivity
  have hxt : (h : ℝ) / ((p : ℝ) * q) - (t : ℝ) = (m : ℝ) / ((p : ℝ) * q) := by
    have : (h : ℝ) - (m : ℝ) = ((p : ℝ) * q) * (t : ℝ) := by exact_mod_cast ht
    field_simp
    linarith [this]
  have hmle : |(m : ℝ)| ≤ ((p : ℝ) * q) / 2 := by
    have hint : |m| ≤ ((p * q : ℕ) : ℤ) / 2 := crtRepr_abs_le p q _ _ hcop hp0 hq0
    have h2 : 2 * |m| ≤ ((p * q : ℕ) : ℤ) := by
      set a := |m| with ha
      omega
    have h2R : 2 * |(m : ℝ)| ≤ (p : ℝ) * q := by
      rw [← Int.cast_abs]
      calc 2 * ((|m| : ℤ) : ℝ) = ((2 * |m| : ℤ) : ℝ) := by push_cast; ring
        _ ≤ (((p * q : ℕ) : ℤ) : ℝ) := by exact_mod_cast h2
        _ = (p : ℝ) * q := by push_cast; ring
    linarith [h2R]
  have habs : |(h : ℝ) / ((p : ℝ) * q) - (t : ℝ)| ≤ 1 / 2 := by
    rw [hxt, abs_div, abs_of_pos hpqR]
    rw [div_le_iff₀ hpqR]
    linarith [hmle]
  rw [nndist1_eq_of_int _ t habs, hxt, abs_div, abs_of_pos hpqR]

/-- Endpoints of a control pair are distinct primes. -/
lemma ctrlPairs_distinct_primes (BS : BlockSystem) {pq : ℕ × ℕ}
    (hpq : pq ∈ ctrlPairs BS) :
    Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≠ pq.2 := by
  have hmem := ctrlPairs_mem_blockSupport BS hpq
  refine ⟨blockSupport_prime BS hmem.1, blockSupport_prime BS hmem.2, ?_⟩
  simp only [ctrlPairs, Finset.mem_union, Finset.mem_biUnion, internalPairs,
    bipartitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Ico] at hpq
  rcases hpq with ⟨k, _, ⟨_, _⟩, hlt⟩ | ⟨k, _, hp1, hp2⟩
  · exact Nat.ne_of_lt hlt
  · -- bipartite: pq.1 < 2^(k+1) ≤ pq.2
    have h1 := (BS.hwindow k pq.1 hp1).2
    have h2 := (BS.hwindow (k + 1) pq.2 hp2).1
    exact Nat.ne_of_lt (lt_of_lt_of_le h1 h2)

/-- **Q_ctrl of the frequency-induced assignment** equals the nearest-integer
energy sum.  With `a(h)_p = h mod p`, `Q_ctrl(a(h)) = ∑_{pq} ‖h/(pq)‖²` — the
`Q_ctrl` side of the C4 identity `Q_E(h) = Q_ctrl(a(h))`. -/
lemma Qctrl_freq_eq (BS : BlockSystem) (h : ℕ) :
    Qctrl BS (fun p => ((h : ZMod p.1))) =
      ∑ pq ∈ ctrlPairs BS, (GlobalControl.nndist1 ((h : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))) ^ 2 := by
  unfold Qctrl
  refine Finset.sum_congr rfl (fun pq hpq => ?_)
  obtain ⟨hp1, hp2, hne⟩ := ctrlPairs_distinct_primes BS hpq
  have hmem := ctrlPairs_mem_blockSupport BS hpq
  -- toPlain of the frequency assignment is h mod p on the support
  have htp1 : toPlain BS (fun p => ((h : ZMod p.1))) pq.1 = (h : ZMod pq.1) := by
    simp only [toPlain, dif_pos hmem.1]
  have htp2 : toPlain BS (fun p => ((h : ZMod p.1))) pq.2 = (h : ZMod pq.2) := by
    simp only [toPlain, dif_pos hmem.2]
  have hHglob : Hglob (toPlain BS (fun p => ((h : ZMod p.1)))) pq.1 pq.2
      = crtRepr pq.1 pq.2 (h : ZMod pq.1) (h : ZMod pq.2) := by
    unfold Hglob; rw [htp1, htp2]
  rw [hHglob]
  -- ‖h/(pq)‖ = |crtRepr|/(pq), so nndist² = (crtRepr/(pq))²
  have hbridge := nndist1_eq_crtRepr_div pq.1 pq.2 hp1 hp2 hne h
  rw [hbridge, div_pow, div_pow, sq_abs]

/-! ## C4 minor-arc energy reindex (assembly glue)

Given the structural facts that the C1 construction must provide — `Q_E(h) ≥
Q_ctrl(a(h))` (control pairs are edges), the off-main-arc membership of `a(h)`,
and injectivity of `h ↦ a(h)` — the minor-arc energy sum over frequencies is
bounded by the off-main-arc control-energy sum, ready to feed
`global_control_partition_final`. -/
lemma minor_energy_sum_le (BS : BlockSystem) (E : Finset ℕ) (c C : ℝ) (Sm : Finset ℕ)
    (hc : 0 ≤ c)
    (hQE : ∀ h ∈ Sm, Qctrl BS (fun p => ((h : ZMod p.1))) ≤ QE E h)
    (hnotmain : ∀ h ∈ Sm,
      (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C)
    (hinj : ∀ h₁ ∈ Sm, ∀ h₂ ∈ Sm,
      (fun p => ((h₁ : ZMod p.1)) : GlobalAssignment BS)
        = (fun p => ((h₂ : ZMod p.1)) : GlobalAssignment BS) → h₁ = h₂) :
    ∑ h ∈ Sm, Real.exp (-c * QE E h) ≤
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
        Real.exp (-c * Qctrl BS a.1) := by
  set af : ℕ → GlobalAssignment BS := fun h => (fun p => ((h : ZMod p.1))) with haf
  have hinj' : ∀ x ∈ Sm, ∀ y ∈ Sm, af x = af y → x = y := hinj
  rw [fintype_subtype_tsum_eq (fun a => a ∉ mainArc BS C)
    (fun a => Real.exp (-c * Qctrl BS a))]
  calc ∑ h ∈ Sm, Real.exp (-c * QE E h)
      ≤ ∑ h ∈ Sm, Real.exp (-c * Qctrl BS (af h)) := by
        refine Finset.sum_le_sum (fun h hh => ?_)
        exact Real.exp_le_exp.mpr (by nlinarith [hQE h hh, hc])
    _ = ∑ a ∈ Sm.image af, Real.exp (-c * Qctrl BS a) := by
        rw [Finset.sum_image hinj']
    _ ≤ ∑ a ∈ Finset.univ.filter (fun a => a ∉ mainArc BS C),
          Real.exp (-c * Qctrl BS a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => (Real.exp_pos _).le)
        intro a ha
        rw [Finset.mem_image] at ha
        obtain ⟨h, hh, rfl⟩ := ha
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hnotmain h hh⟩

end CircleMethod

end
