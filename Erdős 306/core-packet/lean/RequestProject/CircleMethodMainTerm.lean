import RequestProject.CircleMethodMainArc

open Complex Finset BigOperators Real

noncomputable section

namespace CircleMethod

/-!
# Phase C — C3 main term (L2-full / L3 / L4), note 44

Builds the positive real main term of the circle method from the per-edge Taylor
expansion `bernoulli_log_taylor` (L1) and the diagonal Gaussian lower bound
`main_arc_gaussian_lower` (C3).  Everything here is self-contained over an edge
set `E : Finset ℕ` (edge value `val(e) = e`), weights `θ`, target `b`, with the
mass identity `∑_e θ_e/e = 1/b`; no `BlockSystem` is needed.  The assembly into
the frequency sum (R3) is in `CircleMethod` (`exists_positive_weighted_construction`).
-/

/-- The deviation `σ_E² = ∑_e θ_e(1-θ_e)/e²`. -/
def sigmaE2 (E : Finset ℕ) (θ : ℕ → ℝ) : ℝ :=
  ∑ e ∈ E, θ e * (1 - θ e) / (e : ℝ) ^ 2

lemma sigmaE2_nonneg (E : Finset ℕ) (θ : ℕ → ℝ)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3) :
    0 ≤ sigmaE2 E θ := by
  unfold sigmaE2
  refine Finset.sum_nonneg (fun e he => ?_)
  have h1 := hlb e he
  have h2 := hub e he
  have : 0 ≤ θ e * (1 - θ e) := by nlinarith
  positivity

/-- `σ_E² > 0` once the edge set is nonempty (each term is `≥ (2/9)/e² > 0`). -/
lemma sigmaE2_pos (E : Finset ℕ) (θ : ℕ → ℝ) (hne : E.Nonempty)
    (he0 : ∀ e ∈ E, 0 < e)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3) :
    0 < sigmaE2 E θ := by
  obtain ⟨e0, he0'⟩ := hne
  unfold sigmaE2
  apply Finset.sum_pos'
  · intro e he
    have h1 := hlb e he; have h2 := hub e he
    have : 0 ≤ θ e * (1 - θ e) := by nlinarith
    positivity
  · refine ⟨e0, he0', ?_⟩
    have h1 := hlb e0 he0'; have h2 := hub e0 he0'
    have hθ : 0 < θ e0 * (1 - θ e0) := by nlinarith
    have hepos : 0 < (e0 : ℝ) := by exact_mod_cast he0 e0 he0'
    positivity

/-- **Non-vanishing of the Bernoulli factor on the main arc.**  For `θ ∈ [1/3,2/3]`
and `|t| ≤ 1/10`, `φ_θ(t) ≠ 0`.  (Indeed `|φ|² ≥ cos²(πt) > 0`.) -/
lemma bernoulliCharFun_ne_zero_main (θ t : ℝ) (hlb : 1/3 ≤ θ) (hub : θ ≤ 2/3)
    (ht : |t| ≤ 1/10) :
    bernoulliCharFun θ t ≠ 0 := by
  have hns : Complex.normSq (bernoulliCharFun θ t)
      = 1 - 4 * θ * (1 - θ) * Real.sin (Real.pi * t) ^ 2 := bernoulliCharFun_normSq θ t
  -- 4θ(1-θ) ≤ 1
  have hcoef : 4 * θ * (1 - θ) ≤ 1 := by nlinarith [sq_nonneg (2 * θ - 1)]
  have hcoef0 : 0 ≤ 4 * θ * (1 - θ) := by nlinarith
  -- cos(πt) > 0 since |πt| < π/2
  have hpi : 0 < Real.pi := Real.pi_pos
  have htlt : |Real.pi * t| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [ht, abs_nonneg t]
  have hcos : 0 < Real.cos (Real.pi * t) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [Set.mem_Ioo]
    constructor
    · linarith [neg_abs_le (Real.pi * t), htlt]
    · linarith [le_abs_self (Real.pi * t), htlt]
  have hsin : Real.sin (Real.pi * t) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t), sq_nonneg (Real.cos (Real.pi * t))]
  -- normSq ≥ 1 - 4θ(1-θ)·sin² ≥ cos² > 0
  have hpos : 0 < Complex.normSq (bernoulliCharFun θ t) := by
    rw [hns]
    have hcos2 : Real.cos (Real.pi * t) ^ 2 = 1 - Real.sin (Real.pi * t) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
    nlinarith [mul_pos hcos hcos, hcoef, hcoef0,
      Real.sin_sq_add_cos_sq (Real.pi * t), sq_nonneg (Real.sin (Real.pi*t))]
  intro hzero
  rw [hzero, Complex.normSq_zero] at hpos
  exact lt_irrefl 0 hpos

/-- **L2-full** (note 44).  The summed log of the Bernoulli factors at the
diagonal label `m` expands to `2πi(m/b) − 2π²m²σ_E²` up to a cubic remainder,
the linear coefficient being pinned to `1/b` by the **mass identity**. -/
lemma sum_logphi_bound (E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (m : ℤ)
    (he0 : ∀ e ∈ E, 0 < e)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3)
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (ht : ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10) :
    ‖(∑ e ∈ E, Complex.log (bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ))))
        - (2*Real.pi*((m:ℝ)/(b:ℝ))*Complex.I
            - 2*Real.pi^2*(m:ℝ)^2*((sigmaE2 E θ : ℝ) : ℂ))‖
      ≤ ∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3 := by
  have hstep := sum_bernoulli_log_taylor E θ (fun e => (m:ℝ)/(e:ℝ)) hlb hub ht
  simp only [] at hstep
  -- mass identity over ℂ
  have hmassC : (∑ e ∈ E, (θ e : ℂ) / (e : ℂ)) = 1 / (b : ℂ) := by
    have hcast : (∑ e ∈ E, (θ e : ℂ) / (e : ℂ))
        = ((∑ e ∈ E, θ e / (e:ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, hmass]; push_cast; ring
  -- σ_E² over ℂ
  have hsigC : ((sigmaE2 E θ : ℝ) : ℂ) = ∑ e ∈ E, (θ e : ℂ) * (1 - (θ e : ℂ)) / (e : ℂ)^2 := by
    unfold sigmaE2
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    push_cast; ring
  -- the key sum identity: ∑ (linImag − quad) = newTGT
  have key : (∑ e ∈ E, (2*(Real.pi:ℂ)*(θ e:ℂ)*((((m:ℝ)/(e:ℝ)):ℝ):ℂ)*Complex.I
                - 2*(Real.pi:ℂ)^2*(θ e:ℂ)*(1-(θ e:ℂ))*((((m:ℝ)/(e:ℝ)):ℝ):ℂ)^2))
            = 2*Real.pi*((m:ℝ)/(b:ℝ))*Complex.I
                - 2*Real.pi^2*(m:ℝ)^2*((sigmaE2 E θ : ℝ) : ℂ) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · -- linear part: ∑ 2π θe (m/e) I = 2π (m/b) I
      have hlin : (∑ e ∈ E, 2*(Real.pi:ℂ)*(θ e:ℂ)*((((m:ℝ)/(e:ℝ)):ℝ):ℂ)*Complex.I)
          = 2*(Real.pi:ℂ)*Complex.I*(m:ℂ)*(∑ e ∈ E, (θ e : ℂ)/(e : ℂ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e he => ?_)
        push_cast; ring
      rw [hlin, hmassC]; push_cast; ring
    · -- quadratic part: ∑ 2π² θe(1-θe)(m/e)² = 2π²m² ∑ θe(1-θe)/e²
      rw [hsigC, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e he => ?_)
      push_cast; ring
  rw [key] at hstep
  exact hstep

/-- The diagonal **main-arc term** at label `m`: the Bernoulli product at `t_e =
m/e` times the target phase `e(−m/b)`. -/
def term_label (E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (m : ℤ) : ℂ :=
  (∏ e ∈ E, bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ)))
    * Complex.exp (2 * Real.pi * (-((m:ℝ)/(b:ℝ))) * Complex.I)

/-- **L3** (note 44).  The main-arc term equals the real Gaussian
`exp(−2π²m²σ_E²)` times `exp(δ)`, where `δ` is the cubic Taylor remainder. -/
lemma term_label_eq (E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (m : ℤ)
    (he0 : ∀ e ∈ E, 0 < e)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3)
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (ht : ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10) :
    term_label E θ b m
      = ((Real.exp (-(2*Real.pi^2*(m:ℝ)^2*(sigmaE2 E θ))) : ℝ) : ℂ)
          * Complex.exp ((∑ e ∈ E, Complex.log (bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ))))
              - (2*Real.pi*((m:ℝ)/(b:ℝ))*Complex.I
                  - 2*Real.pi^2*(m:ℝ)^2*((sigmaE2 E θ : ℝ) : ℂ))) := by
  set δ : ℂ := (∑ e ∈ E, Complex.log (bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ))))
      - (2*Real.pi*((m:ℝ)/(b:ℝ))*Complex.I
          - 2*Real.pi^2*(m:ℝ)^2*((sigmaE2 E θ : ℝ) : ℂ)) with hδ
  have hne : ∀ e ∈ E, bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ)) ≠ 0 :=
    fun e he => bernoulliCharFun_ne_zero_main (θ e) _ (hlb e he) (hub e he) (ht e he)
  have hprod : (∏ e ∈ E, bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ)))
      = Complex.exp (∑ e ∈ E, Complex.log (bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ)))) :=
    prod_eq_exp_sum_log E _ hne
  unfold term_label
  rw [hprod, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  rw [hδ]; push_cast; ring

/-- **L3→Re** (per label).  When the cubic remainder is small (`≤ 1/10`), the
real part of the main-arc term is at least `0.8` times the Gaussian. -/
lemma term_label_re_lower (E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (m : ℤ)
    (he0 : ∀ e ∈ E, 0 < e)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3)
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (ht : ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10)
    (hsmall : (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10) :
    0.8 * Real.exp (-(2*Real.pi^2*(m:ℝ)^2*(sigmaE2 E θ))) ≤ (term_label E θ b m).re := by
  rw [term_label_eq E θ b m he0 hlb hub hmass ht]
  set G : ℝ := Real.exp (-(2*Real.pi^2*(m:ℝ)^2*(sigmaE2 E θ))) with hGdef
  have hGpos : 0 < G := Real.exp_pos _
  set δ : ℂ := (∑ e ∈ E, Complex.log (bernoulliCharFun (θ e) ((m:ℝ)/(e:ℝ))))
      - (2*Real.pi*((m:ℝ)/(b:ℝ))*Complex.I
          - 2*Real.pi^2*(m:ℝ)^2*((sigmaE2 E θ : ℝ) : ℂ)) with hδdef
  -- ‖δ‖ ≤ 1/10
  have hδnorm : ‖δ‖ ≤ 1/10 := by
    rw [hδdef]
    exact le_trans (sum_logphi_bound E θ b m he0 hlb hub hmass ht) hsmall
  -- ‖exp δ - 1‖ ≤ 2‖δ‖
  have hδle1 : ‖δ‖ ≤ 1 := by linarith [hδnorm]
  have hexpb : ‖Complex.exp δ - 1‖ ≤ 2 * ‖δ‖ := Complex.norm_exp_sub_one_le hδle1
  -- (exp δ).re ≥ 0.8
  have hre : (0.8 : ℝ) ≤ (Complex.exp δ).re := by
    have h1 : |(Complex.exp δ - 1).re| ≤ ‖Complex.exp δ - 1‖ := Complex.abs_re_le_norm _
    have h2 : (Complex.exp δ).re = 1 + (Complex.exp δ - 1).re := by
      rw [Complex.sub_re, Complex.one_re]; ring
    have h3 : |(Complex.exp δ - 1).re| ≤ 2 * (1/10) := le_trans (le_trans h1 hexpb) (by linarith [hδnorm])
    rw [h2]
    linarith [(abs_le.mp h3).1]
  -- combine
  have hmulre : (((G:ℂ)) * Complex.exp δ).re = G * (Complex.exp δ).re := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hmulre]
  nlinarith [mul_le_mul_of_nonneg_left hre hGpos.le, hGpos]

/-- **L4** (note 44).  The diagonal main sum over the label window
`[-N, N]` has real part `≥ c₃/σ_E` with `c₃ = 0.8·e^{-π²/2}/2`. -/
lemma main_re_lower (E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (N : ℤ)
    (hne : E.Nonempty) (he0 : ∀ e ∈ E, 0 < e)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3)
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (hN : (1:ℝ) / Real.sqrt (sigmaE2 E θ) ≤ (N:ℝ))
    (ht : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N, (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10) :
    0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E θ)
      ≤ (∑ m ∈ Finset.Icc (-N) N, term_label E θ b m).re := by
  set σ := Real.sqrt (sigmaE2 E θ) with hσdef
  have hσ2pos : 0 < sigmaE2 E θ := sigmaE2_pos E θ hne he0 hlb hub
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hσ2pos
  have hσsq : σ ^ 2 = sigmaE2 E θ := Real.sq_sqrt hσ2pos.le
  rw [Complex.re_sum]
  calc 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / σ
      = 0.8 * (Real.exp (-(Real.pi^2/2)) / 2 / σ) := by ring
    _ ≤ 0.8 * (∑ m ∈ Finset.Icc (-N) N, Real.exp (-(2*Real.pi^2*σ^2)*(m:ℝ)^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact main_arc_gaussian_lower σ hσpos N hN
    _ = ∑ m ∈ Finset.Icc (-N) N, 0.8 * Real.exp (-(2*Real.pi^2*σ^2)*(m:ℝ)^2) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.Icc (-N) N, (term_label E θ b m).re := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hgauss : Real.exp (-(2*Real.pi^2*σ^2)*(m:ℝ)^2)
            = Real.exp (-(2*Real.pi^2*(m:ℝ)^2*(sigmaE2 E θ))) := by
          congr 1; rw [hσsq]; ring
        rw [hgauss]
        exact term_label_re_lower E θ b m he0 hlb hub hmass (ht m hm) (hsmall m hm)

/-- The Fourier-identity summand at frequency `h` (matches `wcount_fourier_identity`). -/
def fourierTerm (E : Finset ℕ) (theta : ℕ → ℝ) (b L h : ℕ) : ℂ :=
  (∏ e ∈ E, ((theta e : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
      + (1 - theta e)))
    * Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))

/-- **R3 main-arc reindex.**  Given a label map `lbl` that bijects the main-arc
frequency set `SM` onto the label window `[-N, N]` and identifies the Fourier
term with the diagonal label term (the CRT/periodicity facts the construction
supplies), the real part of the main-arc Fourier sum is `≥ c₃/σ_E`. -/
lemma main_sum_re_lower (E : Finset ℕ) (θ : ℕ → ℝ) (b L : ℕ) (N : ℤ) (SM : Finset ℕ)
    (lbl : ℕ → ℤ)
    (hne : E.Nonempty) (he0 : ∀ e ∈ E, 0 < e)
    (hlb : ∀ e ∈ E, 1/3 ≤ θ e) (hub : ∀ e ∈ E, θ e ≤ 2/3)
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (hN : (1:ℝ) / Real.sqrt (sigmaE2 E θ) ≤ (N:ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N, (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10)
    (hmaps : ∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N)
    (hinj : ∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂)
    (hsurj : ∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m)
    (hterm : ∀ h ∈ SM, fourierTerm E θ b L h = term_label E θ b (lbl h)) :
    0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E θ)
      ≤ (∑ h ∈ SM, fourierTerm E θ b L h).re := by
  have hsum : (∑ h ∈ SM, fourierTerm E θ b L h)
      = ∑ m ∈ Finset.Icc (-N) N, term_label E θ b m := by
    rw [Finset.sum_congr rfl hterm]
    exact Finset.sum_bij (fun h _ => lbl h) hmaps hinj
      (fun m hm => by obtain ⟨h, hh, he⟩ := hsurj m hm; exact ⟨h, hh, he⟩)
      (fun h _ => rfl)
  rw [hsum]
  exact main_re_lower E θ b N hne he0 hlb hub hmass hN htw hsmall

end CircleMethod

end
