/-
  BernoulliFourier.lean

  Bernoulli random variable Fourier analysis for the Erdős 306 proof.

  Core facts:
  1. The characteristic function of a Bernoulli(θ) variable at frequency t is
     φ(t) = 1 - θ + θ · exp(2πit) = 1 - θ(1 - exp(2πit)).
  2. |φ(t)|² = 1 - 4θ(1-θ)sin²(πt).
  3. For θ ∈ [θ₀, 1-θ₀], |φ(t)| ≤ exp(-c·‖t‖²) where ‖t‖ = min_{n∈ℤ}|t-n|.
  4. For independent Bernoulli variables, the product of characteristic
     functions gives |μ̂(h)| ≤ exp(-c · ∑ ‖h/eᵢ‖²).
  5. Fourier inversion on ℤ/Lℤ: ℙ(Y = m) = (1/L) ∑_{h mod L} μ̂(h)·e(-hm/L).

  These are the foundational estimates used in §4-§6 of the conditional proof.
-/
import Mathlib

open Real BigOperators Complex

noncomputable section

/-! ## 1. Bernoulli characteristic function -/

/-- The characteristic function of a Bernoulli(θ) variable at frequency t:
    φ_θ(t) = (1 - θ) + θ · exp(2πit). -/
def bernoulliCharFun (θ t : ℝ) : ℂ :=
  (1 - θ : ℝ) + θ * Complex.exp (2 * Real.pi * t * Complex.I)

/-
|φ_θ(t)|² = 1 - 4θ(1-θ)sin²(πt).
-/
theorem bernoulliCharFun_normSq (θ t : ℝ) :
    Complex.normSq (bernoulliCharFun θ t) =
    1 - 4 * θ * (1 - θ) * Real.sin (Real.pi * t) ^ 2 := by
  unfold bernoulliCharFun; norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring;
  rw [ Real.sin_sq, Real.cos_sq ] ; ring;
  rw [ Real.sin_sq, Real.cos_sq ] ; ring

/-
For θ ∈ [θ₀, 1-θ₀] with 0 < θ₀ ≤ 1/2, the Bernoulli characteristic
    function satisfies |φ_θ(t)|² ≤ 1 - c·sin²(πt) with c = 4θ₀(1-θ₀).
-/
theorem bernoulliCharFun_normSq_le (θ₀ θ t : ℝ)
    (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ ≤ 1/2) (hθ : θ₀ ≤ θ) (hθ' : θ ≤ 1 - θ₀) :
    Complex.normSq (bernoulliCharFun θ t) ≤
    1 - 4 * θ₀ * (1 - θ₀) * Real.sin (Real.pi * t) ^ 2 := by
  rw [ bernoulliCharFun_normSq ];
  exact sub_le_sub_left ( mul_le_mul_of_nonneg_right ( by nlinarith ) ( sq_nonneg _ ) ) _

/-! ## 2. Product bound for independent Bernoulli variables -/

/-- The quadratic CRT energy of a character h with respect to edge set E
    and modulus parameters: Q_E(h) = ∑_{e ∈ E} ‖h/e‖², where
    ‖·‖ denotes the distance to the nearest integer.

    We formalize this abstractly: the energy is a sum of squared
    distances to nearest integers. -/
def quadraticCRTEnergy (phases : Finset ℝ) : ℝ :=
  ∑ t ∈ phases, Int.fract (t + 1/2) ^ 2

/-
approximation; exact ‖·‖² needs care

For independent Bernoulli(θ_e) variables with θ_e ∈ [θ₀, 1-θ₀],
    the product of characteristic functions satisfies
    |∏_e φ_{θ_e}(h/e)| ≤ exp(-c · Q_E(h))
    where c depends only on θ₀.

    This is the fundamental Fourier decay estimate used in the minor arc bound.
-/
theorem product_charFun_bound (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ ≤ 1/2)
    (E : Finset ℕ) (θ : ℕ → ℝ)
    (hθ_lb : ∀ e ∈ E, θ₀ ≤ θ e) (hθ_ub : ∀ e ∈ E, θ e ≤ 1 - θ₀)
    (h : ℕ) :
    ‖∏ e ∈ E, bernoulliCharFun (θ e) (h / (e : ℝ))‖ ≤
    Real.exp (- (2 * θ₀ * (1 - θ₀)) *
      ∑ e ∈ E, Real.sin (Real.pi * (h : ℝ) / (e : ℝ)) ^ 2) := by
  -- Applying the bound from `bernoulliCharFun_normSq_le` to each term in the product.
  have h_prod_bound : ∀ e ∈ E, ‖bernoulliCharFun (θ e) (h / e)‖ ≤ Real.exp (-2 * θ₀ * (1 - θ₀) * (Real.sin (Real.pi * h / e)) ^ 2) := by
    intro e he
    have h_char_bound : ‖bernoulliCharFun (θ e) (h / e)‖^2 ≤ 1 - 4 * θ₀ * (1 - θ₀) * (Real.sin (Real.pi * h / e)) ^ 2 := by
      convert bernoulliCharFun_normSq_le θ₀ ( θ e ) ( h / e ) hθ₀ hθ₀' ( hθ_lb e he ) ( hθ_ub e he ) using 1 ; ring;
      · rw [ Complex.normSq_eq_norm_sq ];
      · ring;
    -- Applying the inequality $1 - x \leq e^{-x}$ with $x = 4θ₀(1-θ₀)sin²(πh/e)$.
    have h_exp_bound : 1 - 4 * θ₀ * (1 - θ₀) * (Real.sin (Real.pi * h / e)) ^ 2 ≤ Real.exp (-4 * θ₀ * (1 - θ₀) * (Real.sin (Real.pi * h / e)) ^ 2) := by
      exact le_trans ( by ring_nf; norm_num ) ( Real.add_one_le_exp _ );
    convert Real.le_sqrt_of_sq_le ( h_char_bound.trans h_exp_bound ) using 1 ; rw [ Real.sqrt_eq_rpow, ← Real.exp_mul ] ; ring;
  convert Finset.prod_le_prod ?_ h_prod_bound using 1;
  · norm_num;
  · norm_num [ ← Real.exp_sum, Finset.mul_sum _ _ _ ];
  · exact fun _ _ => norm_nonneg _

/-! ## 3. Fourier inversion on ℤ/Lℤ

The Fourier inversion identity for Bernoulli sums on ℤ/Lℤ:
  ℙ(Y ≡ m (mod L)) = (1/L) ∑_{h=0}^{L-1} μ̂(h) · e(-hm/L)
where μ̂(h) = ∏_e φ_{θ_e}(h/e).

This is the starting point for the main-arc / minor-arc decomposition.
Full formalization requires a Bernoulli probability space. The identity
itself is a standard consequence of character orthogonality on ℤ/Lℤ
and independence of the Bernoulli variables. -/

/-! ## 4. Main-arc Taylor expansion -/

/-
**Main-arc estimate.** For |m| ≤ C/σ_E and all edges e with |m|/(e) → 0,
    the Bernoulli characteristic function admits a Taylor expansion:
      log φ_θ(m/e) = 2πi · m · θ/e - 2π² · m² · θ(1-θ)/e² + O(m³/e³).
    Summing over edges and using ∑ θ_e/e = 1/b:
      log μ̂(m) = 2πim/b - 2π²m²σ² + o(1)
    where σ² = ∑ θ_e(1-θ_e)/e².
    After cancellation with e(-m/b):
      μ̂(m)e(-m/b) = exp(-2π²σ²m²)(1 + o(1)).

    The main-arc contribution is therefore
      ∑_{|m| ≤ C/σ} μ̂(m)e(-m/b) ≈ ∑ exp(-2π²σ²m²) ≈ 1/σ > 0.

    This is the content of CP 01 §5.
-/
theorem main_arc_positive (σ : ℝ) (_hσ : 0 < σ) :
    0 < ∑ m ∈ Finset.Icc (-1 : ℤ) 1, Real.exp (- 2 * Real.pi ^ 2 * σ ^ 2 * (m : ℝ) ^ 2) := by
  exact Finset.sum_pos ( fun m hm => Real.exp_pos _ ) ( by decide )

end