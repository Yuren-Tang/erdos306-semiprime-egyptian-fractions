import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Finset

/-
**Finite spectral probabilistic existence principle.**

Let `J` and `Ω` be finite sets.  For each `j ∈ J` let `A j` be a finite set carrying a
weight `p j`, let `t ∈ X`, and let `S : (∏ j, A j) → X` be a "generated object".  Suppose
that for spectral functions `k ω : X → ℂ` the indicator of `S a = t` admits the spectral
representation
`1_{S a = t} = (1/N) ∑_ω k ω (S a) * conj (k ω t)`,
that `k ω` factorises through local functions `x j : A j → X` as
`k ω (S a) = ∏_j k ω (x j (a j))`,
and that the local spectral factors are `b j ω = ∑_{a_j} p j a_j * k ω (x j a_j)`.
Set `F ω = (∏_j b j ω) * conj (k ω t)` and split `Ω = L ⊔ H`.  If
`Re ∑_{ω ∈ L} F ω ≥ M`, while on `H` we have `‖b j ω‖ ≤ exp (-Δ ω j)`, `‖k ω t‖ ≤ C ω`
and `∑_{ω ∈ H} C ω · exp (-∑_j Δ ω j) ≤ R`, then `M > R` forces the existence of some
`a` with `S a = t`.

Remark.  The statement only uses `p j` as a family of complex weights; the fact that the
`p j` are genuine probability weights (nonnegative and summing to `1`) is **not** needed for
this existence conclusion, so those hypotheses are omitted.
-/
theorem spectral_existence
    {J Ω X : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] [DecidableEq X]
    {A : J → Type*} [∀ j, Fintype (A j)]
    (p : (j : J) → A j → ℝ)
    (t : X)
    (S : ((j : J) → A j) → X)
    (N : ℝ) (hN : 0 < N)
    (k : Ω → X → ℂ)
    (hspec : ∀ a : (j : J) → A j,
      (if S a = t then (1 : ℂ) else 0)
        = (1 / (N : ℂ)) * ∑ ω, k ω (S a) * (starRingEnd ℂ) (k ω t))
    (x : (j : J) → A j → X)
    (b : J → Ω → ℂ)
    (hb_def : ∀ j ω, b j ω = ∑ a, (p j a : ℂ) * k ω (x j a))
    (hfact : ∀ (a : (j : J) → A j) (ω : Ω), k ω (S a) = ∏ j, k ω (x j (a j)))
    (F : Ω → ℂ)
    (hF_def : ∀ ω, F ω = (∏ j, b j ω) * (starRingEnd ℂ) (k ω t))
    (L H : Finset Ω) (hdisj : Disjoint L H) (hcover : L ∪ H = Finset.univ)
    (M R : ℝ)
    (hM : M ≤ (∑ ω ∈ L, F ω).re)
    (Δ : Ω → J → ℝ) (C : Ω → ℝ)
    (hb : ∀ ω ∈ H, ∀ j, ‖b j ω‖ ≤ Real.exp (-(Δ ω j)))
    (hk : ∀ ω ∈ H, ‖k ω t‖ ≤ C ω)
    (hR : (∑ ω ∈ H, C ω * Real.exp (-(∑ j, Δ ω j))) ≤ R)
    (hMR : R < M) :
    ∃ a : (j : J) → A j, S a = t := by
  by_contra h_contra;
  -- Applying the hypothesis `hspec` to each `a`, we get that the sum over `ω` of `k ω (S a) * conj (k ω t)` is zero.
  have h_sum_zero : ∑ ω, F ω = 0 := by
    have h_sum_zero : ∑ a : ∀ j, A j, (∏ j, (p j (a j) : ℂ)) * (∑ ω, (∏ j, k ω (x j (a j))) * (starRingEnd ℂ) (k ω t)) = 0 := by
      refine' Finset.sum_eq_zero fun a ha => _;
      specialize hspec a; simp_all +decide [ ne_of_gt hN ] ;
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ a : ∀ j, A j, (∏ j, (p j (a j) : ℂ)) * (∑ ω, (∏ j, k ω (x j (a j))) * (starRingEnd ℂ) (k ω t)) = ∑ ω, (∏ j, (∑ a : A j, (p j a : ℂ) * k ω (x j a))) * (starRingEnd ℂ) (k ω t) := by
      simp +decide only [prod_sum, sum_mul];
      rw [ Finset.sum_comm ];
      refine' Finset.sum_bij ( fun a _ => fun j _ => a j ) _ _ _ _ <;> simp +decide;
      · simp +decide [ funext_iff ];
      · exact fun b => ⟨ fun j => b j ( Finset.mem_univ j ), rfl ⟩;
      · simp +decide [ Finset.prod_mul_distrib, Finset.mul_sum _ _ _, mul_assoc ];
    grind;
  -- Applying the hypothesis `hF_def` to each `ω`, we get that the sum over `ω` of `F ω` is zero.
  have h_sum_zero : (∑ ω ∈ H, F ω).re ≥ -R := by
    have h_sum_zero : ∀ ω ∈ H, ‖F ω‖ ≤ C ω * Real.exp (-∑ j, Δ ω j) := by
      intro ω hω
      rw [hF_def];
      simp +decide [ mul_comm, Real.exp_neg, Real.exp_sum ];
      exact mul_le_mul ( hk ω hω ) ( by rw [ ← Finset.prod_inv_distrib ] ; exact Finset.prod_le_prod ( fun _ _ => norm_nonneg _ ) fun _ _ => by simpa [ Real.exp_neg ] using hb ω hω _ ) ( Finset.prod_nonneg fun _ _ => norm_nonneg _ ) ( by linarith [ norm_nonneg ( k ω t ), hk ω hω ] );
    exact neg_le_of_abs_le ( le_trans ( Complex.abs_re_le_norm _ ) ( le_trans ( norm_sum_le _ _ ) ( le_trans ( Finset.sum_le_sum h_sum_zero ) hR ) ) );
  rw [ ← hcover, Finset.sum_union hdisj ] at *;
  norm_num [ Complex.ext_iff ] at * ; linarith