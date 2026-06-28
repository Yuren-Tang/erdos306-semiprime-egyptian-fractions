/-
# Gaussian integer sums

An elementary one-dimensional Gaussian lattice-sum estimate used by the global
control argument. This module is independent of block systems and arithmetic
bookkeeping.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ## G7 support. Elementary Gaussian integer-sum bound (note 38 §7) -/

/-
**Gaussian integer-sum lemma (note 38 §7, step II).**  For `0 < A ≤ 1`,
    `∑_{m ∈ ℤ} exp(-A·m²) ≤ 1 + 6/√A`.

    Proof: the `m = 0` term contributes `1`; by symmetry the rest is
    `2·∑_{m ≥ 1} exp(-A·m²)`.  Split that tail at `1/√A`: for `m ≤ 1/√A` use
    `exp ≤ 1` (at most `1/√A + 1` terms — bounded by `2/√A`), and for
    `m > 1/√A` use `m² ≥ m/√A` so `exp(-A·m²) ≤ exp(-√A·m)`, a geometric tail
    summing to `≤ 1/(√A·(1 - e^{-√A})) ≤ 2/(√A·√A)`… ; collecting gives the
    stated `1 + 6/√A`.
-/
lemma gaussian_int_sum_le (A : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∑' m : ℤ, Real.exp (-A * (m : ℝ) ^ 2) ≤ 1 + 6 / Real.sqrt A := by
  -- Let s := Real.sqrt A, so 0 < s ≤ 1 and s^2 = A (since 0 < A ≤ 1).
  set s := Real.sqrt A with hs_def
  have hs_pos : 0 < s := by
    exact Real.sqrt_pos.mpr hA0
  have hs_le_one : s ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, by linarith ⟩
  have hs_sq_eq_A : s^2 = A := by
    exact Real.sq_sqrt hA0.le;
  -- The sum over ℤ is 1 + 2 * ∑'_{n≥1} exp(-A*n^2).
  have h_sum_decomp : ∑' m : ℤ, Real.exp (-A * m ^ 2) = 1 + 2 * ∑' n : ℕ, Real.exp (-A * (n + 1) ^ 2) := by
    have h_sum_decomp : ∑' m : ℤ, Real.exp (-A * m ^ 2) = ∑' m : ℕ, Real.exp (-A * m ^ 2) + ∑' m : ℕ, Real.exp (-A * (-(m + 1) : ℤ) ^ 2) := by
      rw [ ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
      rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
      · norm_num [ Equiv.intEquivNatSumNat ];
      · have h_summable : Summable (fun n : ℕ => Real.exp (-A * n ^ 2)) := by
          have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hA0 ) );
          exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
        simpa [Equiv.intEquivNatSumNat] using h_summable;
      · norm_num [ Equiv.intEquivNatSumNat ];
        have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ) );
        exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; nlinarith;
    rw [ h_sum_decomp, Summable.tsum_eq_zero_add ] <;> norm_num ; ring_nf;
    have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hA0 ) );
    exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
  -- For 1 ≤ n ≤ N: exp(-A n^2) ≤ 1; there are ≤ N ≤ 1/s such terms, contributing ≤ 1/s.
  have h_tail_bound : ∑' n : ℕ, Real.exp (-A * (n + 1) ^ 2) ≤ ∑ n ∈ Finset.range (Nat.floor (1 / s)), Real.exp (-A * (n + 1) ^ 2) + ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) := by
    rw [ ← Summable.sum_add_tsum_nat_add ];
    refine' add_le_add le_rfl ( Summable.tsum_le_tsum _ _ _ );
    · intro i; rw [ ← hs_sq_eq_A ] ; ring_nf; norm_num;
      nlinarith only [ show ( 0 : ℝ ) ≤ s * i by positivity, show ( 0 : ℝ ) ≤ s * ⌊s⁻¹⌋₊ by positivity, show ( 0 : ℝ ) ≤ s ^ 2 * i by positivity, show ( 0 : ℝ ) ≤ s ^ 2 * ⌊s⁻¹⌋₊ by positivity, Nat.lt_floor_add_one ( s⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hs_pos ), hs_pos, hs_le_one ];
    · have h_summable : Summable (fun n : ℕ => Real.exp (-A * n ^ 2)) := by
        have := Real.summable_exp_nat_mul_of_ge ( show -A < 0 by linarith ) ( show ∀ n : ℕ, ( n : ℝ ) ≤ n ^ 2 by intros n; norm_cast; nlinarith );
        convert this using 1;
      exact_mod_cast h_summable.comp_injective ( add_left_injective ( ⌊1 / s⌋₊ + 1 ) );
    · have h_geo_series : Summable (fun n : ℕ => (Real.exp (-s)) ^ (n + Nat.floor (1 / s) + 1)) := by
        exact Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; linarith ) ) fun a b h => by simpa using h;
      simpa [← Real.exp_nat_mul, mul_comm] using h_geo_series;
    · have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ) );
      exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith ) this;
  -- The tail ∑_{n≥1} exp(-s*n) = exp(-s)/(1-exp(-s)) = 1/(exp s - 1) ≤ 1/s (because exp s - 1 ≥ s for all s).
  have h_tail_sum : ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) ≤ 1 / s := by
    have h_tail_sum : ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) = Real.exp (-s * (Nat.floor (1 / s) + 1)) / (1 - Real.exp (-s)) := by
      let c := Real.exp (-s * (Nat.floor (1 / s) + 1))
      have h_geo : HasSum (fun n : ℕ => c * Real.exp (-s) ^ n)
          (c * (1 - Real.exp (-s))⁻¹) :=
        HasSum.mul_left c <| hasSum_geometric_of_lt_one (by positivity) <|
          show Real.exp (-s) < 1 from by rw [Real.exp_lt_one_iff]; linarith
      have h_terms : (fun n : ℕ => Real.exp (-s * (n + Nat.floor (1 / s) + 1))) =
          fun n : ℕ => c * Real.exp (-s) ^ n := by
        funext n
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [h_terms, h_geo.tsum_eq]
      simp only [c, div_eq_mul_inv]
    rw [ h_tail_sum, div_le_div_iff₀ ] <;> norm_num [ Real.exp_neg ];
    · field_simp;
      rw [ mul_comm ];
      gcongr;
      · exact le_mul_of_one_le_right hs_pos.le ( by linarith );
      · linarith [ Real.add_one_le_exp s ];
    · exact inv_lt_one_of_one_lt₀ <| by norm_num; positivity;
    · positivity;
  -- For 1 ≤ n ≤ N: exp(-A n^2) ≤ 1; there are ≤ N ≤ 1/s such terms, contributing ≤ 1/s.
  have h_tail_bound : ∑ n ∈ Finset.range (Nat.floor (1 / s)), Real.exp (-A * (n + 1) ^ 2) ≤ Nat.floor (1 / s) := by
    exact le_trans ( Finset.sum_le_sum fun _ _ => Real.exp_le_one_iff.mpr <| by nlinarith ) <| by norm_num;
  ring_nf at *;
  norm_num [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ] at * ; nlinarith [ Nat.floor_le ( inv_nonneg.mpr hs_pos.le ), mul_inv_cancel₀ hs_pos.ne' ]

end GlobalControl

end
