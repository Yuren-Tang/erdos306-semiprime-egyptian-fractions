import RequestProject.DyadicBlockDef

/-!
# Structural analytic inputs

This file is the analytic-number-theory audit boundary of the formalization.
It states the two non-standard assumptions in the construction-facing structural
form supplied by the prime number theorem and Mertens' reciprocal-prime theorem.

The exported theorem names `dyadic_prime_density` and
`dyadic_mertens_cumulative` are deliberately kept as the stable downstream
interface.  The actual axioms have more descriptive names, so the audit output
makes clear which mathematical background each one represents.
-/

open Finset BigOperators

noncomputable section

namespace GlobalControl

/-- **Prime-number-theorem input, dyadic structural form.**

For every construction scale `k ≥ 5`, the dyadic prime block `[2^k, 2^(k+1))`
contains at least `2^k / (2 log(2^k))` primes.  This is the coarse prime-supply
interface consumed downstream.  Conceptually it is an eventual consequence of
`π(x) ~ x / log x`; the lower cutoff is part of this formal structural input. -/
axiom pnt_dyadic_prime_density (k : ℕ) (hk : 5 ≤ k) :
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ ((dyadicBlock k).card : ℝ)

/-- Stable downstream interface for dyadic prime density. -/
theorem dyadic_prime_density (k : ℕ) (hk : 5 ≤ k) :
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ ((dyadicBlock k).card : ℝ) :=
  pnt_dyadic_prime_density k hk

/-- **Mertens reciprocal-prime input, dyadic-window structural form.**

For all sufficiently large `k0`, the union of dyadic prime blocks from `k0` to
`3*k0` has reciprocal-prime mass at least `21/20`.  Conceptually this follows
from Mertens' theorem `∑_{p≤x} 1/p = log log x + B + o(1)`, since the window mass
for `[X, X^3)` tends to `log 3 > 1`. -/
axiom mertens_dyadic_window_mass :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
      (21 : ℝ) / 20 ≤
        ∑ p ∈ (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock, (1 : ℝ) / (p : ℝ)

/-- Stable downstream interface for the reciprocal-prime dyadic-window mass. -/
theorem dyadic_mertens_cumulative :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
      (21 : ℝ) / 20 ≤
        ∑ p ∈ (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock, (1 : ℝ) / (p : ℝ) :=
  mertens_dyadic_window_mass

end GlobalControl

end
