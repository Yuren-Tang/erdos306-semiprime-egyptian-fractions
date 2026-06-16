import Mathlib

open Finset BigOperators

noncomputable section

namespace GlobalControl

/-!
# Dyadic prime blocks — definition only

This minimal, axiom-free base file isolates the dyadic prime block `dyadicBlock`
so that downstream elementary developments can depend on the definition without
pulling in the classical analytic axioms (`dyadic_prime_density`,
`dyadic_mertens_cumulative`), which live in `DyadicPrimes`.
-/

/-- The dyadic block of primes in `[2ᵏ, 2ᵏ⁺¹)`. -/
def dyadicBlock (k : ℕ) : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime

end GlobalControl

end
