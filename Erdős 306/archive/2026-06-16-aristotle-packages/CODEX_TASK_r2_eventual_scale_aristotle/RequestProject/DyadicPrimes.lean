import RequestProject.DyadicBlockDef

open Finset BigOperators

noncomputable section

namespace GlobalControl

/-!
# Dyadic prime blocks and their classical analytic inputs

This lightweight base file isolates the dyadic prime block `dyadicBlock` together
with the two classical analytic inputs used by the R2 construction:
`dyadic_prime_density` (Rosser–Schoenfeld) and `dyadic_mertens_cumulative`
(Mertens).  It imports only Mathlib so that the block-aligned mass-pool
development does not have to pull in the full Global-Control / SBEE chain.

These declarations were previously stated inside `BlockSystemConstruction`; they
have been relocated here verbatim (no new axioms are introduced).  The definition
`dyadicBlock` itself lives in the axiom-free base `DyadicBlockDef`.
-/

/-- **Dyadic prime density** (the one classical analytic input — *named, not proved*).

Rosser, J. B.; Schoenfeld, L. (1962), *Approximate formulas for some functions of
prime numbers*, Illinois J. Math. 6(1), Corollary 3:
`π(2x) − π(x) > 3x/(5 log x)` for `x ≥ 20.5`.  Since `3/5 > 1/2`, this dominates the
bound `2ᵏ/(2 log 2ᵏ)` required by `BlockSystem.hdensity`.  Stated for `k ≥ 5`
(so `2ᵏ ≥ 32 > 20.5`).  To be replaced once a PNT-level prime-density lower bound is
available in Mathlib (cf. the `PrimeNumberTheoremAnd` project). -/
axiom dyadic_prime_density (k : ℕ) (hk : 5 ≤ k) :
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ ((dyadicBlock k).card : ℝ)

/-- **Dyadic Mertens lower bound, cumulative form** (classical input for R2
block-aligned mass — *named, not proved*).

By Mertens (`∑_{p≤x} 1/p = log log x + M + o(1)`), the reciprocal sum of the
primes in the dyadic range `[2^{k₀}, 2^{3k₀})` is
`∑ = log log 2^{3k₀} − log log 2^{k₀} + o(1) = log 3 + o(1) ≈ 1.0986`.  We record
the honest cumulative lower bound `≥ 21/20 = 1.05` for all large `k₀` (true since
`1.05 < log 3`; the `o(1)` is absorbed by taking `k₀` large — hence the
`∃ k₁, ∀ k₀ ≥ k₁` shape, the same threshold form the construction already uses).

The *cumulative* form is essential: a per-block bound with the true constant
`c₀ ≈ 1` is **false for small `k`** (e.g. `∑_{p∈[32,64)} 1/p ≈ 0.148 < 1/6`), and
the count axiom `dyadic_prime_density` only yields the far-too-weak `≈ 1/(4k log2)`
per block (total `≈ 0.40`, product-load `≈ 0.08`).  With `≥ 1.05` here the
block-aligned product-load is `≥ (1.05² − ∑1/p²)/2 > 0.5`, clearing the common-θ
window `[3/(2b),3/b]` for squarefree `b ≥ 3` (`b=3` needs `0.5`).

Provenance: Rosser–Schoenfeld (1962) / Mertens; same status as
`dyadic_prime_density`, to be discharged once Mertens-level estimates upstream to
Mathlib. -/
axiom dyadic_mertens_cumulative :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
      (21 : ℝ) / 20 ≤
        ∑ p ∈ (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock, (1 : ℝ) / (p : ℝ)

end GlobalControl

end
