import RequestProject.GlobalControl

open Finset BigOperators

noncomputable section

namespace GlobalControl

/-!
# Block-system construction (R2 foundation)

Constructs a `BlockSystem` with arbitrarily large `k₀` and `admissibleGlobalRange`,
taking the dyadic blocks `Pₖ = {primes in [2ᵏ, 2ᵏ⁺¹)}`.  The only non-elementary
input is the dyadic prime-density lower bound (`hdensity`), which is the classical
**Rosser–Schoenfeld (1962)** estimate; it is recorded here as a single named axiom
pending the upstreaming of PNT-level results to Mathlib.
-/

/-- The dyadic block of primes in `[2ᵏ, 2ᵏ⁺¹)`. -/
def dyadicBlock (k : ℕ) : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime

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

/-- **R2 (a): block-system existence.**  For every target `k₀min` there is a
`BlockSystem` with `k₀min ≤ k₀` and `admissibleGlobalRange`, namely the dyadic
prime blocks with `K = 3·k₀` (the maximal admissible range, so the block-aligned
mass over `[2^{k₀},2^{3k₀}]` reaches the common-θ window for `b ≥ 3`).  All fields
are elementary except `hdensity`, supplied by `dyadic_prime_density`. -/
theorem exists_blockSystem (k0min : ℕ) :
    ∃ BS : BlockSystem, k0min ≤ BS.k0 ∧ admissibleGlobalRange BS := by
  set k0 : ℕ := max k0min 5 with hk0def
  have h5 : 5 ≤ k0 := le_max_right _ _
  refine ⟨{
    k0 := k0
    K := 3 * k0
    hk := by omega
    hk0 := by omega
    P := dyadicBlock
    hprime := by
      intro k p hp
      exact (Finset.mem_filter.mp hp).2
    hwindow := by
      intro k p hp
      have := (Finset.mem_filter.mp hp).1
      rw [Finset.mem_Ico] at this
      exact this
    hdensity := by
      intro k hk1 _hk2
      exact dyadic_prime_density k (le_trans h5 hk1) }, ?_, ?_⟩
  · exact le_max_left _ _
  · dsimp only [admissibleGlobalRange]; omega

end GlobalControl

end
