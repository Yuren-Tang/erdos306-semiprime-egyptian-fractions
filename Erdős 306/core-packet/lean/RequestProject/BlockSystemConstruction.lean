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

/-- **R2 (a): block-system existence.**  For every target `k₀min` there is a
`BlockSystem` with `k₀min ≤ k₀` and `admissibleGlobalRange`, namely the dyadic
prime blocks with `K = 2·k₀`.  All fields are elementary except `hdensity`, supplied
by `dyadic_prime_density`. -/
theorem exists_blockSystem (k0min : ℕ) :
    ∃ BS : BlockSystem, k0min ≤ BS.k0 ∧ admissibleGlobalRange BS := by
  set k0 : ℕ := max k0min 5 with hk0def
  have h5 : 5 ≤ k0 := le_max_right _ _
  refine ⟨{
    k0 := k0
    K := 2 * k0
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
