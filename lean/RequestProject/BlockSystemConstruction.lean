import RequestProject.GlobalControl.BlockSystem
import RequestProject.DyadicPrimes

open Finset BigOperators

noncomputable section

namespace GlobalControl

/-!
# Block-system construction (R2 foundation)

Constructs a `BlockSystem` with arbitrarily large `k₀` and `admissibleGlobalRange`,
taking the dyadic blocks `Pₖ = {primes in [2ᵏ, 2ᵏ⁺¹)}`.  The only non-elementary
input is the dyadic prime-density lower bound (`hdensity`), which is the structural PNT-type dyadic prime-density input.
-/

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
