import RequestProject.R2MassBatchFinalBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# Dyadic block-system support bridge

The abstract `BlockSystem` interface does not imply that `blockPrimes BS.k0` is
contained in `blockSupport BS`.  The concrete dyadic block system used by the R2
construction does have this property.  This leaf exposes that fact without
modifying the cached block-system construction file.
-/

/-- A dyadic block system with arbitrarily large `k₀`, admissible global range,
and with the full `blockPrimes k₀` pool contained in its support. -/
theorem exists_blockSystem_with_blockPrimes_subset (k0min : ℕ) :
    ∃ BS : BlockSystem,
      k0min ≤ BS.k0 ∧ admissibleGlobalRange BS ∧
        blockPrimes BS.k0 ⊆ blockSupport BS := by
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
      exact dyadic_prime_density k (le_trans h5 hk1) }, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · dsimp only [admissibleGlobalRange]
    omega
  · intro p hp
    simpa [blockPrimes, blockSupport] using hp

end CircleMethod

end
