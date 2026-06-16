import RequestProject.R2MinorReadyArc
import RequestProject.R2MassBatchBaseLoadBudget
import RequestProject.R2BaseBudgetAssembly
import RequestProject.R2DyadicBlockSupport
import RequestProject.R2MainArcClassification

open Finset BigOperators GlobalControl
open scoped Classical

noncomputable section

namespace CircleMethod

/-- Foundation layer of the R2 construction: a block system at a large bottom
scale together with the prime-divisor set `R = b.primeFactors`, with all the
structural facts the terminal supply needs (block primes large enough to be
coprime to `b` and to keep `R` outside the block support). -/
lemma exists_r2_foundation (b : ℕ) (hb : 3 ≤ b) (k0min : ℕ) :
    ∃ BS : BlockSystem,
      k0min ≤ BS.k0 ∧ admissibleGlobalRange BS ∧
      blockPrimes BS.k0 ⊆ blockSupport BS ∧
      BlockSupportCoprimeWith BS b ∧
      (∀ r ∈ b.primeFactors, Nat.Prime r) ∧
      (∀ r ∈ b.primeFactors, r ∣ b) ∧
      CoversPrimeDivisors b.primeFactors b ∧
      (∀ r ∈ b.primeFactors, r ∉ blockSupport BS) := by
  obtain ⟨BS, hk0, hadm, hsub⟩ :=
    exists_blockSystem_with_blockPrimes_subset (max k0min (b + 1))
  have hk0min : k0min ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  -- every block-support prime exceeds `b` (since it is ≥ 2^k0 > b)
  have hslow : ∀ s ∈ blockSupport BS, b < s := by
    intro s hs
    simp only [blockSupport, Finset.mem_biUnion, Finset.mem_Icc] at hs
    obtain ⟨k, ⟨hkk0, _⟩, hsk⟩ := hs
    have h2k : 2 ^ k ≤ s := (BS.hwindow k s hsk).1
    have hk0le : 2 ^ BS.k0 ≤ s :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hkk0) h2k
    have hbk : b + 1 ≤ BS.k0 := le_trans (le_max_right _ _) hk0
    have hk0lt : BS.k0 < 2 ^ BS.k0 := Nat.lt_two_pow_self
    omega
  have hcop : BlockSupportCoprimeWith BS b := by
    intro s hs
    have hsp : Nat.Prime s := blockSupport_prime BS hs
    exact (hsp.coprime_iff_not_dvd).mpr
      (fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by have := hslow s hs; omega))
  refine ⟨BS, hk0min, hadm, hsub, hcop,
    fun r hr => Nat.prime_of_mem_primeFactors hr,
    fun r hr => Nat.dvd_of_mem_primeFactors hr,
    fun r hrp hrdvd => Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, by omega⟩, ?_⟩
  intro r hr hrmem
  have hrdvd : r ∣ b := Nat.dvd_of_mem_primeFactors hr
  have hrle : r ≤ b := Nat.le_of_dvd (by omega) hrdvd
  have := hslow r hrmem
  omega

/-- Top-level R2 assembly: discharge `exists_arcConstruction` for squarefree `b ≥ 3`
by instantiating the `frequencyMinor` endpoint with a concrete construction.

In progress: foundation layer (`exists_r2_foundation`) done; the concrete data
`D, Q, N`, supplies, lanes, and the parameter chase remain. -/
theorem exists_arcConstruction_final (T : Finset ℕ) (b : ℕ)
    (hb : 3 ≤ b) (hbsf : Squarefree b) :
    Nonempty (ArcConstruction T b) := by
  obtain ⟨k0min, Ctail, hCtail, hmain⟩ :=
    exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_frequencyMinor
      (1 : ℝ) one_pos (1 : ℝ) one_pos
  sorry

end CircleMethod

end
