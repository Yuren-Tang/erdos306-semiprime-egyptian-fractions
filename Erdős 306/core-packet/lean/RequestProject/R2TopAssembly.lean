import RequestProject.R2MinorReadyArc
import RequestProject.R2MassBatchBaseLoadBudget
import RequestProject.R2BaseBudgetAssembly
import RequestProject.R2DyadicBlockSupport
import RequestProject.R2MainArcClassification
import RequestProject.R2ForbiddenBaseBudget

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

/-- Mass-batch layer (gate-free): given a concrete `D` whose base load already fits the
window and whose obstruction edges are below the bottom pair scale, a residual mass batch
`Q` with `R2MassBatchSupply (D.withQ Q)` exists.  The load threshold `k1` is supplied
explicitly (obtained from `blockPrimes_product_load_ge` upstream), avoiding the inner gate. -/
lemma exists_r2_massBatch {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b)
    (D : R2ConcreteData T b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0))
    (hTsmall : ∀ e ∈ T, e < 2 ^ D.BS.k0 * 2 ^ D.BS.k0)
    (hdisj : Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S))
    (hsub : blockPrimes D.BS.k0 ⊆ blockSupport D.BS)
    (k1 : ℕ) (hk1le : k1 ≤ D.BS.k0)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤ ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) :
    ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q) :=
  exists_massBatchSupply_of_blockPrimes_forbiddenBudget D (by omega) hbase hlarge
    (R2ForbiddenBudget.of_basePieces D hTsmall) k1 hk1le hsub hload
    (by simpa [R2ForbiddenBudget.of_basePieces] using
      basePieces_forbiddenBudget_final_ineq D hb hTsmall hdisj)

/-- `G` distinct gadget primes exist in the bottom dyadic block, as long as the
block-density lower bound `G ≤ 2^k/(2 log 2^k)` holds (from the prime-density axiom).
The multi-gadget extra-minor lane needs `G ≈ log` of these to damp the siblings. -/
lemma exists_block_primes (k : ℕ) (hk : 5 ≤ k) (G : ℕ)
    (hG : (G : ℝ) ≤ (2 : ℝ) ^ k / (2 * Real.log ((2 : ℝ) ^ k))) :
    ∃ S : Finset ℕ, S ⊆ dyadicBlock k ∧ S.card = G ∧
      (∀ s ∈ S, Nat.Prime s) ∧ (∀ s ∈ S, 2 ^ k ≤ s) := by
  have hcard : G ≤ (dyadicBlock k).card := by
    have h := dyadic_prime_density k hk
    exact_mod_cast le_trans hG h
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨S, hSsub, hScard, fun s hs => ?_, fun s hs => ?_⟩ <;>
    · have hs' := hSsub hs
      rw [dyadicBlock, Finset.mem_filter, Finset.mem_Ico] at hs'
      first | exact hs'.2 | exact hs'.1.1

/-- Data layer (threading): from a block system, a gadget prime `s`, and the irreducible
numeric facts (control load `≤ 3/(4b)` from the cited axiom, and the gadget-scale budget),
a residual mass batch `Q` with its supply exists, for `D = ⟨BS, ∅, b.primeFactors, {s}⟩`. -/
lemma exists_r2_data_of_numerics {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b)
    (BS : BlockSystem) (s : ℕ)
    (hsub : blockPrimes BS.k0 ⊆ blockSupport BS)
    (hs_ge : 2 ^ BS.k0 ≤ s)
    (hRout : ∀ r ∈ b.primeFactors, r ∉ blockSupport BS)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges BS) ≤ 3 / (4 * (b : ℝ)))
    (hsum : 3 / (4 * (b : ℝ)) +
        ((b.primeFactors.card * (1 : ℕ) : ℕ) : ℝ) / ((2 * 2 ^ BS.k0 : ℕ) : ℝ)
        < 3 / (2 * (b : ℝ)))
    (k1 : ℕ) (_hk15 : 5 ≤ k1) (hk1le : k1 ≤ BS.k0)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤ ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ BS.k0 * 2 ^ BS.k0))
    (hTsmall : ∀ e ∈ T, e < 2 ^ BS.k0 * 2 ^ BS.k0) :
    ∃ Q : Finset ℕ,
      R2MassBatchSupply ((⟨BS, ∅, b.primeFactors, {s}⟩ : R2ConcreteData T b).withQ Q) := by
  set D0 : R2ConcreteData T b := ⟨BS, ∅, b.primeFactors, {s}⟩ with hD0
  have hRprime : ∀ r ∈ D0.R, Nat.Prime r := fun r hr => Nat.prime_of_mem_primeFactors hr
  have hRout' : ∀ r ∈ D0.R, r ∉ blockSupport D0.BS := hRout
  have B0 : R2BaseLoadBudget D0 :=
    baseLoadBudget_of_control_epsilon_and_gadget_scale D0 (3 / (4 * (b : ℝ))) 2 (2 ^ BS.k0)
      (by norm_num) (by positivity) hctrl
      (fun r hr => by
        have := (Nat.prime_of_mem_primeFactors hr).two_le; exact_mod_cast this)
      (fun s' hs' => by
        simp only [hD0, Finset.mem_singleton] at hs'; subst hs'; exact_mod_cast hs_ge)
      (by simpa [hD0] using hsum)
  have hbase : D0.baseLoad < 3 / (2 * (b : ℝ)) := baseLoad_lt_of_budget D0 hRprime hRout' B0
  have hdisj := r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport D0 hRprime hRout'
  exact exists_r2_massBatch hb D0 hbase hlarge hTsmall hdisj hsub k1 hk1le hload

/-- Block-minor lane: the block-fiber-tail data, with `K = b` and `Qextra = QE − Qctrl`
(so `hQE` is an equality and `Qextra ≥ 0`, making `hfiber` the `b`-to-1 fiber count). -/
def r2_blockFiberTail {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (MA : MainArcFields D.E W.theta b D.L N)
    (Sblock : Finset ℕ) (C η Ctail Bblock : ℝ) (hC : 1 ≤ C)
    (heL : ∀ e ∈ D.E, e ∣ D.L) (he0 : ∀ e ∈ D.E, 0 < e) (hL : 0 < D.L)
    (hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p)
    (hsubMA : blockMinorPart MA.Sm Sblock ⊆ Finset.range D.L)
    (hnotmain : ∀ h ∈ blockMinorPart MA.Sm Sblock,
      (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) ∉ mainArc D.BS C)
    (hbudget : (b : ℝ) * ((η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl D.BS)
        ≤ Bblock) :
    R2BlockFiberTailData D W N MA Sblock Bblock η Ctail where
  C := C
  K := b
  Qextra := fun h => QE D.E h - Qctrl D.BS (fun p => ((h : ZMod p.1)))
  hC := hC
  hK := by positivity
  heL := heL
  he0 := he0
  hL := hL
  hQE := fun h _ => le_of_eq (by ring)
  hnotmain := hnotmain
  hbudget := hbudget
  hfiber := fun a => by
    have hsubset : (blockMinorPart MA.Sm Sblock).filter
        (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment D.BS) = a) ⊆
        (Finset.range D.L).filter
        (fun h => (fun p : {p // p ∈ blockSupport D.BS} => ((h : ZMod p.1))) = a) := by
      intro h hh
      rw [Finset.mem_filter] at hh ⊢
      exact ⟨hsubMA hh.1, hh.2⟩
    refine le_trans (Finset.sum_le_card_nsmul _ _ 1 ?_) ?_
    · intro h _
      refine Real.exp_le_one_iff.mpr ?_
      have hnn : 0 ≤ QE D.E h - Qctrl D.BS (fun p => ((h : ZMod p.1))) :=
        sub_nonneg.mpr (QE_ge_Qctrl D.BS D.E D.ctrlEdges_subset_E h)
      nlinarith [hnn]
    · simp only [nsmul_eq_mul, mul_one]
      exact_mod_cast le_trans (Finset.card_le_card hsubset)
        (mainArc_fiber_card_le D.BS D.L b hLeq a)

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
