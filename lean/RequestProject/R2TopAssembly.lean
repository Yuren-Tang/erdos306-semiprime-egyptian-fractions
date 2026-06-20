import RequestProject.R2MinorReadyArc
import RequestProject.R2MassBatchBaseLoadBudget
import RequestProject.R2BaseBudgetAssembly
import RequestProject.R2DyadicBlockSupport
import RequestProject.R2LargeK0
import RequestProject.R2MainArcClassification
import RequestProject.R2ForbiddenBaseBudget

open Finset BigOperators GlobalControl
open scoped Classical

noncomputable section

namespace CircleMethod

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

/-- Data layer for a `G`-element gadget set `S` (generalising the singleton form):
from a block system and a set `S` of primes `≥ 2^k0`, the residual mass batch `Q`
with its supply exists for `D = ⟨BS, ∅, b.primeFactors, S⟩`. -/
lemma exists_r2_data_of_numerics_set {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b)
    (BS : BlockSystem) (S : Finset ℕ)
    (hsub : blockPrimes BS.k0 ⊆ blockSupport BS)
    (hS_ge : ∀ s ∈ S, 2 ^ BS.k0 ≤ s)
    (hRout : ∀ r ∈ b.primeFactors, r ∉ blockSupport BS)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges BS) ≤ 3 / (4 * (b : ℝ)))
    (hsum : 3 / (4 * (b : ℝ)) +
        ((b.primeFactors.card * S.card : ℕ) : ℝ) / ((2 * 2 ^ BS.k0 : ℕ) : ℝ)
        < 3 / (2 * (b : ℝ)))
    (k1 : ℕ) (_hk15 : 5 ≤ k1) (hk1le : k1 ≤ BS.k0)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤ ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ BS.k0 * 2 ^ BS.k0))
    (hTsmall : ∀ e ∈ T, e < 2 ^ BS.k0 * 2 ^ BS.k0) :
    ∃ Q : Finset ℕ,
      R2MassBatchSupply ((⟨BS, ∅, b.primeFactors, S⟩ : R2ConcreteData T b).withQ Q) := by
  set D0 : R2ConcreteData T b := ⟨BS, ∅, b.primeFactors, S⟩ with hD0
  have hRprime : ∀ r ∈ D0.R, Nat.Prime r := fun r hr => Nat.prime_of_mem_primeFactors hr
  have hRout' : ∀ r ∈ D0.R, r ∉ blockSupport D0.BS := hRout
  have B0 : R2BaseLoadBudget D0 :=
    baseLoadBudget_of_control_epsilon_and_gadget_scale D0 (3 / (4 * (b : ℝ))) 2 (2 ^ BS.k0)
      (by norm_num) (by positivity) hctrl
      (fun r hr => by
        have := (Nat.prime_of_mem_primeFactors hr).two_le; exact_mod_cast this)
      (fun s' hs' => by
        have := hS_ge s' (by simpa [hD0] using hs'); exact_mod_cast this)
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

/-
Numeric chase: a large main-arc cutoff `C` makes the block-lane tail term beat
`c₃/4`.
-/
lemma r2_exists_C (Ctail c3 : ℝ) (b : ℕ) (hCtail : 0 < Ctail) (hc3 : 0 < c3)
    (hb : 0 < b) :
    ∃ C : ℝ, 1 ≤ C ∧ (b : ℝ) * Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2) < c3 / 4 := by
  have h_exp_zero : Filter.Tendsto (fun C : ℝ => (b : ℝ) * Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul ( Real.tendsto_exp_atBot.comp <| Filter.tendsto_atTop_atBot.mpr fun x => ⟨ |x| + 1, fun y hy => by cases abs_cases x <;> nlinarith ⟩ );
  exact Filter.eventually_atTop.mp ( h_exp_zero.eventually ( gt_mem_nhds <| by positivity ) ) |> fun ⟨ C, hC ⟩ ↦ ⟨ Max.max C 1, le_max_right _ _, hC _ <| le_max_left _ _ ⟩

/-
Geometric decay: a base in `[0,1)` raised to a large enough power drops below any
positive budget.  Applied with base `√(1-(8/9)/b²) < 1` (the worst-case per-gadget
sibling damping over `rfun ≤ b`).
-/
lemma r2_exists_pow_le (base Dmp : ℝ) (h0 : 0 ≤ base) (h1 : base < 1)
    (hDmp : 0 < Dmp) :
    ∃ G : ℕ, base ^ G ≤ Dmp := by
  obtain ⟨G, hG⟩ := exists_pow_lt_of_lt_one hDmp h1
  exact ⟨G, le_of_lt hG⟩

/-
Numeric chase: for any gadget count `G`, the dyadic prime-density lower bound
`G ≤ 2^k/(2 log 2^k)` holds for all large `k`.
-/
lemma r2_exists_k0_density (G : ℕ) :
    ∃ k0min : ℕ, ∀ k : ℕ, k0min ≤ k →
      (G : ℝ) ≤ (2 : ℝ) ^ k / (2 * Real.log ((2 : ℝ) ^ k)) := by
  -- We'll use that exponential functions grow faster than polynomial functions to find such a $k0min$.
  have h_exp_growth : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / (2 * k * Real.log 2)) Filter.atTop Filter.atTop := by
    have h_exp_growth : Filter.Tendsto (fun k : ℕ => (2 : ℝ) ^ k / k) Filter.atTop Filter.atTop := by
      refine' Filter.tendsto_atTop_mono' _ _ tendsto_natCast_atTop_atTop;
      filter_upwards [ Filter.eventually_ge_atTop 8 ] with k hk using by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; induction hk <;> norm_num [ Nat.pow_succ ] at * ; nlinarith;
    convert h_exp_growth.atTop_div_const ( show 0 < 2 * Real.log 2 by positivity ) using 2 ; ring;
  exact Filter.eventually_atTop.mp ( h_exp_growth.eventually_ge_atTop G ) |> fun ⟨ k0min, hk0min ⟩ ↦ ⟨ k0min, fun k hk ↦ by simpa [ Real.log_pow, mul_assoc, mul_comm, mul_left_comm ] using hk0min k hk ⟩

/-
Count bound for the extra-minor frequencies: a main-arc frequency is a CRT
constant assignment `a_m` for a single label `m` with `|m| ≤ C/σ ≤ N`, and each
label-fiber has `≤ b` frequencies in `range L`.  Hence at most `b·(2N+1)`.
-/
lemma r2_extra_count_le {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D) (N : ℤ) (C : ℝ)
    (hN : 0 ≤ N)
    (hCN : C / sigmaCtrl D.BS ≤ (N : ℝ))
    (hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p)
    (MA : MainArcFields D.E W.theta b D.L N) :
    ((extraMinorPart MA.Sm ((mainArcClassificationData D W N C).Sblock MA)
        ((mainArcClassificationData D W N C).Sextra MA)).card : ℝ)
      ≤ (b : ℝ) * (2 * (N : ℝ) + 1) := by
  refine' le_trans ( Nat.cast_le.mpr ( Finset.card_le_card _ ) ) _;
  exact Finset.biUnion ( Finset.Icc ( -N ) N ) fun m => Finset.filter ( fun h => ( fun p : { p // p ∈ blockSupport D.BS } => ( h : ZMod p.1 ) ) = ( fun p : { p // p ∈ blockSupport D.BS } => ( m : ZMod p.1 ) ) ) ( Finset.range D.L );
  · intro h hh; simp_all +decide [ extraMinorPart, mainArcClassificationData ] ;
    unfold mainArcBlockSet mainArcExtraSet at hh; simp_all +decide [ funext_iff ] ;
    obtain ⟨ m, hm₁, hm₂ ⟩ := hh.2.2.2; use m; simp_all +decide [ freqAssignmentOf ] ;
    exact ⟨ ⟨ by exact_mod_cast neg_le_of_abs_le ( hm₁.trans hCN ), by exact_mod_cast le_of_abs_le ( hm₁.trans hCN ) ⟩, by linarith [ Finset.mem_range.mp ( mainArcFields_mem_range_of_mem_Sm MA hh.1 ) ] ⟩;
  · refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le ) _;
    refine' le_trans ( Nat.cast_le.mpr <| Finset.sum_le_sum fun x hx => mainArc_fiber_card_le D.BS D.L b hLeq _ ) _ ; norm_num [ Int.card_Icc ] ; ring_nf ; norm_cast ; norm_num [ hN ] ;
    rw [ max_eq_left ] <;> linarith

/-
Strengthened foundation: the explicit dyadic block system (with `P = dyadicBlock`)
additionally exposes that the whole dyadic block at any in-range scale lies in the
support, so high-scale gadget primes can be chosen inside `blockSupport`.
-/
lemma exists_r2_foundation_dyadic (b : ℕ) (hb : 3 ≤ b) (k0min : ℕ) :
    ∃ BS : BlockSystem,
      k0min ≤ BS.k0 ∧ 5 ≤ BS.k0 ∧ admissibleGlobalRange BS ∧
      blockPrimes BS.k0 ⊆ blockSupport BS ∧
      BlockSupportCoprimeWith BS b ∧
      (∀ r ∈ b.primeFactors, Nat.Prime r) ∧
      (∀ r ∈ b.primeFactors, r ∣ b) ∧
      CoversPrimeDivisors b.primeFactors b ∧
      (∀ r ∈ b.primeFactors, r ∉ blockSupport BS) ∧
      2 * BS.k0 ≤ BS.K ∧
      dyadicBlock (2 * BS.k0) ⊆ blockSupport BS := by
  obtain ⟨BS, hk0, hadm, hsub⟩ := exists_blockSystem_with_blockPrimes_subset (max (max k0min 5) (b + 1));
  refine' ⟨ BS, _, _, hadm, hsub, _, _, _, _ ⟩ <;> norm_num at *;
  all_goals norm_num [ BlockSupportCoprimeWith, CoversPrimeDivisors ];
  any_goals tauto;
  · intro s hs; exact Nat.Coprime.symm <| Nat.Coprime.gcd_eq_one <| Nat.Coprime.symm <| Nat.Coprime.gcd_eq_one <| Nat.Coprime.coprime_dvd_right ( show b ∣ b from dvd_rfl ) <| Nat.Coprime.gcd_eq_one <| Nat.Prime.coprime_iff_not_dvd ( show Nat.Prime s from by
                                                                                                                                                                                                                                          grind +suggestions ) |>.2 <| by
                                                                                                                                                                                                                                          have hslow : ∀ s ∈ blockSupport BS, b < s := by
                                                                                                                                                                                                                                            intro s hs
                                                                                                                                                                                                                                            simp [blockSupport] at hs
                                                                                                                                                                                                                                            obtain ⟨k, ⟨hkk0, _⟩, hsk⟩ := hs
                                                                                                                                                                                                                                            have h2k : 2 ^ k ≤ s := (BS.hwindow k s hsk).1
                                                                                                                                                                                                                                            have hk0le : 2 ^ BS.k0 ≤ s := le_trans (Nat.pow_le_pow_right (by norm_num) hkk0) h2k
                                                                                                                                                                                                                                            have hbk : b + 1 ≤ BS.k0 := by linarith
                                                                                                                                                                                                                                            have hk0lt : BS.k0 < 2 ^ BS.k0 := Nat.lt_two_pow_self
                                                                                                                                                                                                                                            omega
                                                                                                                                                                                                                                          exact Nat.not_dvd_of_pos_of_lt (by omega) (hslow s hs);
  · refine' ⟨ fun r hr hr' => ⟨ hr, hr', by linarith ⟩, _, _, _ ⟩;
    · intro r hr hrdvd hb0 hrBS
      have hrle : r ≤ b := Nat.le_of_dvd (by omega) hrdvd
      have hslow : ∀ s ∈ blockSupport BS, b < s := by
        intro s hs
        simp only [blockSupport, mem_biUnion, mem_Icc] at hs
        obtain ⟨k, ⟨hkk0, _⟩, hsk⟩ := hs
        have h2k : 2 ^ k ≤ s := (BS.hwindow k s hsk).1
        have hk0le : 2 ^ BS.k0 ≤ s := le_trans (Nat.pow_le_pow_right (by norm_num) hkk0) h2k
        have hk0lt : BS.k0 < 2 ^ BS.k0 := Nat.lt_two_pow_self
        omega
      have := hslow r hrBS
      linarith;
    · linarith [ hadm.1 ];
    · intro p hp; simp_all +decide [ blockPrimes, blockSupport ] ;
      grind

/-
`sigmaE2` is bounded below by the control deviation: every weight
`θ∈[1/3,2/3]` has `θ(1-θ) ≥ 2/9`, and the control edges sit inside `E`.
-/
lemma sigmaE2_ge_ctrl {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D) :
    (2 / 9 : ℝ) * (sigmaCtrl D.BS) ^ 2 ≤ sigmaE2 D.E W.theta := by
  -- Apply the lemma that states the sum of the reciprocals of the squares of the control edges is equal to the square of the control deviation.
  have h_sum_ctrl : ∑ e ∈ ctrlEdges D.BS, (1 : ℝ) / (e : ℝ) ^ 2 = (sigmaCtrl D.BS) ^ 2 := by
    convert sum_inv_sq_ctrlEdges_eq_sigmaCtrl_sq D.BS using 1;
  -- Apply the lemma that states the sum of the reciprocals of the squares of the control edges is less than or equal to the sum of the reciprocals of the squares of the edges in E.
  have h_sum_le : ∑ e ∈ ctrlEdges D.BS, (1 : ℝ) / (e : ℝ) ^ 2 ≤ ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg ( D.ctrlEdges_subset_E ) fun _ _ _ => by positivity;
  refine' le_trans _ ( Finset.sum_le_sum fun e he => show ( 1 : ℝ ) / e ^ 2 * ( 2 / 9 ) ≤ W.theta e * ( 1 - W.theta e ) / e ^ 2 from _ );
  · rw [ ← Finset.sum_mul _ _ _ ] ; nlinarith;
  · convert mul_le_mul_of_nonneg_right ( show ( 2 / 9 : ℝ ) ≤ W.theta e * ( 1 - W.theta e ) by nlinarith only [ sq_nonneg ( W.theta e - 1 / 2 ), W.hlb e he, W.hub e he ] ) ( inv_nonneg.mpr ( sq_nonneg ( e : ℝ ) ) ) using 1 ; ring

/-
Strong lower bound for `sigmaCtrl` (true order `~2^{-k0}/k0`), keeping the full
`|P k0|^2` internal-pair count.  Needed to keep the label window `N ≈ 1/σ_E`
small enough that the fine main-arc cubic error `hsmall` decays.
-/
lemma sigmaCtrl_ge_strong (BS : BlockSystem) (hk0 : 14 ≤ BS.k0) :
    (1 : ℝ) / (100 * (BS.k0 : ℝ) * (2 : ℝ) ^ BS.k0) ≤ sigmaCtrl BS := by
  refine Real.le_sqrt_of_sq_le ?_ ; norm_num [ sigmaCtrl ] ; ring;
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( show ctrlPairs BS ⊇ internalPairs BS BS.k0 from _ ) fun _ _ _ => by positivity ) <;> norm_num [ pow_mul' ];
  · refine' le_trans _ ( Finset.sum_le_sum fun x hx => show ( x.1 ^ 2 : ℝ ) ⁻¹ * ( x.2 ^ 2 : ℝ ) ⁻¹ ≥ ( 1 / ( 2 ^ ( BS.k0 + 1 ) ) ^ 2 ) ^ 2 from _ ) <;> norm_num [ pow_mul' ] at *;
    · -- Count the number of internal pairs in block `k0`.
      have h_card_internal : (internalPairs BS BS.k0).card ≥ (2 ^ BS.k0 / (2 * (BS.k0 : ℝ) * Real.log 2)) * ((2 ^ BS.k0 / (2 * (BS.k0 : ℝ) * Real.log 2) - 1) / 2) := by
        have h_card_ge : ((internalPairs BS BS.k0).card : ℝ) ≥ (BS.P BS.k0).card * ((BS.P BS.k0).card - 1) / 2 := by
          have h_card_internal : (internalPairs BS BS.k0).card = Finset.card (Finset.powersetCard 2 (BS.P BS.k0)) := by
            refine' Finset.card_bij ( fun x hx => { x.1, x.2 } ) _ _ _ <;> simp_all +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
            · simp +contextual [ internalPairs ];
              exact fun a b ha hb hab => Finset.card_pair hab.ne;
            · simp +contextual [ internalPairs ];
              grind +suggestions;
            · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; simp_all +decide [ internalPairs ] ;
              cases lt_or_gt_of_ne hab <;> [ exact ⟨ a, b, ⟨ hb, ‹_› ⟩, rfl ⟩ ; exact ⟨ b, a, ⟨ ⟨ hb.2, hb.1 ⟩, ‹_› ⟩, by rw [ Finset.pair_comm ] ⟩ ];
          rcases n : Finset.card ( BS.P BS.k0 ) with ( _ | _ | n ) <;> simp_all +decide [ Nat.choose_two_right ];
          rw [ Nat.cast_div ] <;> norm_cast ; exact Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] );
        have h_card_ge : ((BS.P BS.k0).card : ℝ) ≥ (2 ^ BS.k0 / (2 * BS.k0 * Real.log 2)) := by
          have := BS.hdensity BS.k0 ( by linarith ) ( by linarith [ BS.hk ] ) ; simp_all +decide [ Real.log_pow ] ;
          simpa only [ mul_assoc ] using this;
        nlinarith [ show ( 2 : ℝ ) ^ BS.k0 / ( 2 * BS.k0 * Real.log 2 ) ≥ 1 by exact one_le_div ( by positivity ) |>.2 <| by nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, show ( BS.k0 : ℝ ) ≥ 14 by norm_cast, show ( 2 : ℝ ) ^ BS.k0 ≥ 2 * BS.k0 by exact mod_cast Nat.le_induction ( by norm_num ) ( fun k hk ih ↦ by norm_num [ Nat.pow_succ ] at * ; nlinarith ) _ hk0 ] ];
      refine' le_trans _ ( mul_le_mul_of_nonneg_right h_card_internal _ ) <;> norm_num [ pow_succ' ] at *;
      field_simp;
      refine' Nat.le_induction _ _ BS.k0 hk0 <;> norm_num [ pow_succ' ] at *;
      · have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ Real.log_nonneg one_le_two ];
      · intro n hn ih; ring_nf at *; norm_num at *;
        nlinarith [ Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos zero_lt_two, show ( n : ℝ ) ≥ 14 by norm_cast, pow_pos ( zero_lt_two' ℝ ) n ];
    · rw [ ← mul_inv ] ; gcongr ; norm_cast ; simp_all +decide [ internalPairs ];
      · exact ⟨ pow_pos ( Nat.Prime.pos ( by exact BS.hprime _ _ hx.1.1 ) ) 2, pow_pos ( Nat.Prime.pos ( by exact BS.hprime _ _ hx.1.2 ) ) 2 ⟩;
      · norm_cast ; exact Nat.le_trans ( Nat.mul_le_mul ( Nat.pow_le_pow_left ( BS.hwindow BS.k0 x.1 ( Finset.mem_filter.mp hx |>.1 |> Finset.mem_product.mp |>.1 ) |>.2.le ) 2 ) ( Nat.pow_le_pow_left ( BS.hwindow BS.k0 x.2 ( Finset.mem_filter.mp hx |>.1 |> Finset.mem_product.mp |>.2 ) |>.2.le ) 2 ) ) ( by ring_nf; norm_num ) ;
  · exact Finset.subset_iff.mpr fun x hx => Finset.mem_union_left _ <| Finset.mem_biUnion.mpr ⟨ BS.k0, Finset.mem_Icc.mpr ⟨ le_rfl, by linarith [ BS.hk ] ⟩, hx ⟩

/-
Fine main-arc numeric fields for the concrete edge set: with all edges
`≥ Emin`, the label window `N` small relative to `Emin`, and the quadratic
reciprocal-square control `N^2 · ∑ 1/e^2 ≤ 18`, the Taylor conditions `htw`/`hsmall`
hold via the *actual* per-edge sum (not the lossy `card·ρ^3` bound).
-/
lemma r2_numericFields {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (W : R2ConcreteData.Weights D) (N : ℤ) (Emin B : ℝ)
    (hB : 0 < B)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (hEmin0 : 0 < Emin)
    (hEmin : ∀ e ∈ D.E, Emin ≤ (e : ℝ))
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hNnonneg : 0 ≤ N)
    (h10N : 10 * (N : ℝ) ≤ Emin)
    (hsumsq : (N : ℝ) ^ 2 * (∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2) ≤ B)
    (hsmallN : (N : ℝ) / Emin ≤ 1 / (1000000 * B)) :
    MainArcNumericFields D.E W.theta N := by
  refine' ⟨ hN, hNnonneg, _, _ ⟩;
  · intro m hm e he; rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ e ) ] ; rw [ div_le_iff₀ ( by norm_cast; linarith [ he0 e he ] ) ] ; ring_nf at *; norm_num at *;
    cases abs_cases ( m : ℝ ) <;> nlinarith [ show ( m : ℝ ) ≥ -N by exact_mod_cast hm.1, show ( m : ℝ ) ≤ N by exact_mod_cast hm.2, show ( e : ℝ ) ≥ Emin by exact_mod_cast hEmin e he ];
  · intro m hm;
    -- For each edge e, |(m:ℝ)/e|^3 ≤ N/Emin * (m^2 * 1/e^2).
    have h_edge_bound : ∀ e ∈ D.E, |(m : ℝ) / e| ^ 3 ≤ (N / Emin) * ((m : ℝ) ^ 2 * (1 / e ^ 2 : ℝ)) := by
      intros e he
      have h_abs : |(m : ℝ) / e| ≤ N / Emin := by
        rw [ abs_div, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ e ) ];
        gcongr <;> norm_cast;
        · exact abs_le.mpr ⟨ by linarith [ Finset.mem_Icc.mp hm ], by linarith [ Finset.mem_Icc.mp hm ] ⟩;
        · exact hEmin e he;
      convert mul_le_mul_of_nonneg_right h_abs ( show 0 ≤ ( m : ℝ ) ^ 2 * ( 1 / e ^ 2 : ℝ ) by positivity ) using 1 ; ring;
      cases abs_cases ( ( m : ℝ ) * ( e : ℝ ) ⁻¹ ) <;> simp +decide [ * ] <;> ring;
    refine' le_trans ( Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left ( h_edge_bound e he ) ( by norm_num ) ) _ ; norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *;
    refine' le_trans ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( show ( m : ℝ ) ^ 2 ≤ N ^ 2 by norm_cast; nlinarith ) <| Finset.sum_nonneg fun _ _ => inv_nonneg.2 <| sq_nonneg _ ) <| by positivity ) <| by positivity ) _;
    nlinarith [ mul_inv_cancel₀ ( ne_of_gt hB ), show ( 0 : ℝ ) ≤ N / Emin by positivity ]

/-
Obtain the residual mass batch `Q` for the high-block gadget set `S`,
discharging the `k0`-large side conditions (`hsum`/`hlarge`/`hTsmall`).
-/
lemma r2_getQ {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b)
    (BS : BlockSystem) (S : Finset ℕ)
    (hsub : blockPrimes BS.k0 ⊆ blockSupport BS)
    (hSge : ∀ s ∈ S, 2 ^ (2 * BS.k0) ≤ s)
    (hRout : ∀ r ∈ b.primeFactors, r ∉ blockSupport BS)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges BS) ≤ 3 / (4 * (b : ℝ)))
    (k1 : ℕ) (hk15 : 5 ≤ k1) (hk1le : k1 ≤ BS.k0)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤ ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))
    (hk0big : 1000 * S.card + 1000 * b + 100000 ≤ BS.k0)
    (hk0T : T.sup id + 1 ≤ BS.k0) :
    ∃ Q : Finset ℕ,
      R2MassBatchSupply ((⟨BS, ∅, b.primeFactors, S⟩ : R2ConcreteData T b).withQ Q) := by
  convert exists_r2_data_of_numerics_set hb BS S hsub ( fun s hs => ?_ ) hRout hctrl ?_ k1 hk15 hk1le hload ?_ ?_ using 1;
  · exact le_trans ( pow_le_pow_right₀ ( by norm_num ) ( by linarith ) ) ( hSge s hs );
  · rw [ div_add_div, div_lt_div_iff₀ ] <;> norm_cast <;> try positivity;
    -- We'll use that $b \leq BS.k0$ and $S.card \leq BS.k0$ to bound the terms.
    have h_bound : b ≤ BS.k0 ∧ S.card ≤ BS.k0 := by
      grind;
    -- We'll use that $b \leq BS.k0$ and $S.card \leq BS.k0$ to bound the terms and simplify the inequality.
    have h_bound : b * #S * #b.primeFactors ≤ BS.k0 ^ 3 := by
      exact le_trans ( Nat.mul_le_mul ( Nat.mul_le_mul h_bound.1 h_bound.2 ) ( show #b.primeFactors ≤ BS.k0 from le_trans ( Finset.card_le_card ( show b.primeFactors ⊆ Finset.Icc 1 b from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors hx, Nat.le_of_mem_primeFactors hx ⟩ ) ) ( by norm_num; linarith ) ) ) ( by nlinarith only [ h_bound ] );
    have h_exp_growth : 2 ^ BS.k0 > BS.k0 ^ 3 * 2 := by
      exact Nat.le_induction ( by norm_num ) ( fun n hn ih => by norm_num [ Nat.pow_succ' ] at * ; nlinarith only [ ih, hn ] ) _ ( show BS.k0 ≥ 30 by linarith );
    nlinarith [ Nat.zero_le ( b * #S * #b.primeFactors ) ];
  · nlinarith [ show 2 ^ BS.k0 > BS.k0 by exact Nat.recOn BS.k0 ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ], Nat.zero_le ( #S ) ];
  · intro e he; nlinarith [ show e ≤ T.sup id from Finset.le_sup ( f := id ) he, show 2 ^ BS.k0 > BS.k0 from Nat.recOn BS.k0 ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ] ;

/-
Prime-counting upper bound on a dyadic block, from Mathlib's `primorial_le_4_pow`:
the primes in `[2^k, 2^{k+1})` number at most `2^(k+2)/k`.  This is the missing
*upper* companion to the density axiom, and is what makes `σ_E ≤ K·σ_ctrl` hold with a
*constant* `K` (not `~k0`).
-/
lemma dyadic_block_card_upper (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) * ((dyadicBlock k).card : ℝ) ≤ (2 : ℝ) ^ (k + 2) := by
  have h_card : (dyadicBlock k).card * k ≤ 2 ^ (k + 2) := by
    have h_card : (2 ^ k) ^ (dyadicBlock k).card ≤ 4 ^ (2 ^ (k + 1)) := by
      have h_prod : (∏ p ∈ dyadicBlock k, p) ≤ 4 ^ (2 ^ (k + 1)) := by
        refine' le_trans _ ( primorial_le_4_pow ( 2 ^ ( k + 1 ) ) );
        refine' Finset.prod_le_prod_of_subset_of_one_le' _ _ <;> norm_num [ dyadicBlock ];
        · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ] ), Finset.mem_filter.mp hx |>.2 ⟩;
        · exact fun i hi₁ hi₂ hi₃ => Nat.Prime.pos hi₂;
      refine le_trans ?_ h_prod;
      exact le_trans ( by norm_num [ pow_mul ] ) ( Finset.prod_le_prod' fun x hx => show x ≥ 2 ^ k from Finset.mem_filter.mp hx |>.2 |> fun hx' => by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ] );
    convert Nat.pow_le_pow_iff_right ( show 1 < 2 by norm_num ) |>.1 ( show 2 ^ ( k * #(dyadicBlock k) ) ≤ 2 ^ ( 2 ^ ( k + 2 ) ) from ?_ ) using 1 <;> ring_nf at *;
    exact h_card.trans ( by rw [ show ( 4 : ℕ ) = 2 ^ 2 by norm_num, ← pow_mul ] ; ring_nf; norm_num );
  norm_cast ; linarith

/-
The block-support reciprocal-square sum decays like `2^{-k0}/k0` (using the
prime-counting upper bound).
-/
lemma r2_blockSupport_inv_sq_le (BS : BlockSystem) (hk0 : 1 ≤ BS.k0) :
    ∑ p ∈ blockSupport BS, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ 8 / ((BS.k0 : ℝ) * (2 : ℝ) ^ BS.k0) := by
  have h_sum_le_card : (blockSupport BS).sum (fun p => (1 : ℝ) / p ^ 2) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (dyadicBlock k).card * (1 / (2 ^ k) ^ 2 : ℝ) := by
    have h_sum_le_card : (blockSupport BS).sum (fun p => (1 : ℝ) / p ^ 2) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (BS.P k).sum (fun p => (1 : ℝ) / p ^ 2) := by
      rw [ ← Finset.sum_biUnion ];
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( by aesop_cat ) fun _ _ _ => by positivity;
      · exact fun x hx y hy hxy => blocks_disjoint BS hxy;
    refine le_trans h_sum_le_card <| Finset.sum_le_sum fun k hk => ?_;
    refine' le_trans ( Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le ( by positivity ) <| pow_le_pow_left₀ ( by positivity ) ( show ( p : ℝ ) ≥ 2 ^ k from mod_cast _ ) 2 ) _;
    · exact_mod_cast BS.hwindow k p hp |>.1;
    · simp +zetaDelta at *;
      exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_le_card <| show BS.P k ⊆ dyadicBlock k from fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr <| BS.hwindow k x hx, BS.hprime k x hx ⟩ ) <| by positivity;
  -- Using the upper bound on the cardinality of `dyadicBlock k`, we can further bound the sum.
  have h_card_bound : ∀ k ∈ Finset.Icc BS.k0 BS.K, (dyadicBlock k).card * (1 / (2 ^ k) ^ 2 : ℝ) ≤ 4 / (BS.k0 * 2 ^ k) := by
    intro k hk
    have h_card_bound : (dyadicBlock k).card ≤ (2 ^ (k + 2)) / k := by
      have := dyadic_block_card_upper k ( by linarith [ Finset.mem_Icc.mp hk ] ) ; rw [ Nat.le_div_iff_mul_le ( by linarith [ Finset.mem_Icc.mp hk ] ) ] ; norm_cast at *;
      linarith;
    rw [ mul_one_div, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ pow_succ' ] at *;
    · exact le_trans ( Nat.mul_le_mul_right _ h_card_bound ) ( by nlinarith [ Nat.div_mul_le_self ( 2 * ( 2 * 2 ^ k ) ) k, pow_pos ( zero_lt_two' ℕ ) k, pow_pos ( zero_lt_two' ℕ ) ( k + 1 ), pow_pos ( zero_lt_two' ℕ ) ( k + 2 ), mul_le_mul_left' hk.1 ( 2 ^ k ) ] );
    · linarith;
  refine le_trans h_sum_le_card <| le_trans ( Finset.sum_le_sum h_card_bound ) ?_;
  erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, pow_add ] ; ring_nf ; norm_num;
  norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  rw [ geom_sum_eq ] <;> ring <;> norm_num

/-- **Light extra edges.**  The mass-batch and gadget edges carry only a bounded
multiple of the control deviation in reciprocal-square mass.  Combined with
`sigmaCtrl_ge_strong`, this yields `σ_E ≤ K·σ_ctrl` with an explicit constant. -/
lemma r2_extra_inv_sq_le {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hk0 : 14 ≤ D.BS.k0)
    (hk0big : 1000 * D.S.card + 1000 * b + 100000 ≤ D.BS.k0)
    (QB : R2MassBatchSupply D)
    (hSge : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s)
    (hRpos : ∀ r ∈ D.R, 2 ≤ r) (hRcard : D.R.card ≤ b) :
    ∑ e ∈ D.E \ ctrlEdges D.BS, (1 : ℝ) / (e : ℝ) ^ 2
      ≤ 1000000 * (sigmaCtrl D.BS) ^ 2 := by
  have hQ_mass : ∑ e ∈ D.Q, (1 : ℝ) / e ^ 2 ≤ (8 / ((D.BS.k0 : ℝ) * (2 : ℝ) ^ D.BS.k0)) ^ 2 := by
    have hQ : (∑ e ∈ D.Q, (1 : ℝ) / (e : ℝ) ^ 2) ≤ (∑ p ∈ blockSupport D.BS, (1 : ℝ) / (p : ℝ) ^ 2) ^ 2 := by
      have := QB.hQpair
      have h_sum_Q_le : D.Q.sum (fun e => (1 : ℝ) / e ^ 2) ≤ (blockSupport D.BS ×ˢ blockSupport D.BS).sum (fun pq => (1 : ℝ) / (pq.1 * pq.2) ^ 2) := by
        choose! p q hp hq hpq he using this
        have h_sum_Q_le : D.Q.sum (fun e => (1 : ℝ) / e ^ 2) ≤ (Finset.image (fun e => (p e, q e)) D.Q).sum (fun pq => (1 : ℝ) / (pq.1 * pq.2) ^ 2) := by
          rw [ Finset.sum_image ]
          · exact Finset.sum_le_sum fun x hx => by rw [ ← Nat.cast_mul, ← he x hx ]
          · intros e he e' he' h_eq
            grind
        exact h_sum_Q_le.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.image_subset_iff.mpr fun e he => Finset.mem_product.mpr ⟨ hp e he, hq e he ⟩ ) fun _ _ _ => by positivity )
      convert h_sum_Q_le using 1 ; norm_num [ Finset.sum_product, mul_pow ] ; ring
      simp +decide only [sq, ← Finset.mul_sum _ _ _, ← Finset.sum_mul]
    exact hQ.trans ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => by positivity ) ( r2_blockSupport_inv_sq_le D.BS ( by linarith ) ) _ )
  have hgadget_mass : ∑ e ∈ gadgetEdges D.R D.S, (1 : ℝ) / e ^ 2 ≤ (D.R.card * D.S.card) * (2 : ℝ) ^ (-4 * D.BS.k0 : ℝ) := by
    refine' le_trans ( Finset.sum_le_sum fun e he => one_div_le_one_div_of_le ( by positivity ) ( show ( e : ℝ ) ^ 2 ≥ ( 2 ^ ( 2 * D.BS.k0 ) ) ^ 2 by
      gcongr ; norm_cast ; simp_all +decide [ gadgetEdges ]
      obtain ⟨ a, c, ⟨ ha, hc ⟩, rfl ⟩ := he; nlinarith [ hRpos a ha, hSge c hc ] ) ) _ ; norm_num [ ← pow_mul ] ; ring_nf ; norm_num
    norm_num [ Real.rpow_neg, Real.div_rpow ]
    norm_cast ; norm_num [ gadgetEdges_card_le_product ]
    exact mul_le_mul ( mod_cast gadgetEdges_card_le_product D.R D.S ) ( by norm_num [ ← inv_pow ] ) ( by positivity ) ( by positivity )
  have h_combined : ∑ e ∈ D.E \ ctrlEdges D.BS, (1 : ℝ) / e ^ 2 ≤ (8 / ((D.BS.k0 : ℝ) * (2 : ℝ) ^ D.BS.k0)) ^ 2 + (b * D.S.card) * (2 : ℝ) ^ (-4 * D.BS.k0 : ℝ) := by
    have h_subset : ∑ e ∈ D.E \ ctrlEdges D.BS, (1 : ℝ) / e ^ 2 ≤ ∑ e ∈ D.Q ∪ gadgetEdges D.R D.S, (1 : ℝ) / e ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro e he
      rw [ Finset.mem_sdiff ] at he
      have heE := he.1
      have henc := he.2
      rw [ R2ConcreteData.E, r2Edges ] at heE
      rw [ Finset.mem_union ]
      rcases Finset.mem_union.mp heE with h | h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact absurd h' henc
        · exact Or.inl h'
      · exact Or.inr h
    refine le_trans h_subset ?_
    refine le_trans ?_ ( add_le_add hQ_mass <| hgadget_mass.trans ?_ )
    · rw [ ← Finset.sum_union_inter ] ; norm_num
      exact Finset.sum_nonneg fun _ _ => by positivity
    · exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mod_cast hRcard ) ( Nat.cast_nonneg _ ) ) ( by positivity )
  have h_second_term : (b * D.S.card : ℝ) * (2 : ℝ) ^ (-4 * D.BS.k0 : ℝ) ≤ (sigmaCtrl D.BS) ^ 2 := by
    have h_second_term : (b * D.S.card : ℝ) * (2 : ℝ) ^ (-4 * D.BS.k0 : ℝ) ≤ (1 / (100 * (D.BS.k0 : ℝ) * (2 : ℝ) ^ D.BS.k0)) ^ 2 := by
      rw [ Real.rpow_mul ] <;> norm_num ; ring_nf ; norm_num at *
      rw [ pow_mul' ] ; norm_num ; ring_nf ; norm_num at *
      field_simp
      refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( show ( b : ℝ ) * #D.S ≤ ( D.BS.k0 : ℝ ) ^ 2 / 1000000 by
        rw [ le_div_iff₀ ] <;> norm_cast ; nlinarith only [ hk0big, sq ( D.BS.k0 - 1000 : ℤ ) ] ) <| by positivity ) <| by positivity ) <| by positivity ) _ ; ring_nf ; norm_num at *
      refine' Nat.le_induction _ _ D.BS.k0 hk0 <;> norm_num [ pow_succ' ] at *
      intro n hn ih; ring_nf at *; norm_num at *
      nlinarith [ show ( n : ℝ ) ≥ 14 by norm_cast, pow_pos ( by positivity : 0 < ( n : ℝ ) ) 2, pow_pos ( by positivity : 0 < ( n : ℝ ) ) 3, pow_pos ( by positivity : 0 < ( n : ℝ ) ) 4, pow_pos ( by positivity : 0 < ( 1 / 16 : ℝ ) ) n, pow_pos ( by positivity : 0 < ( 1 / 4 : ℝ ) ) n ]
    refine le_trans h_second_term ?_
    exact pow_le_pow_left₀ ( by positivity ) ( sigmaCtrl_ge_strong D.BS hk0 ) 2
  refine le_trans h_combined <| le_trans ( add_le_add ( show ( 8 / ( D.BS.k0 * 2 ^ D.BS.k0 : ℝ ) ) ^ 2 ≤ 999999 * sigmaCtrl D.BS ^ 2 from ?_ ) h_second_term ) ?_
  · refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( sigmaCtrl_ge_strong D.BS hk0 ) 2 ) ( by positivity ) ) ; ring_nf ; norm_num
    exact mul_le_mul_of_nonneg_left ( by norm_num ) ( by positivity )
  · linarith

/-- **Main-arc CRT label lane.** Every extra-minor frequency `h` lies on the main
arc, hence carries an integer block-label `m = mainArcWitnessLabel D C h` with
`|m| ≤ C/σ ≤ N`. This packages that label data as
`R2ExtraIntFrequencyLabelData`, the input the gadget reservoir reads when damping
each extra frequency. -/
def r2FreqLabelLane {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) (C : ℝ)
    (hCN : C / sigmaCtrl D.BS ≤ (N : ℝ)) :
    ∀ MA : MainArcFields D.E W.theta b D.L N,
      R2ExtraIntFrequencyLabelData D W N MA
        ((mainArcClassificationData D W N C).Sblock MA)
        ((mainArcClassificationData D W N C).Sextra MA) :=
  fun MA => intFrequencyLabelData_of_mainArcClassification D W N C MA (by
    intro m hm
    exact Finset.mem_Icc.mpr
      ⟨by exact_mod_cast neg_le_of_abs_le <| hm.trans hCN,
        by exact_mod_cast le_of_abs_le <| hm.trans hCN⟩)

/-- **Block-lane fibre-tail certificate.** On the block-minor part the
frequency-to-assignment map is `b`-to-1 (bounded multiplicity from the chosen
period `L = b · ∏ blockSupport`), so the block fibre tail is controlled by
`Bblock = b · (η + Ctail·exp(-8C²/9))/σ_ctrl`.  This is the block lane of the
frequency endgame, produced for every main-arc field `MA`. -/
def r2_freqLane_block {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C η Ctail : ℝ) (hC : 1 ≤ C)
    (heL : ∀ e ∈ D.E, e ∣ D.L) (he0 : ∀ e ∈ D.E, 0 < e) (hL : 0 < D.L)
    (hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p) :
    ∀ MA : MainArcFields D.E W.theta b D.L N,
      R2BlockFiberTailData D W N MA
        ((mainArcClassificationData D W N C).Sblock MA)
        ((b : ℝ) * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl D.BS)
        η Ctail :=
  fun MA => by
    apply r2_blockFiberTail D W N MA ((mainArcClassificationData D W N C).Sblock MA) C η Ctail
      ((b:ℝ)*(η+Ctail*Real.exp (-C^2*(16/9)/2))/sigmaCtrl D.BS) hC heL he0 hL hLeq (by
      exact fun x hx => mainArcFields_mem_range_of_mem_Sm MA ( mem_blockMinorPart.mp hx |>.1 )) (by
      intro h hh; exact (by
      exact Finset.mem_filter.mp ( Finset.mem_filter.mp hh |>.2 ) |>.2)) (by
      grind +extAll)

/-- **Extra-frequency count certificate.** Each extra-minor frequency is the CRT
constant assignment of a single label `m` with `|m| ≤ N`, and every label fibre
has at most `b` frequencies in `range L`; hence at most `b·(2N+1)` extra
frequencies.  Multiplying by the per-frequency damping budget `Dmp` gives the
uniform extra-count budget `Bextra = b·(2N+1)·Dmp`. -/
lemma r2_freqLane_extra_count {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C Dmp : ℝ) (hNnonneg : 0 ≤ N) (hDmpnn : 0 ≤ Dmp)
    (hCN : C / sigmaCtrl D.BS ≤ (N : ℝ))
    (hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p) :
    ∀ MA : MainArcFields D.E W.theta b D.L N,
      ((extraMinorPart MA.Sm ((mainArcClassificationData D W N C).Sblock MA)
          ((mainArcClassificationData D W N C).Sextra MA)).card : ℝ) * Dmp
        ≤ (b : ℝ) * (2 * (N : ℝ) + 1) * Dmp :=
  fun MA => by
    gcongr
    convert r2_extra_count_le D W N C hNnonneg hCN hLeq MA using 1

/-- **Gadget pointwise damping certificate.** For every extra-minor frequency the
chosen `R`-prime sibling has `rfun h ∣ b`, so `1 ≤ rfun h ≤ b`, and damping by
the `G = |S|` gadget primes drives the per-frequency factor
`√(1-(8/9)/rfun²)^G` below the worst-case bound `√(1-(8/9)/b²)^G ≤ Dmp`.  This is
the gadget lane of the frequency endgame, using the labels from
`r2FreqLabelLane`. -/
lemma r2_freqLane_gadget_damping {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C Dmp : ℝ) (G : ℕ)
    (hbpos : 0 < b) (hsqfree : Squarefree b)
    (hcovR : CoversPrimeDivisors D.R b) (hcopB : BlockSupportCoprimeWith D.BS b)
    (hCN : C / sigmaCtrl D.BS ≤ (N : ℝ))
    (hScard : D.S.card = G)
    (hG : (Real.sqrt (1 - (8 / 9) / (b : ℝ) ^ 2)) ^ G ≤ Dmp) :
    ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∀ h ∈ extraMinorPart MA.Sm ((mainArcClassificationData D W N C).Sblock MA)
          ((mainArcClassificationData D W N C).Sextra MA),
        (Real.sqrt (1 - (8 / 9) /
          (((r2ExtraSiblingChoice_of_intLabelData D W N MA
            ((mainArcClassificationData D W N C).Sblock MA)
            ((mainArcClassificationData D W N C).Sextra MA)
            (r2FreqLabelLane D W N C hCN MA) hbpos hsqfree hcovR hcopB).rfun h : ℝ) ^ 2))) ^
              D.S.card ≤ Dmp :=
  fun MA h hh => by
    refine' le_trans _ hG
    rw [ hScard ]
    gcongr
    · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( by exact ( r2ExtraSiblingChoice_of_intLabelData D W N MA _ _ _ hbpos hsqfree hcovR hcopB ).hrprime h hh ) ) )
    · exact Nat.le_of_dvd hbpos ( r2ExtraSiblingChoice_of_intLabelData D W N MA _ _ _ hbpos hsqfree hcovR hcopB |>.hrdvd h hh )

/-- **Small-label gap certificate.** Every extra-minor frequency carries a label
`m` with `|m| ≤ C/σ ≤ N`, while each gadget prime `s ∈ S` satisfies
`2^{2k₀} ≤ s`; combined with `2N < 2^{2k₀}` this gives the gap `2|m| < s` the
gadget reservoir needs to read each label modulo `s`. -/
lemma r2_freqLane_label_small_gap {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) (C : ℝ)
    (hCN : C / sigmaCtrl D.BS ≤ (N : ℝ))
    (hN2 : 2 * N < (2 : ℤ) ^ (2 * D.BS.k0))
    (hSge : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s) :
    ∀ MA : MainArcFields D.E W.theta b D.L N,
      ∀ h ∈ extraMinorPart MA.Sm ((mainArcClassificationData D W N C).Sblock MA)
          ((mainArcClassificationData D W N C).Sextra MA),
        ∀ s ∈ D.S, 2 * |(r2FreqLabelLane D W N C hCN MA).mfun h| < (s : ℤ) := by
  intro MA h hh s hs
  -- the label is the main-arc witness, with `|label| ≤ C/σ ≤ N`
  rw [mem_extraMinorPart] at hh
  have hmain : freqAssignmentOf D h ∈ mainArc D.BS C := by
    have h22 := hh.2.2
    simp only [mainArcClassificationData, mainArcExtraSet, Finset.mem_filter] at h22
    exact h22.2
  have hspec := Classical.choose_spec hmain
  have hlblval : (r2FreqLabelLane D W N C hCN MA).mfun h = Classical.choose hmain := by
    simp [r2FreqLabelLane, intFrequencyLabelData_of_mainArcClassification,
      mainArcWitnessLabel, hmain]
  have hlabel_le : |((Classical.choose hmain : ℤ) : ℝ)| ≤ (N : ℝ) := hspec.1.trans hCN
  have hlabel_leN : |Classical.choose hmain| ≤ N := by
    have := hlabel_le
    rw [← Int.cast_abs] at this
    exact_mod_cast this
  have hsge2 : (2 : ℤ) ^ (2 * D.BS.k0) ≤ (s : ℤ) := by exact_mod_cast hSge s hs
  rw [hlblval]
  have := abs_le.mp hlabel_leN
  omega

/-
Assemble the frequency-minor endgame lanes from the foundation/gadget data and
the parameter choices: the component scale (ρ = N), the block fiber-tail lane
(`r2_freqLane_block`), the main-arc CRT label lane (`r2FreqLabelLane`), the
small-label gap (`r2_freqLane_label_small_gap`), the extra-frequency count budget
(`r2_freqLane_extra_count`), and the `G`-gadget per-frequency damping
(`r2_freqLane_gadget_damping`).
-/
lemma r2_buildFreqLanes {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C η Ctail Dmp : ℝ) (G : ℕ)
    (hbpos : 0 < b) (hsqfree : Squarefree b)
    (hcovR : CoversPrimeDivisors D.R b) (hcopB : BlockSupportCoprimeWith D.BS b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r) (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hRdvd : ∀ r ∈ D.R, r ∣ b) (hSblock : D.S ⊆ blockSupport D.BS)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T)
    (heL : ∀ e ∈ D.E, e ∣ D.L) (he0 : ∀ e ∈ D.E, 0 < e) (hL : 0 < D.L)
    (hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p)
    (hC : 1 ≤ C) (hNnonneg : 0 ≤ N)
    (hSge : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s) (hScard : D.S.card = G)
    (hCN : C / sigmaCtrl D.BS ≤ (N : ℝ))
    (hN2 : 2 * N < (2 : ℤ) ^ (2 * D.BS.k0))
    (hDmpnn : 0 ≤ Dmp)
    (hG : (Real.sqrt (1 - (8 / 9) / (b : ℝ) ^ 2)) ^ G ≤ Dmp) :
    Nonempty (R2MinorEndgameFrequencyLanes D W N
      ((b : ℝ) * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl D.BS)
      ((b : ℝ) * (2 * (N : ℝ) + 1) * Dmp) η Ctail (N : ℝ) Dmp
      (mainArcClassificationData D W N C)) := by
  constructor;
  apply_rules [ R2MinorEndgameFrequencyLanes.mk ];
  use by norm_cast;
  exact le_mul_of_one_le_right ( by positivity ) ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by positivity );
  exact 1;
  exact le_mul_of_one_le_right ( by positivity ) ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by positivity );
  exact fun r hr => Nat.Prime.pos ( hRprime r hr );
  -- block lane: block-fibre-tail certificate
  exact r2_freqLane_block D W N C η Ctail hC heL he0 hL hLeq;
  exact fun MA h hh => Finset.Subset.refl _;
  rotate_right;
  -- main-arc CRT label lane
  exact r2FreqLabelLane D W N C hCN;
  · -- small-label gap `2|m| < s` for the gadget primes
    exact r2_freqLane_label_small_gap D W N C hCN hN2 hSge;
  · -- extra-frequency count budget
    exact r2_freqLane_extra_count D W N C Dmp hNnonneg hDmpnn hCN hLeq;
  · -- gadget pointwise damping
    exact r2_freqLane_gadget_damping D W N C Dmp G hbpos hsqfree hcovR hcopB hCN hScard hG

/-- Numeric main-arc fields for the R2 construction, extracted as its own
declaration so `D` stays opaque (no `Classical.choose` unfolding / `isDefEq`
blow-up) and it gets its own elaboration budget. -/
lemma r2_close_numericFields {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ) (σ C : ℝ)
    (hσpos : 0 < σ)
    (he0 : ∀ e ∈ D.E, 0 < e)
    (QB : R2MassBatchSupply D)
    (hSge : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s)
    (hRpos' : ∀ r ∈ D.R, 2 ≤ r)
    (hsumE : ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1000001 * σ ^ 2)
    (hsigmaE_lb : Real.sqrt (2 / 9) * σ ≤ Real.sqrt (sigmaE2 D.E W.theta))
    (hNnonneg : 0 ≤ N) (hCge3 : (3 : ℝ) ≤ C)
    (hNlo : C / σ ≤ (N : ℝ)) (hNsigma : (N : ℝ) * σ ≤ C + 1)
    (hk0dom : 1000000 * (Nat.ceil C + 1) ^ 4 ≤ D.BS.k0)
    (hNreal : (N : ℝ) ≤ 100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 + 1) :
    MainArcNumericFields D.E W.theta N := by
  have hk0big6 : 1000000 ≤ D.BS.k0 := by
    have h1 : 1 ≤ (Nat.ceil C + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [hk0dom, h1]
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hNlo
  have hEminN : ∀ e ∈ D.E, 2 ^ (2 * D.BS.k0) ≤ e := by
    intro e he
    rw [R2ConcreteData.E, r2Edges] at he
    have hpoweq : (2 : ℕ) ^ (2 * D.BS.k0) = 2 ^ D.BS.k0 * 2 ^ D.BS.k0 := by rw [two_mul, pow_add]
    rcases Finset.mem_union.mp he with hcQ | hg
    · rcases Finset.mem_union.mp hcQ with hc | hq
      · rw [hpoweq]; exact ctrlEdges_ge_k0_square D.BS hc
      · obtain ⟨p, q, hp, hq', _, rfl⟩ := QB.hQpair e hq
        rw [hpoweq]
        exact Nat.mul_le_mul (blockSupport_ge_pow_k0 D.BS hp) (blockSupport_ge_pow_k0 D.BS hq')
    · rw [mem_gadgetEdges] at hg
      obtain ⟨r, hr, s, hs, rfl⟩ := hg
      exact le_trans (hSge s hs) (Nat.le_mul_of_pos_left _ (by have := hRpos' r hr; omega))
  have hEmin : ∀ e ∈ D.E, (2 : ℝ) ^ (2 * D.BS.k0) ≤ (e : ℝ) := by
    intro e he; exact_mod_cast hEminN e he
  have hN10nat : 10 * (100 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 1) ≤ 2 ^ (2 * D.BS.k0) := by
    have hc := cube_lt_two_pow D.BS.k0 (by omega)
    have hpoweq : (2 : ℕ) ^ (2 * D.BS.k0) = 2 ^ D.BS.k0 * 2 ^ D.BS.k0 := by rw [two_mul, pow_add]
    have h2le : 2 ≤ 2 ^ D.BS.k0 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ D.BS.k0 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkey : 1000 * D.BS.k0 ^ 2 + 10 ≤ 2 ^ D.BS.k0 := by
      nlinarith only [hc, hk0big6, mul_le_mul_left hk0big6 (D.BS.k0 ^ 2)]
    calc 10 * (100 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 1)
        = (1000 * D.BS.k0 ^ 2) * 2 ^ D.BS.k0 + 10 := by ring
      _ ≤ (1000 * D.BS.k0 ^ 2) * 2 ^ D.BS.k0 + 10 * 2 ^ D.BS.k0 := by nlinarith only [h2le]
      _ = (1000 * D.BS.k0 ^ 2 + 10) * 2 ^ D.BS.k0 := by ring
      _ ≤ 2 ^ D.BS.k0 * 2 ^ D.BS.k0 := Nat.mul_le_mul_right _ hkey
      _ = 2 ^ (2 * D.BS.k0) := hpoweq.symm
  have h10N : 10 * (N : ℝ) ≤ (2 : ℝ) ^ (2 * D.BS.k0) := by
    have hd : 10 * (100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 + 1) ≤ (2 : ℝ) ^ (2 * D.BS.k0) := by
      calc 10 * (100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 + 1)
          = ((10 * (100 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 1) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ (2 * D.BS.k0) : ℕ) : ℝ) := by exact_mod_cast hN10nat
        _ = (2 : ℝ) ^ (2 * D.BS.k0) := by push_cast; ring
    linarith [hNreal, hd]
  have hN : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ) := by
    have hlb : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ 1 / (Real.sqrt (2 / 9) * σ) :=
      one_div_le_one_div_of_le (by positivity) hsigmaE_lb
    have hsq : (1 : ℝ) / 3 ≤ Real.sqrt (2 / 9) := by
      rw [show (1 : ℝ) / 3 = Real.sqrt (1 / 9) by
        rw [show (1 : ℝ) / 9 = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt; norm_num
    have h2 : 1 / (Real.sqrt (2 / 9) * σ) ≤ 3 / σ := by
      rw [div_le_div_iff₀ (by positivity) hσpos, one_mul]
      nlinarith only [hsq, hσpos]
    have h3 : (3 : ℝ) / σ ≤ (N : ℝ) := by
      rw [div_le_iff₀ hσpos]
      have hh := hNlo; rw [div_le_iff₀ hσpos] at hh
      nlinarith only [hh, hCge3]
    linarith [hlb, h2, h3]
  have hsumsq : (N : ℝ) ^ 2 * (∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2)
      ≤ (N : ℝ) ^ 2 * (1000001 * σ ^ 2) :=
    mul_le_mul_of_nonneg_left hsumE (by positivity)
  have hsmallN : (N : ℝ) / (2 : ℝ) ^ (2 * D.BS.k0)
      ≤ 1 / (1000000 * ((N : ℝ) ^ 2 * (1000001 * σ ^ 2))) := by
    have hCk0' : C ≤ (D.BS.k0 : ℝ) := by
      have hcl : Nat.ceil C ≤ D.BS.k0 := by
        have hp : Nat.ceil C + 1 ≤ (Nat.ceil C + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
        nlinarith only [hp, hk0dom]
      calc C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
        _ ≤ (D.BS.k0 : ℝ) := by exact_mod_cast hcl
    have hk0lb : 256000000 ≤ D.BS.k0 := by
      have hp : (256 : ℕ) ≤ (Nat.ceil C + 1) ^ 4 := by
        have h3 : 3 ≤ Nat.ceil C := by
          have : (3 : ℝ) ≤ (Nat.ceil C : ℝ) := le_trans hCge3 (Nat.le_ceil C)
          exact_mod_cast this
        calc (256 : ℕ) = 4 ^ 4 := by norm_num
          _ ≤ (Nat.ceil C + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      nlinarith only [hp, hk0dom]
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ D.BS.k0 := one_le_pow₀ (by norm_num)
    have hk0r : (256000000 : ℝ) ≤ (D.BS.k0 : ℝ) := by exact_mod_cast hk0lb
    have hquart : (500000000000000 : ℕ) * D.BS.k0 ^ 4 ≤ 2 ^ D.BS.k0 :=
      quartic_le_two_pow_of_le_sq _ D.BS.k0 (by nlinarith only [hk0lb]) (by omega)
    have hquartr : (500000000000000 : ℝ) * (D.BS.k0 : ℝ) ^ 4 ≤ (2 : ℝ) ^ D.BS.k0 := by
      exact_mod_cast hquart
    have hNσ : (N : ℝ) * σ ≤ (D.BS.k0 : ℝ) + 1 := le_trans hNsigma (by linarith [hCk0'])
    have hNσ2 : ((N : ℝ) * σ) ^ 2 ≤ ((D.BS.k0 : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ (N : ℝ) * σ := by positivity
      nlinarith only [hNσ, this]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hlhs : (N : ℝ) * (1000000 * ((N : ℝ) ^ 2 * (1000001 * σ ^ 2)))
        = 1000000 * 1000001 * ((N : ℝ) * ((N : ℝ) * σ) ^ 2) := by ring
    rw [hlhs]
    have hprod : (N : ℝ) * ((N : ℝ) * σ) ^ 2
        ≤ (101 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0) * (4 * (D.BS.k0 : ℝ) ^ 2) := by
      refine mul_le_mul ?_ ?_ (sq_nonneg _) (by positivity)
      · calc (N : ℝ) ≤ 100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 + 1 := hNreal
          _ ≤ 101 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 := by nlinarith only [hk0r, htwo]
      · calc ((N : ℝ) * σ) ^ 2 ≤ ((D.BS.k0 : ℝ) + 1) ^ 2 := hNσ2
          _ ≤ 4 * (D.BS.k0 : ℝ) ^ 2 := by nlinarith only [hk0r]
    calc 1000000 * 1000001 * ((N : ℝ) * ((N : ℝ) * σ) ^ 2)
        ≤ 1000000 * 1000001 *
            ((101 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0) * (4 * (D.BS.k0 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = (1000000 * 1000001 * 404) * ((D.BS.k0 : ℝ) ^ 4 * (2 : ℝ) ^ D.BS.k0) := by ring
      _ ≤ 500000000000000 * ((D.BS.k0 : ℝ) ^ 4 * (2 : ℝ) ^ D.BS.k0) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (500000000000000 * (D.BS.k0 : ℝ) ^ 4) * (2 : ℝ) ^ D.BS.k0 := by ring
      _ ≤ (2 : ℝ) ^ D.BS.k0 * (2 : ℝ) ^ D.BS.k0 :=
          mul_le_mul_of_nonneg_right hquartr (by positivity)
      _ = (2 : ℝ) ^ (2 * D.BS.k0) := by rw [two_mul, pow_add]
  exact r2_numericFields D W N ((2 : ℝ) ^ (2 * D.BS.k0)) ((N : ℝ) ^ 2 * (1000001 * σ ^ 2))
    (by positivity) he0 (by positivity) hEmin hN hNnonneg h10N hsumsq hsmallN


end CircleMethod

end