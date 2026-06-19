import RequestProject.R2ComponentDisjoint
import RequestProject.DyadicBlockUpper

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 base-load upper socket

This leaf isolates the remaining base-load upper condition into separate
control and gadget reciprocal-load budgets.
-/

/-- If every gadget denominator prime lies outside the block support, the fixed
base load splits exactly into control and gadget reciprocal loads. -/
theorem baseLoad_eq_ctrl_add_gadget_of_R_outside
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS) :
    D.baseLoad =
      R2ConcreteData.recipLoad (ctrlEdges D.BS) +
        R2ConcreteData.recipLoad (gadgetEdges D.R D.S) := by
  exact baseLoad_eq_ctrl_add_gadget_of_disjoint D
    (r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport D hRprime hRout)

/-- Separate control/gadget budgets for the R2 base-load upper condition. -/
structure R2BaseLoadBudget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) where
  Cctrl : ℝ
  Cgadget : ℝ
  hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl
  hgadget : R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget
  hsum : Cctrl + Cgadget < 3 / (2 * (b : ℝ))

/-- Component budgets imply the requested strict base-load upper bound. -/
theorem baseLoad_lt_of_budget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS)
    (B : R2BaseLoadBudget D) :
    D.baseLoad < 3 / (2 * (b : ℝ)) := by
  rw [baseLoad_eq_ctrl_add_gadget_of_R_outside D hRprime hRout]
  exact lt_of_le_of_lt (add_le_add B.hctrl B.hgadget) B.hsum

lemma block_recip_sum_le_four_div (BS : BlockSystem) (k : ℕ) (hk : 1 ≤ k) :
    ∑ p ∈ BS.P k, (1 : ℝ) / (p : ℝ) ≤ 4 / (k : ℝ) := by
  refine le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
    (dyadicBlock_recip_sum_le_four_div k hk)
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (BS.hwindow k p hp), BS.hprime k p hp⟩

lemma internalPairs_recip_sum_le_sq (BS : BlockSystem) (k : ℕ) :
    ∑ pq ∈ internalPairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2)
      ≤ (∑ p ∈ BS.P k, (1 : ℝ) / (p : ℝ)) ^ 2 := by
  have hsub : internalPairs BS k ⊆ BS.P k ×ˢ BS.P k := by
    intro pq hpq
    rw [internalPairs, Finset.mem_filter] at hpq
    exact hpq.1
  calc
    ∑ pq ∈ internalPairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2)
        ≤ ∑ pq ∈ BS.P k ×ˢ BS.P k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ p ∈ BS.P k, (1 : ℝ) / (p : ℝ)) ^ 2 := by
      rw [Finset.sum_product]
      rw [sq]
      simp [Nat.cast_mul, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_assoc]

lemma bipartitePairs_recip_sum_eq_mul (BS : BlockSystem) (k : ℕ) :
    ∑ pq ∈ bipartitePairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2)
      =
        (∑ q ∈ BS.P (k + 1), (1 : ℝ) / (q : ℝ)) *
          (∑ p ∈ BS.P k, (1 : ℝ) / (p : ℝ)) := by
  rw [bipartitePairs, Finset.sum_product_right]
  simp [Nat.cast_mul, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_assoc]

lemma inv_sq_sum_Icc_le (k0 K : ℕ) (hk0 : 2 ≤ k0) :
    ∑ k ∈ Finset.Icc k0 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / ((k0 : ℝ) - 1) := by
  by_cases hK : k0 ≤ K
  · have h_sum_bound : ∀ n : ℕ, k0 ≤ n → (1 : ℝ) / (n : ℝ) ^ 2 ≤
        1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
      intro n hn
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans hk0 hn
      rw [div_sub_div, div_le_div_iff₀] <;> nlinarith
    have h_telescope : ∀ N : ℕ, k0 ≤ N →
        (∑ n ∈ Finset.Ico k0 N, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)))
          = (1 / ((k0 : ℝ) - 1)) - (1 / ((N : ℝ) - 1)) := by
      intro N hN
      induction hN with
      | refl =>
          simp
      | @step N hN ih =>
          rw [Finset.sum_Ico_succ_top hN, ih]
          norm_num
    have hIcc :
        ∑ k ∈ Finset.Icc k0 K, (1 : ℝ) / (k : ℝ) ^ 2
          = ∑ k ∈ Finset.Ico k0 (K + 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
      have hsets : Finset.Icc k0 K = Finset.Ico k0 (K + 1) := by
        ext k
        simp
      rw [hsets]
    rw [hIcc]
    exact le_trans (Finset.sum_le_sum fun i hi => h_sum_bound i (Finset.mem_Ico.mp hi).1) (by
      rw [h_telescope (K + 1) (Nat.le_succ_of_le hK)]
      exact sub_le_self _ <| one_div_nonneg.mpr <| sub_nonneg.mpr <| by
        exact_mod_cast (by omega : 1 ≤ K + 1))
  · have hempty : Finset.Icc k0 K = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hK (le_trans (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2))
      · intro hx
        exact False.elim (Finset.notMem_empty x hx)
    rw [hempty]
    simp [hk0]
    omega

/-- Elementary dyadic control-load bound. -/
lemma ctrl_recipLoad_le_tail (BS : BlockSystem) (hk0 : 2 ≤ BS.k0) :
    R2ConcreteData.recipLoad (ctrlEdges BS) ≤ 512 / ((BS.k0 : ℝ) - 1) := by
  let f : ℕ × ℕ → ℝ := fun pq => (1 : ℝ) / ((pq.1 : ℝ) * pq.2)
  have hsum_ctrl :
      R2ConcreteData.recipLoad (ctrlEdges BS) = ∑ pq ∈ ctrlPairs BS, f pq := by
    unfold R2ConcreteData.recipLoad ctrlEdges f
    rw [Finset.sum_image (fun a ha b hb hab => ctrlPairs_prod_injOn BS ha hb hab)]
    simp only [Nat.cast_mul]
  have hpair :
      ∑ pq ∈ ctrlPairs BS, f pq
        ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (4 / (k : ℝ)) ^ 2
          + ∑ k ∈ Finset.Ico BS.k0 BS.K, (4 / (k : ℝ)) * (4 / ((k + 1 : ℕ) : ℝ)) := by
    have hint : ∀ k ∈ Finset.Icc BS.k0 BS.K,
        ∑ pq ∈ internalPairs BS k, f pq ≤ (4 / (k : ℝ)) ^ 2 := by
      intro k hk
      have hk1 : 1 ≤ k := le_trans (le_trans (by omega : 1 ≤ BS.k0) (Finset.mem_Icc.mp hk).1) le_rfl
      have hsum_nonneg : 0 ≤ ∑ p ∈ BS.P k, (1 : ℝ) / (p : ℝ) :=
        Finset.sum_nonneg fun _ _ => by positivity
      have hblock := block_recip_sum_le_four_div BS k hk1
      have hfour_nonneg : 0 ≤ 4 / (k : ℝ) := by positivity
      exact le_trans (internalPairs_recip_sum_le_sq BS k)
        (sq_le_sq' (by nlinarith) hblock)
    have hbip : ∀ k ∈ Finset.Ico BS.k0 BS.K,
        ∑ pq ∈ bipartitePairs BS k, f pq
          ≤ (4 / (k : ℝ)) * (4 / ((k + 1 : ℕ) : ℝ)) := by
      intro k hk
      have hk1 : 1 ≤ k := by
        exact le_trans (by omega : 1 ≤ BS.k0) (Finset.mem_Ico.mp hk).1
      have hk1' : 1 ≤ k + 1 := by omega
      rw [bipartitePairs_recip_sum_eq_mul]
      have h1 := block_recip_sum_le_four_div BS (k + 1) hk1'
      have h2 := block_recip_sum_le_four_div BS k hk1
      have hmul := mul_le_mul h1 h2 (by positivity) (by positivity)
      nlinarith
    refine le_trans ?_ (add_le_add (Finset.sum_le_sum hint) (Finset.sum_le_sum hbip))
    rw [ctrlPairs, ← Finset.sum_biUnion, ← Finset.sum_biUnion]
    · rw [← Finset.sum_union_inter]
      exact le_add_of_le_of_nonneg
        (Finset.sum_le_sum_of_subset_of_nonneg (by aesop_cat) fun _ _ _ => by positivity)
        (Finset.sum_nonneg fun _ _ => by positivity)
    · intros k hk l hl hkl
      simp_all +decide [Finset.disjoint_left, bipartitePairs]
      intro a b ha hb ha' hb'
      have := blocks_disjoint BS (show k ≠ l by tauto)
      simp_all +decide [Finset.disjoint_left]
    · intros k hk l hl hkl
      simp_all +decide [Finset.disjoint_left, internalPairs]
      exact fun a b ha hb hab ha' hb' => hkl <| by
        have := blocks_disjoint BS (show k ≠ l from hkl)
        exact False.elim <| Finset.disjoint_left.mp this ha ha'
  rw [hsum_ctrl]
  refine le_trans hpair ?_
  have hIco_sub : Finset.Ico BS.k0 BS.K ⊆ Finset.Icc BS.k0 BS.K := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩
  have hterm_Icc : ∀ k ∈ Finset.Icc BS.k0 BS.K,
      (4 / (k : ℝ)) ^ 2 ≤ 16 * ((1 : ℝ) / (k : ℝ) ^ 2) := by
    intro k hk
    ring_nf
    exact le_rfl
  have hterm_Ico : ∀ k ∈ Finset.Ico BS.k0 BS.K,
      (4 / (k : ℝ)) * (4 / ((k + 1 : ℕ) : ℝ)) ≤
        16 * ((1 : ℝ) / (k : ℝ) ^ 2) := by
    intro k hk
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < BS.k0) (Finset.mem_Ico.mp hk).1
    have hsucc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    have hinv : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 / (k : ℝ) :=
      one_div_le_one_div_of_le hkpos hsucc
    have hnonneg : 0 ≤ (1 : ℝ) / (k : ℝ) := one_div_nonneg.mpr hkpos.le
    have hmul := mul_le_mul_of_nonneg_left hinv hnonneg
    ring_nf at hmul ⊢
    nlinarith
  calc
    ∑ k ∈ Finset.Icc BS.k0 BS.K, (4 / (k : ℝ)) ^ 2
          + ∑ k ∈ Finset.Ico BS.k0 BS.K, (4 / (k : ℝ)) * (4 / ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, 16 * ((1 : ℝ) / (k : ℝ) ^ 2)
          + ∑ k ∈ Finset.Ico BS.k0 BS.K, 16 * ((1 : ℝ) / (k : ℝ) ^ 2) :=
        add_le_add (Finset.sum_le_sum hterm_Icc) (Finset.sum_le_sum hterm_Ico)
    _ ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, 16 * ((1 : ℝ) / (k : ℝ) ^ 2)
          + ∑ k ∈ Finset.Icc BS.k0 BS.K, 16 * ((1 : ℝ) / (k : ℝ) ^ 2) := by
        have hsecond :
            ∑ k ∈ Finset.Ico BS.k0 BS.K, 16 * ((1 : ℝ) / (k : ℝ) ^ 2)
              ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, 16 * ((1 : ℝ) / (k : ℝ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hIco_sub (fun _ _ _ => by positivity)
        exact add_le_add_right hsecond _
    _ = 32 * ∑ k ∈ Finset.Icc BS.k0 BS.K, ((1 : ℝ) / (k : ℝ) ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ 512 / ((BS.k0 : ℝ) - 1) := by
        have htail := inv_sq_sum_Icc_le BS.k0 BS.K hk0
        have hden_nonneg : 0 ≤ (BS.k0 : ℝ) - 1 := by
          have hcast : (1 : ℝ) ≤ BS.k0 := by exact_mod_cast (by omega : 1 ≤ BS.k0)
          linarith
        have hpos : 0 ≤ (1 : ℝ) / ((BS.k0 : ℝ) - 1) :=
          one_div_nonneg.mpr hden_nonneg
        calc
          32 * ∑ k ∈ Finset.Icc BS.k0 BS.K, (1 : ℝ) / (k : ℝ) ^ 2
              ≤ 32 * (1 / ((BS.k0 : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left htail (by norm_num)
          _ ≤ 512 / ((BS.k0 : ℝ) - 1) := by
            show 32 * (1 / ((BS.k0 : ℝ) - 1)) ≤ 512 / ((BS.k0 : ℝ) - 1)
            simpa [div_eq_mul_inv, one_mul] using
              mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 512) hpos

/-- Analytic socket: the dyadic reciprocal estimate needed to make the control
load eventually small.  Existing dyadic inputs are lower bounds and do not imply
this upper bound. -/
theorem dyadic_control_recipLoad_eventually_small :
  ∀ ε : ℝ, 0 < ε →
    ∃ k0min : ℕ, ∀ BS : BlockSystem, k0min ≤ BS.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS) ≤ ε :=
by
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 ≤ N ∧ 512 / ((N : ℝ) - 1) ≤ ε := by
    obtain ⟨N0, hN0⟩ := exists_nat_gt (512 / ε + 2)
    let N := max 3 N0
    refine ⟨N, by omega, ?_⟩
    have hbig : 512 / ε < (N : ℝ) - 1 := by
      have hle : (N0 : ℝ) ≤ N := by exact_mod_cast Nat.le_max_right 3 N0
      nlinarith
    have hmul : 512 < ε * ((N : ℝ) - 1) := by
      rw [div_lt_iff₀ hε] at hbig
      linarith
    have hden : 0 < (N : ℝ) - 1 := by nlinarith [hε, hmul]
    exact le_of_lt (by
      rw [div_lt_iff₀ hden]
      exact hmul)
  refine ⟨N, fun BS hBS => ?_⟩
  exact le_trans (ctrl_recipLoad_le_tail BS (le_trans hN.1 hBS)) (by
    have hden : (N : ℝ) - 1 ≤ (BS.k0 : ℝ) - 1 := by
      have hcast : (N : ℝ) ≤ BS.k0 := by exact_mod_cast hBS
      linarith
    have hposN : 0 < (N : ℝ) - 1 := by
      have hcast : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      linarith
    have hposBS : 0 < (BS.k0 : ℝ) - 1 := by
      have hcast : (1 : ℝ) < BS.k0 := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < N) hBS)
      linarith
    have hmono : 512 / ((BS.k0 : ℝ) - 1) ≤ 512 / ((N : ℝ) - 1) := by
      exact div_le_div_of_nonneg_left (by norm_num) hposN hden
    exact le_trans hmono hN.2)

/-- Construction-facing wrapper for the dyadic control-load input. -/
theorem exists_k0_controlLoad_lt
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k0min : ℕ, ∀ BS : BlockSystem, k0min ≤ BS.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS) ≤ ε :=
  dyadic_control_recipLoad_eventually_small ε hε

end CircleMethod
