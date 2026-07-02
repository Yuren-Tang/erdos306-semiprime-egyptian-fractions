import RequestProject.GlobalControl.Encoding.BlockData

/-! Bounding the total number of assignments in the large-energy regime. -/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-
In the trivial regime `R ≥ Rtriv` the total
    number of global assignments is already `≤ exp(εR)`.  Here
    `Rtriv = ε⁻¹·2^{K+2}·(K+1)`.  (Counts `∏ p ≤ exp(∑_k N_k(k+1)log2)`,
    `N_k ≤ 2^k`.)
-/
lemma global_assignment_card_le_exp_above_threshold (eps : ℝ) (heps : 0 < eps) (BS : BlockSystem) (R : ℝ)
    (hR : eps⁻¹ * 2 ^ (BS.K + 2) * ((BS.K : ℝ) + 1) ≤ R) :
    (Fintype.card (GlobalAssignment BS) : ℝ) ≤ Real.exp (eps * R) := by
  -- We can bound each product term $p \leq 2^{k+1}$ for $p \in P_k$ and sum over $k$.
  have h_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (BS.P k).card * Real.log (2 ^ (k + 1)) := by
    have h_log_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, ∑ p ∈ BS.P k, Real.log p := by
      have h_log : Real.log (Fintype.card (GlobalAssignment BS)) = ∑ p ∈ blockSupport BS, Real.log p := by
        have h_card : (Fintype.card (GlobalAssignment BS)) = ∏ p ∈ blockSupport BS, p := by
          unfold GlobalAssignment; simp +decide [ Fintype.card_pi ] ;
          conv_rhs => rw [ ← Finset.prod_attach ] ;
        rw [ h_card, Nat.cast_prod, Real.log_prod ] ; norm_num;
        exact fun h => by obtain ⟨ k, hk, hk' ⟩ := Finset.mem_biUnion.mp h; have := BS.hwindow k 0 hk'; norm_num at this;
      rw [ h_log, blockSupport, Finset.sum_biUnion ];
      exact fun k hk l hl hkl => blocks_disjoint BS hkl;
    refine le_trans h_log_bound <| Finset.sum_le_sum fun k hk => ?_;
    exact le_trans ( Finset.sum_le_sum fun x hx => Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| BS.hprime k x hx ) <| show ( x : ℝ ) ≤ 2 ^ ( k + 1 ) by exact_mod_cast Nat.le_of_lt <| BS.hwindow k x hx |>.2 ) <| by norm_num;
  -- We can bound each term $\log(2^{k+1}) = (k+1)\log(2)$ and use the fact that $(BS.P k).card \leq 2^k$.
  have h_bound' : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (2 ^ k : ℝ) * (k + 1) * Real.log 2 := by
    refine le_trans h_bound <| Finset.sum_le_sum fun k hk => ?_;
    norm_num [ mul_assoc ];
    gcongr;
    exact_mod_cast le_trans ( Finset.card_le_card ( show BS.P k ⊆ Finset.Ico ( 2 ^ k ) ( 2 ^ ( k + 1 ) ) from fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx ) ) ( by norm_num [ pow_succ' ] ; linarith );
  -- We can bound the sum $\sum_{k=k0}^{K} 2^k (k+1)$ by $2^{K+1} (K+1)$.
  have h_sum_bound : ∑ k ∈ Finset.Icc BS.k0 BS.K, (2 ^ k : ℝ) * (k + 1) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) := by
    have h_sum_bound : ∑ k ∈ Finset.range (BS.K + 1), (2 ^ k : ℝ) * (k + 1) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) := by
      exact Nat.recOn BS.K ( by norm_num ) fun n ihn => by norm_num [ Finset.sum_range_succ, pow_succ' ] at * ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) n ] ;
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) fun _ _ _ => by positivity ) h_sum_bound;
  -- We can bound the sum $\sum_{k=k0}^{K} 2^k (k+1)$ by $2^{K+1} (K+1)$ and use the fact that $\log(2) < 1$.
  have h_final_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) * Real.log 2 := by
    exact h_bound'.trans ( by rw [ ← Finset.sum_mul _ _ _ ] ; exact mul_le_mul_of_nonneg_right h_sum_bound <| Real.log_nonneg <| by norm_num );
  rw [ ← Real.log_le_iff_le_exp ( Nat.cast_pos.mpr <| Fintype.card_pos_iff.mpr ⟨ fun _ => 0 ⟩ ) ];
  refine le_trans h_final_bound ?_;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left hR heps.le ) ; ring_nf ; norm_num [ heps.ne' ];
  nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, show ( 0 : ℝ ) ≤ 2 ^ BS.K by positivity, show ( 0 : ℝ ) ≤ BS.K * 2 ^ BS.K by positivity ]

end GlobalControl

end
