import RequestProject.R2DyadicBlockSupport

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 forbidden budget from base-load absorption

This leaf proves the key arithmetic simplification for the residual mass batch:
if the old obstruction set `T` lies below the bottom pair scale, and the control
and gadget components are disjoint, then the forbidden budget is absorbed by the
already-spent base load.  The remaining inequality is just `3/(2b) ≤ 1/2`, i.e.
`b ≥ 3`.
-/

/-- If every obstruction is below the bottom pair scale, then no obstruction can
belong to the block-support pair pool. -/
lemma blockSupportPairPool_inter_T_eq_empty_of_lt_k0_square
    {T : Finset ℕ} {BS : BlockSystem}
    (hTsmall : ∀ e ∈ T, e < 2 ^ BS.k0 * 2 ^ BS.k0) :
    blockSupportPairPool BS ∩ T = ∅ := by
  ext e
  constructor
  · intro he
    rw [Finset.mem_inter] at he
    have hge : 2 ^ BS.k0 * 2 ^ BS.k0 ≤ e := by
      obtain ⟨p, q, hp, hq, _hpq, rfl⟩ := blockSupportPairPool_pair he.1
      exact Nat.mul_le_mul (blockSupport_ge_k0 hp) (blockSupport_ge_k0 hq)
    exact False.elim (not_le_of_gt (hTsmall e he.2) hge)
  · intro he
    simp at he

/-- The fixed base load splits over disjoint control and gadget components. -/
lemma baseLoad_eq_ctrl_add_gadget_of_disjoint
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hdisj : Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S)) :
    D.baseLoad =
      R2ConcreteData.recipLoad (ctrlEdges D.BS) +
        R2ConcreteData.recipLoad (gadgetEdges D.R D.S) := by
  unfold R2ConcreteData.baseLoad R2ConcreteData.recipLoad
  rw [Finset.sum_union hdisj]

/-- Concrete forbidden budget using zero obstruction overlap and the full
control/gadget reciprocal loads as component budgets. -/
def R2ForbiddenBudget.of_basePieces
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hTsmall : ∀ e ∈ T, e < 2 ^ D.BS.k0 * 2 ^ D.BS.k0) :
    R2ForbiddenBudget D where
  FT := 0
  Fctrl := R2ConcreteData.recipLoad (ctrlEdges D.BS)
  Fgadget := R2ConcreteData.recipLoad (gadgetEdges D.R D.S)
  hT := by
    rw [blockSupportPairPool_inter_T_eq_empty_of_lt_k0_square hTsmall]
    simp [R2ConcreteData.recipLoad]
  hctrl := by
    exact recipLoad_mono (Finset.inter_subset_right)
  hgadget := by
    exact recipLoad_mono (Finset.inter_subset_right)

/-- For `b ≥ 3`, the common R2 target obeys `3/(2b) ≤ 1/2`. -/
lemma three_div_two_mul_le_half_of_three_le {b : ℕ} (hb : 3 ≤ b) :
    3 / (2 * (b : ℝ)) ≤ (1 : ℝ) / 2 := by
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbne : (b : ℝ) ≠ 0 := by positivity
  field_simp [hbne]
  nlinarith

/-- With zero obstruction overlap and disjoint fixed components, the final
forbidden-budget inequality follows from `b ≥ 3`. -/
theorem basePieces_forbiddenBudget_final_ineq
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hb : 3 ≤ b)
    (hTsmall : ∀ e ∈ T, e < 2 ^ D.BS.k0 * 2 ^ D.BS.k0)
    (hdisj : Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S)) :
    let B := R2ForbiddenBudget.of_basePieces D hTsmall
    (3 / (2 * (b : ℝ)) - D.baseLoad) + (B.FT + B.Fctrl + B.Fgadget)
      ≤ (1 : ℝ) / 2 := by
  intro B
  have hbase := baseLoad_eq_ctrl_add_gadget_of_disjoint D hdisj
  have htarget := three_div_two_mul_le_half_of_three_le hb
  dsimp [B, R2ForbiddenBudget.of_basePieces]
  rw [hbase]
  linarith

/-- Mass-batch existence with the forbidden budget discharged by base-load
absorption. -/
theorem exists_massBatchSupply_of_basePieces_forbiddenBudget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 3 ≤ b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0))
    (hTsmall : ∀ e ∈ T, e < 2 ^ D.BS.k0 * 2 ^ D.BS.k0)
    (hdisj : Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S))
    (hsub : blockPrimes D.BS.k0 ⊆ blockSupport D.BS) :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ (k1 ≤ D.BS.k0 →
      ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q)) := by
  let B := R2ForbiddenBudget.of_basePieces D hTsmall
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hbudget :
      (3 / (2 * (b : ℝ)) - D.baseLoad) + (B.FT + B.Fctrl + B.Fgadget)
        ≤ (1 : ℝ) / 2 := by
    simpa [B] using basePieces_forbiddenBudget_final_ineq D hb hTsmall hdisj
  exact exists_massBatchSupply_of_eventual_blockPrimes_forbiddenBudget D hbpos
    hbase hlarge B hsub hbudget

end CircleMethod

end
