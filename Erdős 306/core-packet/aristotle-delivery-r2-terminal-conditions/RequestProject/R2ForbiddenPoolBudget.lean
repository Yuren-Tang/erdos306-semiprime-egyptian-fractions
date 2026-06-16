import RequestProject.R2PairPoolFullLower

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 forbidden-pool budget bookkeeping

This leaf decomposes the reciprocal load of the forbidden part of the residual
pair pool into obstruction, control, and gadget pieces.
-/

/-- Reciprocal load of a union is at most the sum of reciprocal loads. -/
lemma recipLoad_union_le (A B : Finset ℕ) :
    R2ConcreteData.recipLoad (A ∪ B)
      ≤ R2ConcreteData.recipLoad A + R2ConcreteData.recipLoad B := by
  have hdisj : Disjoint A (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBA
    exact (Finset.mem_sdiff.mp hxBA).2 hxA
  have hunion : A ∪ (B \ A) = A ∪ B := by
    ext x
    by_cases hxA : x ∈ A
    · simp [hxA]
    · by_cases hxB : x ∈ B <;> simp [hxA, hxB]
  calc
    R2ConcreteData.recipLoad (A ∪ B) =
        R2ConcreteData.recipLoad (A ∪ (B \ A)) := by rw [hunion]
    _ = R2ConcreteData.recipLoad A + R2ConcreteData.recipLoad (B \ A) := by
        unfold R2ConcreteData.recipLoad
        rw [Finset.sum_union hdisj]
    _ ≤ R2ConcreteData.recipLoad A + R2ConcreteData.recipLoad B := by
        exact add_le_add_right (recipLoad_mono (Finset.sdiff_subset)) _

/-- Intersection with a union has reciprocal load bounded by the two
intersection loads. -/
lemma recipLoad_inter_union_le (A B C : Finset ℕ) :
    R2ConcreteData.recipLoad (A ∩ (B ∪ C))
      ≤ R2ConcreteData.recipLoad (A ∩ B)
        + R2ConcreteData.recipLoad (A ∩ C) := by
  have hsub : A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C) := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_union] at hx
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
    exact hx.2.elim (fun hxB => Or.inl ⟨hx.1, hxB⟩)
      (fun hxC => Or.inr ⟨hx.1, hxC⟩)
  exact le_trans (recipLoad_mono hsub) (recipLoad_union_le (A ∩ B) (A ∩ C))

/-- Decompose the forbidden residual pair-pool load into obstruction, control,
and gadget pieces. -/
theorem residualForbidden_recipLoad_le_components
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) :
    R2ConcreteData.recipLoad
        (blockSupportPairPool D.BS ∩ residualForbidden D)
      ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS ∩ T)
        + R2ConcreteData.recipLoad
            (blockSupportPairPool D.BS ∩ ctrlEdges D.BS)
        + R2ConcreteData.recipLoad
            (blockSupportPairPool D.BS ∩ gadgetEdges D.R D.S) := by
  let A := blockSupportPairPool D.BS
  let C := ctrlEdges D.BS
  let G := gadgetEdges D.R D.S
  have h1 : R2ConcreteData.recipLoad (A ∩ (T ∪ (C ∪ G)))
      ≤ R2ConcreteData.recipLoad (A ∩ T) +
        R2ConcreteData.recipLoad (A ∩ (C ∪ G)) :=
    recipLoad_inter_union_le A T (C ∪ G)
  have h2 : R2ConcreteData.recipLoad (A ∩ (C ∪ G))
      ≤ R2ConcreteData.recipLoad (A ∩ C) +
        R2ConcreteData.recipLoad (A ∩ G) :=
    recipLoad_inter_union_le A C G
  dsimp [A, C, G] at h1 h2 ⊢
  rw [residualForbidden]
  linarith

/-- Separate numeric budgets for the three forbidden pieces. -/
structure R2ForbiddenBudget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) where
  FT : ℝ
  Fctrl : ℝ
  Fgadget : ℝ
  hT :
    R2ConcreteData.recipLoad (blockSupportPairPool D.BS ∩ T) ≤ FT
  hctrl :
    R2ConcreteData.recipLoad
      (blockSupportPairPool D.BS ∩ ctrlEdges D.BS) ≤ Fctrl
  hgadget :
    R2ConcreteData.recipLoad
      (blockSupportPairPool D.BS ∩ gadgetEdges D.R D.S) ≤ Fgadget

/-- The three-piece forbidden budget bounds the full forbidden load. -/
theorem residualForbidden_recipLoad_le_budget
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b}
    (B : R2ForbiddenBudget D) :
    R2ConcreteData.recipLoad
        (blockSupportPairPool D.BS ∩ residualForbidden D)
      ≤ B.FT + B.Fctrl + B.Fgadget := by
  have hparts := residualForbidden_recipLoad_le_components D
  linarith [B.hT, B.hctrl, B.hgadget]

end CircleMethod

end
