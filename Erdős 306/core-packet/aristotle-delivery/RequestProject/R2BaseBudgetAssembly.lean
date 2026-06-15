import RequestProject.R2BaseLoadUpper

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 base-budget assembly

This leaf combines the named control-load input with finite gadget
scale/cardinality bounds to build `R2BaseLoadBudget`.
-/

lemma gadgetEdges_ge_mul_for_base_budget
    {R S : Finset ℕ} {r0 s0 e : ℕ}
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s)
    (he : e ∈ gadgetEdges R S) :
    r0 * s0 ≤ e := by
  rw [mem_gadgetEdges] at he
  obtain ⟨r, hr, s, hs, rfl⟩ := he
  exact Nat.mul_le_mul (hRlow r hr) (hSlow s hs)

lemma gadgetEdges_card_le_product_for_base_budget (R S : Finset ℕ) :
    (gadgetEdges R S).card ≤ R.card * S.card := by
  rw [gadgetEdges]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]

lemma gadget_recip_le_of_lower_bounds
    {R S : Finset ℕ} {r0 s0 e : ℕ}
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s)
    (he : e ∈ gadgetEdges R S) :
    (1 : ℝ) / (e : ℝ) ≤ 1 / ((r0 * s0 : ℕ) : ℝ) := by
  have hle : ((r0 * s0 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast gadgetEdges_ge_mul_for_base_budget hRlow hSlow he
  have hpos : (0 : ℝ) < ((r0 * s0 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hr0 hs0
  exact one_div_le_one_div_of_le hpos hle

theorem gadget_recipLoad_le_card_div
    {R S : Finset ℕ} (r0 s0 : ℕ)
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s) :
    R2ConcreteData.recipLoad (gadgetEdges R S)
      ≤ ((R.card * S.card : ℕ) : ℝ) / ((r0 * s0 : ℕ) : ℝ) := by
  have hpos : (0 : ℝ) < ((r0 * s0 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hr0 hs0
  have hcard :
      ((gadgetEdges R S).card : ℝ) ≤ ((R.card * S.card : ℕ) : ℝ) := by
    exact_mod_cast gadgetEdges_card_le_product_for_base_budget R S
  calc
    R2ConcreteData.recipLoad (gadgetEdges R S)
        ≤ ∑ _e ∈ gadgetEdges R S, (1 : ℝ) / ((r0 * s0 : ℕ) : ℝ) := by
          refine Finset.sum_le_sum (fun e he => ?_)
          exact gadget_recip_le_of_lower_bounds hr0 hs0 hRlow hSlow he
    _ = ((gadgetEdges R S).card : ℝ) * (1 / ((r0 * s0 : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((R.card * S.card : ℕ) : ℝ) * (1 / ((r0 * s0 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hcard (le_of_lt (one_div_pos.mpr hpos))
    _ = ((R.card * S.card : ℕ) : ℝ) / ((r0 * s0 : ℕ) : ℝ) := by
          ring

def r2BaseLoadBudget_of_component_bounds
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (Cctrl Cgadget : ℝ)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl)
    (hgadget : R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget)
    (hsum : Cctrl + Cgadget < 3 / (2 * (b : ℝ))) :
    R2BaseLoadBudget D where
  Cctrl := Cctrl
  Cgadget := Cgadget
  hctrl := hctrl
  hgadget := hgadget
  hsum := hsum

def baseLoadBudget_of_control_and_gadget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (Cctrl Cgadget : ℝ)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl)
    (hgadget : R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget)
    (hsum : Cctrl + Cgadget < 3 / (2 * (b : ℝ))) :
    R2BaseLoadBudget D :=
  r2BaseLoadBudget_of_component_bounds D Cctrl Cgadget hctrl hgadget hsum

theorem exists_k0_baseLoadBudget_of_gadget_bound
    {T : Finset ℕ} {b : ℕ}
    (D0 : R2ConcreteData T b)
    (r0 s0 : ℕ)
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (Cgadget : ℝ)
    (hgap : Cgadget < 3 / (2 * (b : ℝ)))
    (hgadget_bound : ∀ D : R2ConcreteData T b,
      D.R = D0.R → D.S = D0.S →
      R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget) :
    ∃ k0min : ℕ, ∀ D : R2ConcreteData T b, k0min ≤ D.BS.k0 →
      D.R = D0.R → D.S = D0.S →
      Nonempty (R2BaseLoadBudget D) := by
  let target : ℝ := 3 / (2 * (b : ℝ))
  let ε : ℝ := (target - Cgadget) / 2
  have hε : 0 < ε := by
    dsimp [ε, target]
    nlinarith
  obtain ⟨k0min, hctrl⟩ := exists_k0_controlLoad_lt ε hε
  refine ⟨k0min, ?_⟩
  intro D hk0 hR hS
  refine ⟨r2BaseLoadBudget_of_component_bounds D ε Cgadget (hctrl D.BS hk0)
    (hgadget_bound D hR hS) ?_⟩
  · dsimp [ε, target]
    nlinarith

def baseLoadBudget_of_control_epsilon_and_gadget_scale
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (ε : ℝ) (r0 s0 : ℕ)
    (hr0 : 0 < r0) (hs0 : 0 < s0)
    (hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ ε)
    (hRlow : ∀ r ∈ D.R, r0 ≤ r)
    (hSlow : ∀ s ∈ D.S, s0 ≤ s)
    (hsum :
      ε + ((D.R.card * D.S.card : ℕ) : ℝ) / ((r0 * s0 : ℕ) : ℝ)
        < 3 / (2 * (b : ℝ))) :
    R2BaseLoadBudget D :=
  r2BaseLoadBudget_of_component_bounds D ε
    (((D.R.card * D.S.card : ℕ) : ℝ) / ((r0 * s0 : ℕ) : ℝ))
    hctrl
    (gadget_recipLoad_le_card_div r0 s0 hr0 hs0 hRlow hSlow)
    hsum

end CircleMethod

end
