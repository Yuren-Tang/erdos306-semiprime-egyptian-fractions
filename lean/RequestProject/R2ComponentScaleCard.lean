import RequestProject.R2MassBatchReady
import RequestProject.R2ComponentSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 component scale / cardinality supplies
-/

lemma blockSupport_ge_pow_k0 (BS : BlockSystem) {p : ℕ}
    (hp : p ∈ blockSupport BS) :
    2 ^ BS.k0 ≤ p := by
  rw [blockSupport, Finset.mem_biUnion] at hp
  obtain ⟨k, hk, hpk⟩ := hp
  rw [Finset.mem_Icc] at hk
  calc 2 ^ BS.k0 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    _ ≤ p := (BS.hwindow k p hpk).1

lemma ctrlEdges_ge_k0_square
    (BS : BlockSystem) {e : ℕ} (he : e ∈ ctrlEdges BS) :
    2 ^ BS.k0 * 2 ^ BS.k0 ≤ e := by
  rw [ctrlEdges, Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  obtain ⟨h1, h2⟩ := ctrlPairs_mem_blockSupport BS hpq
  exact Nat.mul_le_mul (blockSupport_ge_pow_k0 BS h1) (blockSupport_ge_pow_k0 BS h2)

theorem ctrlEdges_scale_of_k0_square
    (BS : BlockSystem) (N : ℤ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hscale : (N : ℝ) ≤ ρ * ((2 ^ BS.k0 * 2 ^ BS.k0 : ℕ) : ℝ)) :
    ∀ e ∈ ctrlEdges BS, (N : ℝ) ≤ ρ * (e : ℝ) := by
  intro e he
  refine le_trans hscale ?_
  have : ((2 ^ BS.k0 * 2 ^ BS.k0 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast ctrlEdges_ge_k0_square BS he
  exact mul_le_mul_of_nonneg_left this hρ

lemma gadgetEdges_ge_mul
    {R S : Finset ℕ} {r0 s0 e : ℕ}
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s)
    (he : e ∈ gadgetEdges R S) :
    r0 * s0 ≤ e := by
  rw [mem_gadgetEdges] at he
  obtain ⟨r, hr, s, hs, rfl⟩ := he
  exact Nat.mul_le_mul (hRlow r hr) (hSlow s hs)

theorem gadgetEdges_scale_of_mul
    {R S : Finset ℕ} (N : ℤ) (ρ : ℝ) (r0 s0 : ℕ)
    (hρ : 0 ≤ ρ)
    (hscale : (N : ℝ) ≤ ρ * ((r0 * s0 : ℕ) : ℝ))
    (hRlow : ∀ r ∈ R, r0 ≤ r)
    (hSlow : ∀ s ∈ S, s0 ≤ s) :
    ∀ e ∈ gadgetEdges R S, (N : ℝ) ≤ ρ * (e : ℝ) := by
  intro e he
  refine le_trans hscale ?_
  have : ((r0 * s0 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast gadgetEdges_ge_mul hRlow hSlow he
  exact mul_le_mul_of_nonneg_left this hρ

lemma ctrlEdges_card_le_ctrlPairs_card (BS : BlockSystem) :
    (ctrlEdges BS).card ≤ (ctrlPairs BS).card := by
  rw [ctrlEdges]
  exact Finset.card_image_le

lemma gadgetEdges_card_le_product (R S : Finset ℕ) :
    (gadgetEdges R S).card ≤ R.card * S.card := by
  rw [gadgetEdges]
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product]

lemma ctrlPairs_card_le_support_square (BS : BlockSystem) :
    (ctrlPairs BS).card ≤ (blockSupport BS).card * (blockSupport BS).card := by
  have hsub : ctrlPairs BS ⊆ (blockSupport BS) ×ˢ (blockSupport BS) := by
    intro pq hpq
    rw [Finset.mem_product]
    exact ctrlPairs_mem_blockSupport BS hpq
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_product]

theorem r2ControlSupply_of_k0_square
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hscale : (N : ℝ) ≤ ρ * ((2 ^ D.BS.k0 * 2 ^ D.BS.k0 : ℕ) : ℝ))
    (havoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T) :
    R2ControlSupply D N ρ :=
  { hctrledge := ctrlEdges_scale_of_k0_square D.BS N ρ hρ hscale
    hctrlAvoid := havoid }

theorem r2GadgetSupply_of_mul_scale
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ)
    (r0 s0 : ℕ)
    (hρ : 0 ≤ ρ)
    (hscale : (N : ℝ) ≤ ρ * ((r0 * s0 : ℕ) : ℝ))
    (hRlow : ∀ r ∈ D.R, r0 ≤ r)
    (hSlow : ∀ s ∈ D.S, s0 ≤ s)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS) :
    R2GadgetSupply D N ρ :=
  { hRprime := hRprime
    hSprime := hSprime
    hlt := hlt
    hgadgetedge := gadgetEdges_scale_of_mul N ρ r0 s0 hρ hscale hRlow hSlow
    hgadgetAvoid := hgadgetAvoid
    hRdvd := hRdvd
    hSblock := hSblock }

end CircleMethod

