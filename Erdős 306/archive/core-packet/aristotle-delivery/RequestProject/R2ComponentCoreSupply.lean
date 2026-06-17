import RequestProject.R2ComponentSupplyReady
import RequestProject.R2MassBatchPoolSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 component core supply

The final component record includes the selected mass-batch cardinality
`D.Q.card`.  This file separates the stable control/gadget data from the
post-selection `Q` cardinality, so the component package can be rebuilt after
the residual mass-batch selector replaces `D.Q`.
-/

/-- Component data stable under replacing only `D.Q`. -/
structure R2ComponentScaleCoreSupply
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) (N : ℤ) (ρ : ℝ) where
  hρ : 0 ≤ ρ
  hctrlScale : (N : ℝ) ≤ ρ * ((2 ^ D.BS.k0 * 2 ^ D.BS.k0 : ℕ) : ℝ)
  hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T
  r0 : ℕ
  s0 : ℕ
  hgadgetScale : (N : ℝ) ≤ ρ * ((r0 * s0 : ℕ) : ℝ)
  hRlow : ∀ r ∈ D.R, r0 ≤ r
  hSlow : ∀ s ∈ D.S, s0 ≤ s
  hRprime : ∀ r ∈ D.R, Nat.Prime r
  hSprime : ∀ s ∈ D.S, Nat.Prime s
  hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s
  hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T
  hRdvd : ∀ r ∈ D.R, r ∣ b
  hSblock : D.S ⊆ blockSupport D.BS

/-- Reinsert the selected `Q` cardinality budget to obtain the final component
scale/cardinality package. -/
def R2ComponentScaleCoreSupply.toScaleCardSupply
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b} {N : ℤ} {ρ K : ℝ}
    (S : R2ComponentScaleCoreSupply D N ρ)
    (hcomponentCard :
      ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K) :
    R2ComponentScaleCardSupply D N ρ K where
  hρ := S.hρ
  hctrlScale := S.hctrlScale
  hctrlAvoid := S.hctrlAvoid
  r0 := S.r0
  s0 := S.s0
  hgadgetScale := S.hgadgetScale
  hRlow := S.hRlow
  hSlow := S.hSlow
  hRprime := S.hRprime
  hSprime := S.hSprime
  hlt := S.hlt
  hgadgetAvoid := S.hgadgetAvoid
  hRdvd := S.hRdvd
  hSblock := S.hSblock
  hcomponentCard := hcomponentCard

/-- The core component data is unchanged when replacing only `Q`. -/
def R2ComponentScaleCoreSupply.withQ
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b} {N : ℤ} {ρ : ℝ}
    (S : R2ComponentScaleCoreSupply D N ρ) (Q : Finset ℕ) :
    R2ComponentScaleCoreSupply (D.withQ Q) N ρ where
  hρ := S.hρ
  hctrlScale := by simpa [R2ConcreteData.withQ] using S.hctrlScale
  hctrlAvoid := by simpa [R2ConcreteData.withQ] using S.hctrlAvoid
  r0 := S.r0
  s0 := S.s0
  hgadgetScale := S.hgadgetScale
  hRlow := by simpa [R2ConcreteData.withQ] using S.hRlow
  hSlow := by simpa [R2ConcreteData.withQ] using S.hSlow
  hRprime := by simpa [R2ConcreteData.withQ] using S.hRprime
  hSprime := by simpa [R2ConcreteData.withQ] using S.hSprime
  hlt := by simpa [R2ConcreteData.withQ] using S.hlt
  hgadgetAvoid := by simpa [R2ConcreteData.withQ] using S.hgadgetAvoid
  hRdvd := by simpa [R2ConcreteData.withQ] using S.hRdvd
  hSblock := by simpa [R2ConcreteData.withQ] using S.hSblock

/-- Build the final component package after a residual mass-batch `Q` has been
selected. -/
def R2ComponentScaleCoreSupply.toScaleCardSupply_withQ
    {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b} {N : ℤ} {ρ K : ℝ}
    (S : R2ComponentScaleCoreSupply D N ρ) (Q : Finset ℕ)
    (hcomponentCard :
      ((ctrlEdges D.BS).card + Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K) :
    R2ComponentScaleCardSupply (D.withQ Q) N ρ K :=
  (S.withQ Q).toScaleCardSupply (by
    simpa [R2ConcreteData.withQ] using hcomponentCard)

end CircleMethod

end
