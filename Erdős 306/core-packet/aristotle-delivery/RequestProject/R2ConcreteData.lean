import RequestProject.R2AssemblySkeleton
import RequestProject.BlockMassPool
import RequestProject.ArcConstructionSigma
import RequestProject.CircleMethodAssembly

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 concrete construction data

This leaf exposes the concrete edge/period data used by the final R2
`ArcConstruction` assembly.  It deliberately proves only structural fields:
semiprimality, avoidance, period divisibility, positivity, non-emptiness, and the
light-extra `σ_E ≤ σ_ctrl` wrapper.  The final parameter choices and minor-arc
estimate remain outside this file.
-/

/-- The concrete R2 edge data before the final analytic and CRT choices. -/
structure R2ConcreteData (T : Finset ℕ) (b : ℕ) where
  BS : BlockSystem
  Q : Finset ℕ
  R : Finset ℕ
  S : Finset ℕ

namespace R2ConcreteData

variable {T : Finset ℕ} {b : ℕ}

/-- The concrete R2 edge set: control edges, mass-batch edges, and gadget edges. -/
def E (D : R2ConcreteData T b) : Finset ℕ :=
  r2Edges D.BS D.Q D.R D.S

/-- The block-support period used by the R2 construction skeleton. -/
def L (D : R2ConcreteData T b) : ℕ :=
  primeSupportPeriod b (blockSupport D.BS)

/-- Reciprocal load of an edge set. -/
def recipLoad (E : Finset ℕ) : ℝ :=
  ∑ e ∈ E, (1 : ℝ) / (e : ℝ)

/-- The already-fixed part of the R2 load, before adding the residual mass batch. -/
def baseLoad (D : R2ConcreteData T b) : ℝ :=
  recipLoad (ctrlEdges D.BS ∪ gadgetEdges D.R D.S)

lemma ctrlEdges_subset_E (D : R2ConcreteData T b) :
    ctrlEdges D.BS ⊆ D.E := by
  exact ctrlEdges_subset_r2Edges D.BS D.Q D.R D.S

lemma massBatch_subset_E (D : R2ConcreteData T b) :
    D.Q ⊆ D.E := by
  exact massBatch_subset_r2Edges D.BS D.Q D.R D.S

lemma gadgetEdges_subset_E (D : R2ConcreteData T b) :
    gadgetEdges D.R D.S ⊆ D.E := by
  exact gadgetEdges_subset_r2Edges D.BS D.Q D.R D.S

/-- Wrapper for semiprimality of the concrete R2 edge set. -/
lemma semiprime (D : R2ConcreteData T b)
    (hQsemi : ∀ e ∈ D.Q, IsSemiprime e)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s) :
    ∀ e ∈ D.E, IsSemiprime e := by
  exact r2_edges_semiprime hQsemi hRprime hSprime hlt

/-- Wrapper for avoidance of the obstruction set. -/
lemma avoid (D : R2ConcreteData T b)
    (hctrl : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hQ : ∀ e ∈ D.Q, e ∉ T)
    (hgadget : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T) :
    ∀ e ∈ D.E, e ∉ T := by
  exact r2_edges_avoid hctrl hQ hgadget

/-- Wrapper for period divisibility of every concrete R2 edge. -/
lemma dvd_period (D : R2ConcreteData T b)
    (hQdvd : ∀ e ∈ D.Q, e ∣ D.L)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS) :
    ∀ e ∈ D.E, e ∣ D.L := by
  intro e he
  exact r2_edges_dvd_period (b := b) (Q := D.Q) (R := D.R) (S := D.S)
    (BS := D.BS) (by simpa [E] using he)
    (hQdvd := by simpa [L] using hQdvd) (hRdvd := hRdvd) (hSblock := hSblock)

/-- The base denominator divides the concrete R2 period. -/
lemma base_dvd_period (D : R2ConcreteData T b) :
    b ∣ D.L := by
  refine ⟨∏ p ∈ blockSupport D.BS, p, ?_⟩
  rfl

/-- The concrete period is positive once the base denominator is positive. -/
lemma period_pos (D : R2ConcreteData T b) (hb : 0 < b) :
    0 < D.L := by
  unfold L primeSupportPeriod
  exact Nat.mul_pos hb (Finset.prod_pos fun p hp => (blockSupport_prime D.BS hp).pos)

/-- Positivity of all concrete R2 edges, as consumed by the circle-method core. -/
lemma edges_pos (D : R2ConcreteData T b)
    (hsemi : ∀ e ∈ D.E, IsSemiprime e) :
    ∀ e ∈ D.E, 0 < e := by
  intro e he
  exact (hsemi e he).pos

/-- Non-emptiness inherited from a non-empty mass batch. -/
lemma nonempty_of_massBatch_nonempty (D : R2ConcreteData T b)
    (hQne : D.Q.Nonempty) :
    D.E.Nonempty := by
  obtain ⟨e, he⟩ := hQne
  exact ⟨e, D.massBatch_subset_E he⟩

/-- Non-emptiness inherited from a non-empty control-edge set. -/
lemma nonempty_of_ctrlEdges_nonempty (D : R2ConcreteData T b)
    (hctrlne : (ctrlEdges D.BS).Nonempty) :
    D.E.Nonempty := by
  obtain ⟨e, he⟩ := hctrlne
  exact ⟨e, D.ctrlEdges_subset_E he⟩

/-- The light-extra wrapper used to feed `hbeat`: for the concrete edge set,
`σ_E ≤ σ_ctrl` follows from the explicit extra inverse-square hypothesis. -/
lemma sigma_le_sigmaCtrl_of_light (D : R2ConcreteData T b) (theta : ℕ → ℝ)
    (hextra : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2) :
    Real.sqrt (sigmaE2 D.E theta) ≤ sigmaCtrl D.BS := by
  exact sigmaE_le_sigmaCtrl_of_extra_light D.BS D.E theta D.ctrlEdges_subset_E hextra

/-- If the residual batch is disjoint from the fixed base edges, the concrete R2
load splits as `baseLoad + recipLoad Q`. -/
lemma recipLoad_E_eq_baseLoad_add_Q (D : R2ConcreteData T b)
    (hdisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S)) :
    recipLoad D.E = D.baseLoad + recipLoad D.Q := by
  unfold recipLoad baseLoad E r2Edges
  have hset :
      ctrlEdges D.BS ∪ D.Q ∪ gadgetEdges D.R D.S =
        D.Q ∪ (ctrlEdges D.BS ∪ gadgetEdges D.R D.S) := by
    ext e
    simp only [Finset.mem_union]
    tauto
  rw [hset, Finset.sum_union hdisj]
  rw [recipLoad]
  ring

/-- Residual reciprocal-window extraction after a fixed nonnegative base load.

This is the mass-correction wrapper: the mass batch is chosen to fill the
remaining gap below `3/(2b)`, rather than using the standalone block-aligned
batch as the final load. -/
lemma exists_residual_subset_recip_window
    (P : Finset ℕ) (base : ℝ) (b : ℕ)
    (hb : 0 < b)
    (hbase : base < 3 / (2 * (b : ℝ)))
    (hsmall : ∀ e ∈ P, (1 : ℝ) / (e : ℝ) < 3 / (2 * (b : ℝ)))
    (hsum : 3 / (2 * (b : ℝ)) - base ≤ recipLoad P) :
    ∃ Q : Finset ℕ,
      Q ⊆ P ∧
      3 / (2 * (b : ℝ)) ≤ base + recipLoad Q ∧
      base + recipLoad Q < 3 / (b : ℝ) := by
  have hgap_pos : 0 < 3 / (2 * (b : ℝ)) := by
    positivity
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hgap_eq : 3 / (2 * (b : ℝ)) = 3 / (b : ℝ) - 3 / (2 * (b : ℝ)) := by
    field_simp [hbR]
    ring
  obtain ⟨Q, hQsub, hQlb, hQub⟩ :=
    exists_subset_recip_residual_window P base (3 / (2 * (b : ℝ))) (3 / (b : ℝ))
      (3 / (2 * (b : ℝ))) (le_of_lt hbase) hgap_eq hgap_pos hsmall
      (by simpa [recipLoad] using hsum)
  exact ⟨Q, hQsub, hQlb, by simpa [recipLoad] using hQub⟩

/-- Convert residual base-plus-batch load bounds into the concrete edge-load
window for `D.E`. -/
lemma total_recipLoad_window_of_residual (D : R2ConcreteData T b)
    (hdisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))
    (hlb : 3 / (2 * (b : ℝ)) ≤ D.baseLoad + recipLoad D.Q)
    (hub : D.baseLoad + recipLoad D.Q < 3 / (b : ℝ)) :
    3 / (2 * (b : ℝ)) ≤ recipLoad D.E ∧
      recipLoad D.E < 3 / (b : ℝ) := by
  rw [D.recipLoad_E_eq_baseLoad_add_Q hdisj]
  exact ⟨hlb, hub⟩

/-- Abstract weight package for the final `ArcConstruction` assembly.  This names
exactly the common-window and mass hypotheses without forcing the final mass-tuning
choices into this structural file. -/
structure Weights (D : R2ConcreteData T b) where
  theta : ℕ → ℝ
  hlb : ∀ e ∈ D.E, 1 / 3 ≤ theta e
  hub : ∀ e ∈ D.E, theta e ≤ 2 / 3
  hmass : (∑ e ∈ D.E, theta e / (e : ℝ)) = 1 / (b : ℝ)

end R2ConcreteData

/-- Compatibility alias with the task-file naming. -/
abbrev R2ConcreteWeights {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) :=
  R2ConcreteData.Weights D

lemma r2Concrete_semiprime {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hQsemi : ∀ e ∈ D.Q, IsSemiprime e)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s) :
    ∀ e ∈ D.E, IsSemiprime e :=
  D.semiprime hQsemi hRprime hSprime hlt

lemma r2Concrete_avoid {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hctrl : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hQ : ∀ e ∈ D.Q, e ∉ T)
    (hgadget : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T) :
    ∀ e ∈ D.E, e ∉ T :=
  D.avoid hctrl hQ hgadget

lemma r2Concrete_dvd_period {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hQdvd : ∀ e ∈ D.Q, e ∣ D.L)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS) :
    ∀ e ∈ D.E, e ∣ D.L :=
  D.dvd_period hQdvd hRdvd hSblock

lemma r2Concrete_edges_pos {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hsemi : ∀ e ∈ D.E, IsSemiprime e) :
    ∀ e ∈ D.E, 0 < e :=
  D.edges_pos hsemi

lemma r2Concrete_nonempty {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hQne : D.Q.Nonempty) :
    D.E.Nonempty :=
  D.nonempty_of_massBatch_nonempty hQne

lemma r2Concrete_sigma_le_sigmaCtrl_of_light {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (theta : ℕ → ℝ)
    (hextra : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2) :
    Real.sqrt (sigmaE2 D.E theta) ≤ sigmaCtrl D.BS :=
  D.sigma_le_sigmaCtrl_of_light theta hextra

lemma r2Concrete_exists_residual_subset_recip_window
    (P : Finset ℕ) (base : ℝ) (b : ℕ)
    (hb : 0 < b)
    (hbase : base < 3 / (2 * (b : ℝ)))
    (hsmall : ∀ e ∈ P, (1 : ℝ) / (e : ℝ) < 3 / (2 * (b : ℝ)))
    (hsum : 3 / (2 * (b : ℝ)) - base ≤ R2ConcreteData.recipLoad P) :
    ∃ Q : Finset ℕ,
      Q ⊆ P ∧
      3 / (2 * (b : ℝ)) ≤ base + R2ConcreteData.recipLoad Q ∧
      base + R2ConcreteData.recipLoad Q < 3 / (b : ℝ) :=
  R2ConcreteData.exists_residual_subset_recip_window P base b hb hbase hsmall hsum

lemma r2Concrete_total_recipLoad_window_of_residual {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hdisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))
    (hlb : 3 / (2 * (b : ℝ)) ≤ D.baseLoad + R2ConcreteData.recipLoad D.Q)
    (hub : D.baseLoad + R2ConcreteData.recipLoad D.Q < 3 / (b : ℝ)) :
    3 / (2 * (b : ℝ)) ≤ R2ConcreteData.recipLoad D.E ∧
      R2ConcreteData.recipLoad D.E < 3 / (b : ℝ) :=
  D.total_recipLoad_window_of_residual hdisj hlb hub

end CircleMethod

end
