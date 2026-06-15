import RequestProject.R2MassBatchPoolSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 residual mass-batch candidate pool

This file names the canonical candidate pool for the residual mass batch:
products `p*q` of two ordered distinct primes in the block support, after
removing the obstruction set and the already-fixed control/gadget edges.

The endpoint reduces construction of `R2MassBatchSupply` to two numerical pool
facts: individual smallness and enough remaining reciprocal mass.
-/

/-- All ordered block-support prime products `p*q` with `p < q`. -/
def blockSupportPairPool (BS : BlockSystem) : Finset ℕ :=
  ((blockSupport BS).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2)).image
    (fun pq : ℕ × ℕ => pq.1 * pq.2)

/-- The residual mass-batch pool after deleting the obstruction set and the
already-fixed control/gadget edge products. -/
def residualPairPool {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) :
    Finset ℕ :=
  blockSupportPairPool D.BS \ (T ∪ (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))

lemma blockSupportPairPool_pair {BS : BlockSystem} {e : ℕ}
    (he : e ∈ blockSupportPairPool BS) :
    ∃ p q, p ∈ blockSupport BS ∧ q ∈ blockSupport BS ∧ p < q ∧ e = p * q := by
  rw [blockSupportPairPool, Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  rw [Finset.mem_filter, Finset.mem_offDiag] at hpq
  exact ⟨pq.1, pq.2, hpq.1.1, hpq.1.2.1, hpq.2, rfl⟩

lemma residualPairPool_pair {T : Finset ℕ} {b e : ℕ}
    (D : R2ConcreteData T b) (he : e ∈ residualPairPool D) :
    ∃ p q, p ∈ blockSupport D.BS ∧ q ∈ blockSupport D.BS ∧ p < q ∧ e = p * q := by
  rw [residualPairPool, Finset.mem_sdiff] at he
  exact blockSupportPairPool_pair he.1

lemma residualPairPool_avoid {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) :
    ∀ e ∈ residualPairPool D, e ∉ T := by
  intro e he hT
  rw [residualPairPool, Finset.mem_sdiff] at he
  exact he.2 (by simp [hT])

lemma residualPairPool_disjoint_fixed {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) :
    Disjoint (residualPairPool D) (ctrlEdges D.BS ∪ gadgetEdges D.R D.S) := by
  rw [Finset.disjoint_left]
  intro e he hfixed
  rw [residualPairPool, Finset.mem_sdiff] at he
  exact he.2 (by simp [hfixed])

/-- The canonical residual pair pool supplies a valid mass-batch subset once its
remaining reciprocal mass is large enough. -/
theorem exists_massBatchSupply_of_residualPairPool
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 0 < b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hsmall : ∀ e ∈ residualPairPool D,
      (1 : ℝ) / (e : ℝ) < 3 / (2 * (b : ℝ)))
    (hsum : 3 / (2 * (b : ℝ)) - D.baseLoad
      ≤ R2ConcreteData.recipLoad (residualPairPool D)) :
    ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q) := by
  exact exists_massBatchSupply_of_pool D (residualPairPool D) hb hbase
    (residualPairPool_pair D) (residualPairPool_avoid D)
    (residualPairPool_disjoint_fixed D) hsmall hsum

end CircleMethod

end
