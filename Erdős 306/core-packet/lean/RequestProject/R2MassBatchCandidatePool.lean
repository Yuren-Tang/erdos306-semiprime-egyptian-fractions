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

/-- Edges forbidden for the residual mass batch: the obstruction set plus the
already-fixed control/gadget products. -/
def residualForbidden {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) :
    Finset ℕ :=
  T ∪ (ctrlEdges D.BS ∪ gadgetEdges D.R D.S)

/-- The residual mass-batch pool after deleting the obstruction set and the
already-fixed control/gadget edge products. -/
def residualPairPool {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) :
    Finset ℕ :=
  blockSupportPairPool D.BS \ residualForbidden D

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
  exact he.2 (by simp [residualForbidden, hT])

lemma residualPairPool_disjoint_fixed {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) :
    Disjoint (residualPairPool D) (ctrlEdges D.BS ∪ gadgetEdges D.R D.S) := by
  rw [Finset.disjoint_left]
  intro e he hfixed
  rw [residualPairPool, Finset.mem_sdiff] at he
  exact he.2 (by simp [residualForbidden, hfixed])

/-- Reciprocal load splits into the part outside `B` and the part inside `B`. -/
lemma recipLoad_eq_sdiff_add_inter (A B : Finset ℕ) :
    R2ConcreteData.recipLoad A =
      R2ConcreteData.recipLoad (A \ B) +
        R2ConcreteData.recipLoad (A ∩ B) := by
  have hdisj : Disjoint (A \ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro x hx hxint
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_inter] at hxint
    exact hx.2 hxint.2
  have hunion : (A \ B) ∪ (A ∩ B) = A := by
    ext x
    by_cases hxA : x ∈ A
    · by_cases hxB : x ∈ B <;> simp [hxA, hxB]
    · simp [hxA]
  calc
    R2ConcreteData.recipLoad A =
        R2ConcreteData.recipLoad ((A \ B) ∪ (A ∩ B)) := by rw [hunion]
    _ = R2ConcreteData.recipLoad (A \ B) +
          R2ConcreteData.recipLoad (A ∩ B) := by
        unfold R2ConcreteData.recipLoad
        rw [Finset.sum_union hdisj]

/-- If the full block-support pair pool beats the target plus the forbidden
budget, then the residual pool beats the target. -/
lemma residualPairPool_load_lower_of_forbidden_budget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (target : ℝ)
    (hbudget :
      target +
          R2ConcreteData.recipLoad
            (blockSupportPairPool D.BS ∩ residualForbidden D)
        ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS)) :
    target ≤ R2ConcreteData.recipLoad (residualPairPool D) := by
  have hsplit :=
    recipLoad_eq_sdiff_add_inter (blockSupportPairPool D.BS) (residualForbidden D)
  rw [residualPairPool] at *
  linarith

/-- Every block-support prime is at least the bottom dyadic scale. -/
lemma blockSupport_ge_k0 {BS : BlockSystem} {p : ℕ}
    (hp : p ∈ blockSupport BS) :
    2 ^ BS.k0 ≤ p := by
  rw [blockSupport, Finset.mem_biUnion] at hp
  obtain ⟨k, hk, hpk⟩ := hp
  have hk0k : BS.k0 ≤ k := (Finset.mem_Icc.mp hk).1
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hk0k)
    (BS.hwindow k p hpk).1

/-- Every residual pair-pool edge is at least `(2^k₀)^2`. -/
lemma residualPairPool_edge_ge_k0_square {T : Finset ℕ} {b e : ℕ}
    (D : R2ConcreteData T b) (he : e ∈ residualPairPool D) :
    2 ^ D.BS.k0 * 2 ^ D.BS.k0 ≤ e := by
  obtain ⟨p, q, hp, hq, _hpq, rfl⟩ := residualPairPool_pair D he
  exact Nat.mul_le_mul (blockSupport_ge_k0 hp) (blockSupport_ge_k0 hq)

/-- Elementary reciprocal comparison used by the residual pool. -/
lemma one_div_nat_lt_three_div_two_mul
    {b e : ℕ} (hb : 0 < b) (he : 0 < e)
    (hlarge : 2 * b < 3 * e) :
    (1 : ℝ) / (e : ℝ) < 3 / (2 * (b : ℝ)) := by
  have heR : 0 < (e : ℝ) := by exact_mod_cast he
  have hbR : 0 < (2 * (b : ℝ)) := by positivity
  rw [div_lt_div_iff₀ heR hbR]
  norm_num
  exact_mod_cast hlarge

/-- A single bottom-scale inequality makes every residual-pool reciprocal small
enough for the greedy residual-window selector. -/
lemma residualPairPool_small_of_k0_square
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 0 < b)
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0)) :
    ∀ e ∈ residualPairPool D,
      (1 : ℝ) / (e : ℝ) < 3 / (2 * (b : ℝ)) := by
  intro e he
  have hedge := residualPairPool_edge_ge_k0_square D he
  have hepos : 0 < e := by omega
  exact one_div_nat_lt_three_div_two_mul hb hepos
    (lt_of_lt_of_le hlarge (Nat.mul_le_mul_left 3 hedge))

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
    (fun e he => residualPairPool_pair D he) (residualPairPool_avoid D)
    (residualPairPool_disjoint_fixed D) hsmall hsum

/-- Final candidate-pool mass-batch endpoint: it is enough to prove one lower
bound for the full block-support pair pool after budgeting the forbidden edges. -/
theorem exists_massBatchSupply_of_pairPool_forbidden_budget
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b)
    (hb : 0 < b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hlarge : 2 * b < 3 * (2 ^ D.BS.k0 * 2 ^ D.BS.k0))
    (hbudget :
      (3 / (2 * (b : ℝ)) - D.baseLoad) +
          R2ConcreteData.recipLoad
            (blockSupportPairPool D.BS ∩ residualForbidden D)
        ≤ R2ConcreteData.recipLoad (blockSupportPairPool D.BS)) :
    ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q) := by
  refine exists_massBatchSupply_of_residualPairPool D hb hbase ?_ ?_
  · exact residualPairPool_small_of_k0_square D hb hlarge
  · exact residualPairPool_load_lower_of_forbidden_budget D
      (3 / (2 * (b : ℝ)) - D.baseLoad) hbudget

end CircleMethod

end
