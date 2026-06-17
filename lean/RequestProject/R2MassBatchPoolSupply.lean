import RequestProject.R2ComponentSupply

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass-batch pool supply

`R2MassBatchSupply` is the final record consumed by the assembly theorem once the
residual batch `Q` has already been chosen.  This file adds the preceding
selection bridge: if a finite candidate pool `P` has enough reciprocal mass and
all its elements have the right structural properties, choose a subset `Q` and
produce the packaged `R2MassBatchSupply`.
-/

namespace R2ConcreteData

variable {T : Finset ℕ} {b : ℕ}

/-- Replace only the residual mass batch of an `R2ConcreteData` record. -/
def withQ (D : R2ConcreteData T b) (Q : Finset ℕ) : R2ConcreteData T b :=
  { BS := D.BS, Q := Q, R := D.R, S := D.S }

@[simp] lemma withQ_BS (D : R2ConcreteData T b) (Q : Finset ℕ) :
    (D.withQ Q).BS = D.BS := rfl

@[simp] lemma withQ_Q (D : R2ConcreteData T b) (Q : Finset ℕ) :
    (D.withQ Q).Q = Q := rfl

@[simp] lemma withQ_R (D : R2ConcreteData T b) (Q : Finset ℕ) :
    (D.withQ Q).R = D.R := rfl

@[simp] lemma withQ_S (D : R2ConcreteData T b) (Q : Finset ℕ) :
    (D.withQ Q).S = D.S := rfl

@[simp] lemma withQ_baseLoad (D : R2ConcreteData T b) (Q : Finset ℕ) :
    (D.withQ Q).baseLoad = D.baseLoad := rfl

end R2ConcreteData

/-- A candidate residual pool supplies a valid mass-batch subset.

The hypotheses are deliberately local to the pool `P`: every candidate is a
product of two ordered block-support primes, avoids the obstruction set, is
disjoint from the fixed control/gadget edges, is individually small enough for
the greedy window, and has enough total reciprocal mass to fill the residual
gap below `3/(2b)`.
-/
theorem exists_massBatchSupply_of_pool
    {T : Finset ℕ} {b : ℕ}
    (D : R2ConcreteData T b) (P : Finset ℕ)
    (hb : 0 < b)
    (hbase : D.baseLoad < 3 / (2 * (b : ℝ)))
    (hpair : ∀ e ∈ P, ∃ p q,
      p ∈ blockSupport D.BS ∧ q ∈ blockSupport D.BS ∧ p < q ∧ e = p * q)
    (havoid : ∀ e ∈ P, e ∉ T)
    (hdisj : Disjoint P (ctrlEdges D.BS ∪ gadgetEdges D.R D.S))
    (hsmall : ∀ e ∈ P, (1 : ℝ) / (e : ℝ) < 3 / (2 * (b : ℝ)))
    (hsum : 3 / (2 * (b : ℝ)) - D.baseLoad ≤ R2ConcreteData.recipLoad P) :
    ∃ Q : Finset ℕ, R2MassBatchSupply (D.withQ Q) := by
  obtain ⟨Q, hQsub, hQlower, hQupper⟩ :=
    R2ConcreteData.exists_residual_subset_recip_window P D.baseLoad b hb
      hbase hsmall hsum
  refine ⟨Q, ?_⟩
  have hQne : Q.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hQempty
    have htarget_le_base : 3 / (2 * (b : ℝ)) ≤ D.baseLoad := by
      simpa [R2ConcreteData.recipLoad, hQempty] using hQlower
    exact not_lt_of_ge htarget_le_base hbase
  refine
    { hQpair := ?_
      hQavoid := ?_
      hQne := hQne
      hloadDisj := ?_
      hloadLower := ?_
      hloadUpper := ?_ }
  · intro e he
    simpa using hpair e (hQsub he)
  · intro e he
    exact havoid e (hQsub he)
  · simpa [R2ConcreteData.withQ] using hdisj.mono_left hQsub
  · simpa [R2ConcreteData.withQ] using hQlower
  · simpa [R2ConcreteData.withQ] using hQupper

end CircleMethod

end
