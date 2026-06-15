import RequestProject.R2MinorSupportBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 mass-batch supply

This thin leaf packages the structural facts about the residual mass batch
`D.Q`.  The final construction only needs `Q` to consist of products of two
distinct block-support primes, to avoid the obstruction set, and to satisfy the
residual load window/disjointness conditions.
-/

/-- Structural and load-window supply for the residual mass batch `D.Q`. -/
structure R2MassBatchSupply
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) where
  hQpair : ∀ e ∈ D.Q, ∃ p q,
    p ∈ blockSupport D.BS ∧ q ∈ blockSupport D.BS ∧ p < q ∧ e = p * q
  hQavoid : ∀ e ∈ D.Q, e ∉ T
  hQne : D.Q.Nonempty
  hloadDisj : Disjoint D.Q (ctrlEdges D.BS ∪ gadgetEdges D.R D.S)
  hloadLower :
    3 / (2 * (b : ℝ)) ≤ D.baseLoad + R2ConcreteData.recipLoad D.Q
  hloadUpper :
    D.baseLoad + R2ConcreteData.recipLoad D.Q < 3 / (b : ℝ)

namespace R2MassBatchSupply

variable {T : Finset ℕ} {b : ℕ} {D : R2ConcreteData T b}

/-- Products of two ordered block-support primes are semiprimes. -/
lemma q_semiprime (S : R2MassBatchSupply D) :
    ∀ e ∈ D.Q, IsSemiprime e := by
  intro e he
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := S.hQpair e he
  exact ⟨p, q, blockSupport_prime D.BS hp, blockSupport_prime D.BS hq, hpq, rfl⟩

/-- Positivity of every mass-batch edge. -/
lemma q_pos (S : R2MassBatchSupply D) :
    ∀ e ∈ D.Q, 0 < e := by
  intro e he
  exact (S.q_semiprime e he).pos

/-- Every mass-batch edge divides the concrete period. -/
lemma q_dvd_period (S : R2MassBatchSupply D) :
    ∀ e ∈ D.Q, e ∣ D.L := by
  intro e he
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := S.hQpair e he
  have hpprime : Nat.Prime p := blockSupport_prime D.BS hp
  have hqprime : Nat.Prime q := blockSupport_prime D.BS hq
  have hpdvd : p ∣ ∏ r ∈ blockSupport D.BS, r :=
    Finset.dvd_prod_of_mem id hp
  have hqdvd : q ∣ ∏ r ∈ blockSupport D.BS, r :=
    Finset.dvd_prod_of_mem id hq
  have hcop : Nat.Coprime p q := by
    exact hpprime.coprime_iff_not_dvd.mpr fun hdiv => by
      have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp hdiv
      omega
  have hpq_dvd : p * q ∣ ∏ r ∈ blockSupport D.BS, r :=
    hcop.mul_dvd_of_dvd_of_dvd hpdvd hqdvd
  rw [R2ConcreteData.L]
  exact edge_dvd_primeSupportPeriod_of_mem_support hpq_dvd

end R2MassBatchSupply

/-- Final R2 socket with the mass-batch structural/load data packaged. -/
theorem exists_arcConstruction_of_massBatchSupply
    {T : Finset ℕ} {b : ℕ}
    (hb : 3 ≤ b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (Bblock Bextra ρ K : ℝ)
    (hadm : admissibleGlobalRange D.BS)
    (hNscale : (1 : ℝ) / Real.sqrt (sigmaE2 D.E W.theta) ≤ (N : ℝ))
    (hρnonneg : 0 ≤ ρ)
    (hρle : ρ ≤ 1 / 10)
    (hctrledge : ∀ e ∈ ctrlEdges D.BS, (N : ℝ) ≤ ρ * (e : ℝ))
    (hQedge : ∀ e ∈ D.Q, (N : ℝ) ≤ ρ * (e : ℝ))
    (hgadgetedge : ∀ e ∈ gadgetEdges D.R D.S, (N : ℝ) ≤ ρ * (e : ℝ))
    (hcomponentCard :
      ((ctrlEdges D.BS).card + D.Q.card + (gadgetEdges D.R D.S).card : ℝ) ≤ K)
    (hK : K * 100000 * ρ ^ 3 ≤ 1 / 10)
    (hNL : 2 * N + 1 ≤ (D.L : ℤ))
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hSprime : ∀ s ∈ D.S, Nat.Prime s)
    (hlt : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s)
    (hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T)
    (hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T)
    (hRdvd : ∀ r ∈ D.R, r ∣ b)
    (hSblock : D.S ⊆ blockSupport D.BS)
    (QB : R2MassBatchSupply D)
    (MB : R2MinorSupportBudgetData D W N Bblock Bextra)
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1 / (e : ℝ) ^ 2
        ≤ 3 * (sigmaCtrl D.BS) ^ 2)
    (hminorCtrl :
      Bblock + Bextra <
        (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2)) / sigmaCtrl D.BS) :
    Nonempty (ArcConstruction T b) := by
  have hctrlpos : ∀ e ∈ ctrlEdges D.BS, 0 < e := by
    intro e he
    exact (ctrlEdges_semiprime D.BS he).pos
  have hgadgetpos : ∀ e ∈ gadgetEdges D.R D.S, 0 < e := by
    intro e he
    exact (gadgetEdges_semiprime hRprime hSprime hlt e he).pos
  exact exists_arcConstruction_of_component_rho_numeric_minor_budget hb D W N
    Bblock Bextra ρ K hadm hNscale hρnonneg hρle
    hctrlpos hctrledge (QB.q_pos) hQedge hgadgetpos hgadgetedge
    hcomponentCard hK hNL (QB.q_semiprime) hRprime hSprime hlt
    hctrlAvoid QB.hQavoid hgadgetAvoid QB.hQne (QB.q_dvd_period)
    hRdvd hSblock QB.hloadDisj QB.hloadLower QB.hloadUpper
    MB hextraLight hminorCtrl

end CircleMethod

end
