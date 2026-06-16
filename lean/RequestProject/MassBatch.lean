import RequestProject.CircleMethodConstruction

open Finset BigOperators Classical

noncomputable section

namespace CircleMethod

/-- Cofinite divergent batch extraction for products `p0*q` with fixed prime `p0`.

After deleting a finite obstruction set and taking `q` large enough that each
term is below `gap`, a finite batch of prime products still carries at least
`target` reciprocal mass. -/
theorem exists_fixedPrime_largePrimeProduct_batch_recip_sum_ge
    (T : Finset ℕ) (p0 : ℕ) (hp0 : Nat.Prime p0) {target gap : ℝ}
    (_htarget_nonneg : 0 ≤ target) (hgap : 0 < gap) :
    ∃ Q₀ : Finset ℕ,
      (∀ q ∈ Q₀,
        Nat.Prime q ∧ p0 < q ∧ p0 * q ∉ T ∧
          (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) < gap) ∧
      target ≤ ∑ q ∈ Q₀, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) := by
  classical
  set pred : ℕ → Prop :=
    fun q => Nat.Prime q ∧ p0 < q ∧ p0 * q ∉ T ∧
      (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) < gap with hpred
  set f : ℕ → ℝ := fun q => if pred q then (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) else 0
    with hf_def
  have hp0R : 0 < (p0 : ℝ) := by exact_mod_cast hp0.pos
  have hf_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    rw [hf_def]
    dsimp only
    split
    · positivity
    · exact le_refl 0
  have hBound : ∃ B : ℕ, ∀ q, B ≤ q → Nat.Prime q → pred q := by
    refine ⟨(T.sup id) + p0 + ⌈(1 : ℝ) / ((p0 : ℝ) * gap)⌉₊ + 3,
      fun q hq hprime => ?_⟩
    refine ⟨hprime, by omega, ?_, ?_⟩
    · intro hmem
      have : p0 * q ≤ T.sup id := Finset.le_sup (f := id) hmem
      have hq_pos : 0 < q := hprime.pos
      have hsup_lt_q : T.sup id < q := by omega
      have hprod_gt_sup : T.sup id < p0 * q :=
        lt_of_lt_of_le hsup_lt_q (Nat.le_mul_of_pos_left q hp0.pos)
      omega
    · have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hprime.pos
      have hceil : (1 : ℝ) / ((p0 : ℝ) * gap) ≤
          (⌈(1 : ℝ) / ((p0 : ℝ) * gap)⌉₊ : ℝ) := Nat.le_ceil _
      have hqge : (⌈(1 : ℝ) / ((p0 : ℝ) * gap)⌉₊ : ℝ) < (q : ℝ) := by
        have : (⌈(1 : ℝ) / ((p0 : ℝ) * gap)⌉₊ : ℕ) < q := by omega
        exact_mod_cast this
      have hq_big : (1 : ℝ) / ((p0 : ℝ) * gap) < (q : ℝ) :=
        lt_of_le_of_lt hceil hqge
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (p0 : ℝ) * (q : ℝ))]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (p0 : ℝ) * gap)] at hq_big
      nlinarith [hq_big, hp0R, hqR, hgap]
  obtain ⟨Bound, hB⟩ := hBound
  have hns : ¬ Summable f := by
    intro hsum
    apply not_summable_one_div_on_primes
    have key : Set.indicator {q | Nat.Prime q} (fun n => (1 : ℝ) / n)
        = (fun q => (p0 : ℝ) * f q)
          + (fun q => Set.indicator {q | Nat.Prime q} (fun n => (1 : ℝ) / n) q -
              (p0 : ℝ) * f q) := by
      funext q
      simp only [Pi.add_apply]
      ring
    rw [key]
    refine Summable.add (hsum.mul_left (p0 : ℝ)) ?_
    apply summable_of_ne_finset_zero (s := Finset.range Bound)
    intro q hq
    simp only [Finset.mem_range, not_lt] at hq
    by_cases hprime : Nat.Prime q
    · have hpr : pred q := hB q hq hprime
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hprime.pos.ne'
      rw [Set.indicator_of_mem (Set.mem_setOf.mpr hprime)]
      simp only [hf_def, if_pos hpr]
      field_simp [hp0R.ne', hq0]
      ring
    · have hnp : q ∉ {q | Nat.Prime q} := by simpa using hprime
      have hnp' : ¬ pred q := by rw [hpred]; tauto
      rw [Set.indicator_of_notMem hnp]
      simp only [hf_def, if_neg hnp', mul_zero, sub_zero]
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hf_nonneg] at hns
  obtain ⟨n, hn⟩ := (hns.eventually_ge_atTop target).exists
  refine ⟨(Finset.range n).filter pred, fun q hq => (Finset.mem_filter.mp hq).2, ?_⟩
  calc target ≤ ∑ i ∈ Finset.range n, f i := hn
    _ = ∑ q ∈ (Finset.range n).filter pred, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) := by
      rw [Finset.sum_filter]

/-- Prime-product reciprocal window, before mapping the prime batch to products. -/
theorem exists_largePrimeProduct_prime_batch_recip_between
    (T : Finset ℕ) (N0 : ℕ) {target gap : ℝ}
    (htarget : 0 ≤ target) (hgap : 0 < gap) :
    ∃ (p0 : ℕ) (Q : Finset ℕ),
      Nat.Prime p0 ∧ N0 ≤ p0 ∧
      (∀ q ∈ Q,
        Nat.Prime q ∧ p0 < q ∧ p0 * q ∉ T ∧
          (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) < gap) ∧
      target ≤ ∑ q ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) ∧
      ∑ q ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) ≤ target + gap := by
  classical
  obtain ⟨p0, hp0_ge, hp0⟩ := Nat.exists_infinite_primes N0
  obtain ⟨Q₀, hQ₀, hQ₀sum⟩ :=
    exists_fixedPrime_largePrimeProduct_batch_recip_sum_ge T p0 hp0 htarget hgap
  let goodSubsets : Finset (Finset ℕ) :=
    Q₀.powerset.filter
      (fun Q => target ≤ ∑ q ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)))
  have hgood_nonempty : goodSubsets.Nonempty := by
    refine ⟨Q₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, hQ₀sum⟩
  obtain ⟨Q, hQgood, hQmin⟩ :=
    goodSubsets.exists_minimalFor (fun Q : Finset ℕ => Q.card) hgood_nonempty
  have hQ_subset : Q ⊆ Q₀ := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hQgood).1
  have hQsum_lb : target ≤ ∑ q ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) :=
    (Finset.mem_filter.mp hQgood).2
  have hQprop :
      ∀ q ∈ Q,
        Nat.Prime q ∧ p0 < q ∧ p0 * q ∉ T ∧
          (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) < gap := by
    intro q hq
    exact hQ₀ q (hQ_subset hq)
  by_cases htarget_zero : target = 0
  · refine ⟨p0, ∅, hp0, hp0_ge, ?_, ?_, ?_⟩
    · intro q hq
      simp at hq
    · simp [htarget_zero]
    · simp [htarget_zero, hgap.le]
  have htarget_pos : 0 < target :=
    lt_of_le_of_ne htarget (fun h => htarget_zero h.symm)
  have hQ_nonempty : Q.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : target ≤ 0 := by simpa [hne] using hQsum_lb
    linarith
  obtain ⟨q, hq⟩ := hQ_nonempty
  have hErase_not_good :
      ¬ target ≤ ∑ r ∈ Q.erase q, (1 : ℝ) / ((p0 : ℝ) * (r : ℝ)) := by
    intro hcross
    have herase_mem : Q.erase q ∈ goodSubsets := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (by
          intro x hx
          exact hQ_subset (Finset.mem_of_mem_erase hx)), hcross⟩
    have hcard_lt : (Q.erase q).card < Q.card := by
      exact Finset.card_erase_lt_of_mem hq
    exact (not_lt_of_ge (hQmin herase_mem (le_of_lt hcard_lt))) hcard_lt
  have hErase_lt :
      ∑ r ∈ Q.erase q, (1 : ℝ) / ((p0 : ℝ) * (r : ℝ)) < target :=
    not_le.mp hErase_not_good
  have hQsum_split :
      (∑ r ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (r : ℝ))) =
        ∑ r ∈ Q.erase q, (1 : ℝ) / ((p0 : ℝ) * (r : ℝ)) +
          (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) := by
    rw [← Finset.sum_erase_add _ _ hq]
  have hQsum_lt_target_gap :
      (∑ r ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (r : ℝ))) < target + gap := by
    rw [hQsum_split]
    nlinarith [(hQprop q hq).2.2.2, hErase_lt]
  refine ⟨p0, Q, hp0, hp0_ge, hQprop, hQsum_lb, le_of_lt hQsum_lt_target_gap⟩

/-- For a finite obstruction set, a target, a gap, and a threshold `N0`, there is
a finite set of products of two distinct primes, both at least `N0`, avoiding the
obstructions, whose reciprocal sum lies in `[target, target + gap]`. -/
theorem exists_largePrimeProduct_batch_recip_between
    (T : Finset ℕ) (N0 : ℕ) {target gap : ℝ}
    (htarget : 0 ≤ target) (hgap : 0 < gap) :
    ∃ F : Finset ℕ,
      (∀ e ∈ F, ∃ p q,
        Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ N0 ≤ p ∧ N0 ≤ q ∧ e = p * q) ∧
      (∀ e ∈ F, e ∉ T) ∧
      target ≤ ∑ e ∈ F, (1 : ℝ) / (e : ℝ) ∧
      ∑ e ∈ F, (1 : ℝ) / (e : ℝ) ≤ target + gap := by
  classical
  obtain ⟨p0, Q, hp0, hp0_ge, hQprop, hQsum_lb, hQsum_ub⟩ :=
    exists_largePrimeProduct_prime_batch_recip_between T N0 htarget hgap
  have hp0_pos : 0 < p0 := hp0.pos
  have hsum_image :
      (∑ e ∈ Q.image (fun q => p0 * q), (1 : ℝ) / (e : ℝ)) =
        ∑ q ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) := by
    calc
      ∑ e ∈ Q.image (fun q => p0 * q), (1 : ℝ) / (e : ℝ)
          = ∑ q ∈ Q, (1 : ℝ) / (((p0 * q : ℕ) : ℝ)) := by
            rw [Finset.sum_image]
            intro q hq r hr hqr
            exact Nat.mul_left_cancel hp0_pos (show p0 * q = p0 * r from hqr)
      _ = ∑ q ∈ Q, (1 : ℝ) / ((p0 : ℝ) * (q : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            norm_num
  refine ⟨Q.image (fun q => p0 * q), ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨q, hqQ, rfl⟩
    exact ⟨p0, q, hp0, (hQprop q hqQ).1, (hQprop q hqQ).2.1,
      hp0_ge, le_trans hp0_ge (le_of_lt (hQprop q hqQ).2.1), rfl⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨q, hqQ, rfl⟩
    exact (hQprop q hqQ).2.2.1
  · rw [hsum_image]
    exact hQsum_lb
  · rw [hsum_image]
    exact hQsum_ub

end CircleMethod

end
