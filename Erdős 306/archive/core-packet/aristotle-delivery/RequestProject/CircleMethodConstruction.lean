import RequestProject.SemiprimeInfinity

open Finset BigOperators Classical

noncomputable section

namespace CircleMethodConstruction

/-!
# Circle-method edge construction (note 35 §C1)

This file isolates the deterministic C1 construction used by the circle-method
layer.  The target package is: for squarefree `b ≥ 2` and a finite obstruction
set `T`, choose semiprime edge denominators avoiding `T`, Bernoulli weights in
`[1/3, 2/3]`, and a common period `L` such that the weighted reciprocal mass is
exactly `1 / b` and the total load is below `L`.

The audited paper construction uses high-scale control/gadget edges at
`θ = 1/2`, then greedy high-scale semiprime batches with a common
`θ_H = Δ / W_H ∈ [1/3, 1/2]` to tune the mass exactly.  The availability of
large dyadic prime blocks is the Chebyshev/Bertrand input mentioned in note
35 §C1 and note 24.
-/

/-- A Chebyshev-style dyadic prime density input, stated as a local Prop so a
future proof can either discharge it from Mathlib or replace the named C1
construction `sorry` below by an explicit hypothesis-driven proof. -/
def chebyshev_block_density : Prop :=
  ∃ x0 : ℕ, ∀ x : ℕ, x0 ≤ x →
    x / (2 * Nat.log 2 x) ≤
      ((Finset.Ico x (2 * x)).filter Nat.Prime).card

/-- The reciprocal load used in the period bookkeeping. -/
def reciprocalLoad (E : Finset ℕ) : ℝ :=
  ∑ e ∈ E, (1 : ℝ) / (e : ℝ)

/-- A simple common period for a finite edge set.  The paper takes the product
of incident primes; for the denominator-only C1 interface, the product of the
edge values is enough and avoids proving pairwise coprimality here. -/
def commonPeriod (b : ℕ) (E : Finset ℕ) : ℕ :=
  b * ∏ e ∈ E, e

/-- Pure greedy overshoot bound: if a finite prime batch has a prefix ordering
whose first crossing of `target` adds a term smaller than `gap`, then the
crossing prefix lies in `[target, target + gap)`.  This is the finite core of
the first-exceedance argument. -/
lemma first_exceedance_window
    (a : ℕ → ℝ) (target gap : ℝ)
    (htarget : 0 ≤ target)
    (_hgap : 0 < gap)
    (_ha_nonneg : ∀ n, 0 ≤ a n)
    (ha_small : ∀ n, a n < gap)
    (hexists : ∃ n, target ≤ ∑ i ∈ Finset.range (n + 1), a i) :
    ∃ n,
      target ≤ ∑ i ∈ Finset.range (n + 1), a i ∧
      ∑ i ∈ Finset.range (n + 1), a i < target + gap := by
  classical
  let n0 := Nat.find hexists
  have hn0 : target ≤ ∑ i ∈ Finset.range (n0 + 1), a i := Nat.find_spec hexists
  refine ⟨n0, hn0, ?_⟩
  by_cases hzero : n0 = 0
  · have hsum0 : (∑ i ∈ Finset.range (n0 + 1), a i) = a 0 := by
      simp [hzero]
    rw [hsum0]
    have htarget_le : target ≤ a 0 := by
      simpa [hsum0] using hn0
    nlinarith [ha_small 0]
  · have hnpos : 0 < n0 := Nat.pos_of_ne_zero hzero
    have hprev_not :
        ¬ target ≤ ∑ i ∈ Finset.range ((n0 - 1) + 1), a i := by
      exact Nat.find_min hexists (Nat.sub_lt hnpos (by omega))
    have hprev_lt : ∑ i ∈ Finset.range n0, a i < target := by
      simpa [Nat.sub_add_cancel hnpos] using not_le.mp hprev_not
    have hsplit :
        ∑ i ∈ Finset.range (n0 + 1), a i =
          ∑ i ∈ Finset.range n0, a i + a n0 := by
      rw [Finset.sum_range_succ]
    rw [hsplit]
    nlinarith [ha_small n0]

/-- Cofinite divergent batch extraction for the thin odd-prime series.

This is the only remaining analytic input: after deleting the finite obstruction
`T` and taking primes large enough that each `1/(2p)` is below `gap`, a finite
batch still carries at least `target` reciprocal mass.  It follows from
`∑ 1 / p` over primes diverging, or equivalently from iterating the
`one_half_le_sum_primes_ge_one_div` block lower bound. -/
theorem exists_large_odd_prime_batch_recip_sum_ge
    (T : Finset ℕ) {target gap : ℝ}
    (_htarget_nonneg : 0 ≤ target) (_hgap : 0 < gap) :
    ∃ P₀ : Finset ℕ,
      (∀ p ∈ P₀,
        Nat.Prime p ∧ 2 < p ∧ 2 * p ∉ T ∧
          (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) < gap) ∧
      target ≤ ∑ p ∈ P₀, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
  classical
  set pred : ℕ → Prop :=
    fun p => Nat.Prime p ∧ 2 < p ∧ 2 * p ∉ T ∧ (1 : ℝ) / ((2:ℝ) * (p:ℝ)) < gap with hpred
  set f : ℕ → ℝ := fun p => if pred p then (1:ℝ) / ((2:ℝ)*(p:ℝ)) else 0 with hf_def
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p; rw [hf_def]; dsimp only; split
    · positivity
    · exact le_refl 0
  -- all sufficiently large primes satisfy `pred`
  have hBound : ∃ B : ℕ, ∀ p, B ≤ p → Nat.Prime p → pred p := by
    refine ⟨(T.sup id) + ⌈(1:ℝ)/(2*gap)⌉₊ + 3, fun p hp hprime => ?_⟩
    refine ⟨hprime, by omega, ?_, ?_⟩
    · intro hmem
      have : 2 * p ≤ T.sup id := Finset.le_sup (f := id) hmem
      omega
    · have hpR : (0:ℝ) < (p:ℝ) := by exact_mod_cast hprime.pos
      have hceil : (1:ℝ)/(2*gap) ≤ (⌈(1:ℝ)/(2*gap)⌉₊ : ℝ) := Nat.le_ceil _
      have hpge : (⌈(1:ℝ)/(2*gap)⌉₊ : ℝ) < (p:ℝ) := by
        have : (⌈(1:ℝ)/(2*gap)⌉₊ : ℕ) < p := by omega
        exact_mod_cast this
      have hp_big : (1:ℝ)/(2*gap) < (p:ℝ) := lt_of_le_of_lt hceil hpge
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)*(p:ℝ))]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2*gap)] at hp_big
      nlinarith [hp_big, hpR, _hgap]
  obtain ⟨Bound, hB⟩ := hBound
  -- `f` is not summable: it equals `½·(prime reciprocal)` off a finite set
  have hns : ¬ Summable f := by
    intro hsum
    apply not_summable_one_div_on_primes
    have key : Set.indicator {p | Nat.Prime p} (fun n => (1:ℝ)/n)
        = (fun p => 2 * f p)
          + (fun p => Set.indicator {p | Nat.Prime p} (fun n => (1:ℝ)/n) p - 2 * f p) := by
      funext p; simp only [Pi.add_apply]; ring
    rw [key]
    refine Summable.add (hsum.mul_left 2) ?_
    apply summable_of_ne_finset_zero (s := Finset.range Bound)
    intro p hp
    simp only [Finset.mem_range, not_lt] at hp
    by_cases hprime : Nat.Prime p
    · have hpr : pred p := hB p hp hprime
      have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hprime.pos.ne'
      rw [Set.indicator_of_mem (Set.mem_setOf.mpr hprime)]
      simp only [hf_def, if_pos hpr]
      field_simp; ring
    · have hnp : p ∉ {p | Nat.Prime p} := by simpa using hprime
      have hnp' : ¬ pred p := by rw [hpred]; tauto
      rw [Set.indicator_of_notMem hnp]
      simp only [hf_def, if_neg hnp', mul_zero, sub_zero]
  -- partial sums diverge ⇒ exceed `target`
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hf_nonneg] at hns
  obtain ⟨n, hn⟩ := (hns.eventually_ge_atTop target).exists
  refine ⟨(Finset.range n).filter pred, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  calc target ≤ ∑ i ∈ Finset.range n, f i := hn
    _ = ∑ p ∈ (Finset.range n).filter pred, (1:ℝ) / ((2:ℝ)*(p:ℝ)) := by
        rw [Finset.sum_filter]

/-- The remaining prime-reciprocal window selection step.

This is the exact divergence/greedy core from `CODEX_TASK_semiprime_window.md`:
after deleting the finite obstruction and taking terms small enough for the
overshoot bound, choose a finite batch of odd primes whose `∑ 1/(2p)` lies in
the target window. -/
theorem exists_finset_primes_recip_between
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p ∧ 2 < p ∧ 2 * p ∉ T) ∧
      (3 / (2 * (b : ℝ)) ≤ ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) ∧
      ((∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) ≤ 3 / (b : ℝ)) ∧
      (∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) < 1 := by
  classical
  let target : ℝ := 3 / (2 * (b : ℝ))
  let gap : ℝ := min target (1 - target)
  have hbR : 0 < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hb
  have htarget_pos : 0 < target := by
    unfold target
    positivity
  have htarget_nonneg : 0 ≤ target := le_of_lt htarget_pos
  have htarget_lt_one : target < 1 := by
    unfold target
    have hbR2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    rw [div_lt_iff₀ (mul_pos (by norm_num) hbR)]
    nlinarith
  have hgap_pos : 0 < gap := by
    unfold gap
    exact lt_min htarget_pos (sub_pos.mpr htarget_lt_one)
  obtain ⟨P₀, hP₀, hP₀sum⟩ :
      ∃ P₀ : Finset ℕ,
        (∀ p ∈ P₀,
          Nat.Prime p ∧ 2 < p ∧ 2 * p ∉ T ∧
            (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) < gap) ∧
        target ≤ ∑ p ∈ P₀, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
    exact exists_large_odd_prime_batch_recip_sum_ge T htarget_nonneg hgap_pos
  let goodSubsets : Finset (Finset ℕ) :=
    P₀.powerset.filter
      (fun P => target ≤ ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)))
  have hgood_nonempty : goodSubsets.Nonempty := by
    refine ⟨P₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, hP₀sum⟩
  obtain ⟨P, hPgood, hPmin⟩ :=
    goodSubsets.exists_minimalFor (fun P : Finset ℕ => P.card) hgood_nonempty
  have hP_subset : P ⊆ P₀ := by
    have := (Finset.mem_filter.mp hPgood).1
    exact Finset.mem_powerset.mp this
  have hPsum_lb : target ≤ ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
    exact (Finset.mem_filter.mp hPgood).2
  have hPprop :
      ∀ p ∈ P, Nat.Prime p ∧ 2 < p ∧ 2 * p ∉ T := by
    intro p hp
    exact ⟨(hP₀ p (hP_subset hp)).1, (hP₀ p (hP_subset hp)).2.1,
      (hP₀ p (hP_subset hp)).2.2.1⟩
  have hPsmall :
      ∀ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) < gap := by
    intro p hp
    exact (hP₀ p (hP_subset hp)).2.2.2
  have hP_nonempty : P.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : target ≤ 0 := by simpa [hne] using hPsum_lb
    linarith
  obtain ⟨p, hp⟩ := hP_nonempty
  have hErase_not_good :
      ¬ target ≤ ∑ q ∈ P.erase p, (1 : ℝ) / ((2 : ℝ) * (q : ℝ)) := by
    intro hcross
    have herase_mem : P.erase p ∈ goodSubsets := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (by
          intro x hx
          exact hP_subset (Finset.mem_of_mem_erase hx)), hcross⟩
    have hcard_lt : (P.erase p).card < P.card := by
      exact Finset.card_erase_lt_of_mem hp
    exact (not_lt_of_ge (hPmin herase_mem (le_of_lt hcard_lt))) hcard_lt
  have hErase_lt :
      ∑ q ∈ P.erase p, (1 : ℝ) / ((2 : ℝ) * (q : ℝ)) < target :=
    not_le.mp hErase_not_good
  have hPsum_split :
      (∑ q ∈ P, (1 : ℝ) / ((2 : ℝ) * (q : ℝ))) =
        ∑ q ∈ P.erase p, (1 : ℝ) / ((2 : ℝ) * (q : ℝ)) +
          (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
    rw [← Finset.sum_erase_add _ _ hp]
  have hPsum_lt_target_gap :
      (∑ q ∈ P, (1 : ℝ) / ((2 : ℝ) * (q : ℝ))) < target + gap := by
    rw [hPsum_split]
    nlinarith [hErase_lt, hPsmall p hp]
  have hPsum_le_three_over_b :
      (∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) ≤ 3 / (b : ℝ) := by
    have hgap_le_target : gap ≤ target := by
      unfold gap
      exact min_le_left _ _
    have hlt : (∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) < target + target := by
      nlinarith
    have htarget_twice : target + target = 3 / (b : ℝ) := by
      unfold target
      field_simp [hbR.ne']
      ring
    exact le_of_lt (by rwa [htarget_twice] at hlt)
  have hPsum_lt_one :
      (∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ))) < 1 := by
    have hgap_le_one_sub : gap ≤ 1 - target := by
      unfold gap
      exact min_le_right _ _
    exact lt_of_lt_of_le hPsum_lt_target_gap (by linarith)
  refine ⟨P, hPprop, ?_, hPsum_le_three_over_b, hPsum_lt_one⟩
  simpa [target] using hPsum_lb

/-- The semiprime reciprocal window needed by the common-θ C1 construction.

This is now just the map `p ↦ 2p` from the prime-window lemma. -/
theorem semiprime_window_exists
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ E : Finset ℕ,
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (3 / (2 * (b : ℝ)) ≤ reciprocalLoad E) ∧
      (reciprocalLoad E ≤ 3 / (b : ℝ)) ∧
      reciprocalLoad E < 1 := by
  classical
  obtain ⟨P, hP, hsum_lb, hsum_ub, hsum_lt⟩ :=
    exists_finset_primes_recip_between T b hb
  have hsum_image :
      reciprocalLoad (P.image (fun p => (2 : ℕ) * p)) =
        ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
    rw [reciprocalLoad]
    calc
      ∑ e ∈ P.image (fun p => (2 : ℕ) * p), (1 : ℝ) / (e : ℝ)
          = ∑ p ∈ P, (1 : ℝ) / ((((2 : ℕ) * p : ℕ) : ℝ)) := by
            rw [Finset.sum_image (by
              intro p hp q hq hpq
              exact Nat.mul_left_cancel (by norm_num : 0 < 2)
                (show (2 : ℕ) * p = (2 : ℕ) * q from hpq))]
      _ = ∑ p ∈ P, (1 : ℝ) / ((2 : ℝ) * (p : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            norm_num
  refine ⟨P.image (fun p => (2 : ℕ) * p), ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨p, hpP, rfl⟩
    exact ⟨2, p, Nat.prime_two, (hP p hpP).1, (hP p hpP).2.1, rfl⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨p, hpP, rfl⟩
    exact (hP p hpP).2.2
  · simpa [hsum_image] using hsum_lb
  · simpa [hsum_image] using hsum_ub
  · simpa [hsum_image] using hsum_lt

/-- Once the C1 greedy step has produced semiprime denominators, weights with
the exact mass, and reciprocal load `< 1`, the common-period and load
bookkeeping is elementary. -/
theorem assemble_period_from_mass_package
    (T E : Finset ℕ) (θ : ℕ → ℝ) (b : ℕ) (hb : 0 < b)
    (hsemi : ∀ e ∈ E, IsSemiprime e)
    (havoid : ∀ e ∈ E, e ∉ T)
    (hθ : ∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ))
    (hmass : (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ))
    (hload : reciprocalLoad E < 1) :
    ∃ (L : ℕ),
      0 < L ∧
      b ∣ L ∧
      (∀ e ∈ E, e ∣ L) ∧
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      (∑ e ∈ E, (L / e : ℕ)) < L := by
  classical
  refine ⟨commonPeriod b E, ?_⟩
  have hprod_pos : 0 < ∏ e ∈ E, e := by
    exact Finset.prod_pos fun e he => (hsemi e he).pos
  have hLpos : 0 < commonPeriod b E := by
    unfold commonPeriod
    exact Nat.mul_pos hb hprod_pos
  have hEdvd : ∀ e ∈ E, e ∣ commonPeriod b E := by
    intro e he
    unfold commonPeriod
    exact dvd_trans (Finset.dvd_prod_of_mem id he) (Nat.dvd_mul_left _ _)
  have hload_cast :
      (∑ e ∈ E, ((commonPeriod b E / e : ℕ) : ℝ)) =
        (commonPeriod b E : ℝ) * reciprocalLoad E := by
    unfold reciprocalLoad
    calc
      ∑ x ∈ E, ((commonPeriod b E / x : ℕ) : ℝ)
          = ∑ x ∈ E, (commonPeriod b E : ℝ) / (x : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hxpos : 0 < x := (hsemi x hx).pos
            have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hxpos.ne'
            rw [Nat.cast_div (hEdvd x hx) hxR]
      _ = ∑ x ∈ E, (commonPeriod b E : ℝ) * ((1 : ℝ) / (x : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            field_simp
      _ = (commonPeriod b E : ℝ) * ∑ x ∈ E, (1 : ℝ) / (x : ℝ) := by
            rw [Finset.mul_sum]
  have hload_nat :
      (∑ e ∈ E, (commonPeriod b E / e : ℕ)) < commonPeriod b E := by
    rw [← Nat.cast_lt (α := ℝ)]
    rw [Nat.cast_sum]
    rw [hload_cast]
    have hLposR : 0 < (commonPeriod b E : ℝ) := by exact_mod_cast hLpos
    nlinarith
  exact ⟨hLpos, dvd_mul_right b _, hEdvd, hsemi, havoid, hθ, hmass, hload_nat⟩

/-- The C1 greedy mass package, before choosing a common period.

This uses the common-θ simplification from `CODEX_TASK_c1_commontheta.md`.
Once `semiprime_window_exists` provides reciprocal load in `[3/(2b), 3/b]`,
the constant choice `θ = (1/b) / reciprocalLoad E` gives exact mass and
automatically lies in `[1/3, 2/3]`. -/

theorem circle_method_edge_mass_package
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (_hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ),
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      reciprocalLoad E < 1 := by
  classical
  obtain ⟨E, hsemi, havoid, hload_lb, hload_ub, hload_lt⟩ :=
    semiprime_window_exists T b hb
  let θ : ℕ → ℝ := fun _ => (1 / (b : ℝ)) / reciprocalLoad E
  have hbpos : 0 < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hb
  have hload_pos : 0 < reciprocalLoad E := by
    have : 0 < 3 / (2 * (b : ℝ)) := by positivity
    exact lt_of_lt_of_le this hload_lb
  have hload_ub_mul : reciprocalLoad E * (b : ℝ) ≤ 3 := by
    rw [le_div_iff₀ hbpos] at hload_ub
    nlinarith
  have hload_lb_mul : 3 ≤ 2 * (b : ℝ) * reciprocalLoad E := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hbpos)] at hload_lb
    nlinarith
  have hθ_lb : (1 / 3 : ℝ) ≤ (1 / (b : ℝ)) / reciprocalLoad E := by
    rw [le_div_iff₀ hload_pos]
    rw [le_div_iff₀ hbpos]
    nlinarith
  have hθ_ub : (1 / (b : ℝ)) / reciprocalLoad E ≤ (2 / 3 : ℝ) := by
    rw [div_le_iff₀ hload_pos]
    rw [div_le_iff₀ hbpos]
    nlinarith
  have hmass :
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) := by
    have hsum_ne : (∑ x ∈ E, (1 : ℝ) / (x : ℝ)) ≠ 0 := by
      simpa [reciprocalLoad] using hload_pos.ne'
    unfold θ reciprocalLoad
    calc
      ∑ e ∈ E, ((1 / (b : ℝ)) / (∑ x ∈ E, (1 : ℝ) / (x : ℝ))) / (e : ℝ)
          =
        ∑ e ∈ E, ((1 / (b : ℝ)) / (∑ x ∈ E, (1 : ℝ) / (x : ℝ))) *
          ((1 : ℝ) / (e : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            ring
      _ =
        ((1 / (b : ℝ)) / (∑ x ∈ E, (1 : ℝ) / (x : ℝ))) *
          ∑ e ∈ E, (1 : ℝ) / (e : ℝ) := by
            rw [Finset.mul_sum]
      _ = 1 / (b : ℝ) := by
            field_simp [hsum_ne]
  refine ⟨E, θ, hsemi, havoid, ?_, hmass, hload_lt⟩
  intro e he
  exact ⟨hθ_lb, hθ_ub⟩

/-- The full C1 construction package.  This is separated from the public theorem
so the remaining audited construction gap has a precise name. -/
theorem circle_method_edge_construction_core
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ) (L : ℕ),
      0 < L ∧
      b ∣ L ∧
      (∀ e ∈ E, e ∣ L) ∧
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      (∑ e ∈ E, (L / e : ℕ)) < L := by
  obtain ⟨E, θ, hsemi, havoid, hθ, hmass, hload⟩ :=
    circle_method_edge_mass_package T b hb hbsf
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  obtain ⟨L, hLpos, hbL, hEdvd, hsemi', havoid', hθ', hmass', hload'⟩ :=
    assemble_period_from_mass_package T E θ b hbpos hsemi havoid hθ hmass hload
  exact ⟨E, θ, L, hLpos, hbL, hEdvd, hsemi', havoid', hθ', hmass', hload'⟩

/-- **C1 edge construction, final route statement.**  For every squarefree
`b ≥ 2` and finite obstruction set `T`, there are semiprime edge denominators,
weights, and a common period satisfying the exact mass and load conditions. -/
theorem circle_method_edge_construction
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (θ : ℕ → ℝ) (L : ℕ),
      0 < L ∧
      b ∣ L ∧
      (∀ e ∈ E, e ∣ L) ∧
      (∀ e ∈ E, IsSemiprime e) ∧
      (∀ e ∈ E, e ∉ T) ∧
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ θ e ∧ θ e ≤ (2 / 3 : ℝ)) ∧
      (∑ e ∈ E, θ e / (e : ℝ)) = 1 / (b : ℝ) ∧
      (∑ e ∈ E, (L / e : ℕ)) < L := by
  exact circle_method_edge_construction_core T b hb hbsf

end CircleMethodConstruction

end
