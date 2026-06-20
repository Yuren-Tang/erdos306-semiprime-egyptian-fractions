import RequestProject.R2TopAssembly
import RequestProject.Erdos306Unconditional
import RequestProject.CannonBridge

/-!
# Erdős 306 — unconditional, wired to the R2 construction

This leaf re-runs the circle-method chain with the genuine R2 existence theorem
`exists_arcConstruction_final` in place of the placeholder
`CircleMethod.exists_arcConstruction` (a `sorry` in `CircleMethodAssembly`,
unfillable there because the R2 construction lives downstream).  The result,
`erdos_306_unconditional`, is sorry-free.
-/

open scoped BigOperators

namespace CircleMethod

/-- `egyptian_rep_ge3` wired to the R2 construction **through the abstract
`spectral_existence` cannon** (`CannonBridge.exists_subset_of_fourier_arcs`):
the genuine R2 `ArcConstruction` supplies the spectral inputs (the low-frequency
main term via `main_sum_re_lower`, the summed-norm high-frequency tail `c.hminor`,
and the domination `c.hbeat`), and the cannon yields a hitting subset directly. -/
theorem egyptian_rep_ge3_R2 (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  obtain ⟨c⟩ := exists_arcConstruction_final T b hb hbsf
  obtain ⟨S, hSE, hSsum⟩ :=
    exists_subset_of_fourier_arcs c.E c.theta b c.L c.SM c.Sm c.Bm
      (0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) / Real.sqrt (sigmaE2 c.E c.theta))
      (by omega) c.hL c.hbL c.heL c.he0 c.hbound
      (fun e he => by linarith [c.hlb e he])
      (fun e he => by linarith [c.hub e he])
      c.hpart c.hdisj
      (main_sum_re_lower c.E c.theta b c.L c.N c.SM c.lbl c.hne c.he0 c.hlb c.hub
        c.hmass c.hN c.htw c.hsmall c.hmaps c.hinj c.hsurj c.hterm)
      c.hminor c.hbeat
  exact repr_of_subset T c.E b c.hsemi c.havoid S hSE hSsum

/-- `egyptian_rep_eq2` (the `b = 2` reduction `1/2 = 1/3 + 1/6`) wired to the R2
construction (its `1/3`, `1/6` sub-representations go through `egyptian_rep_ge3_R2`). -/
theorem egyptian_rep_eq2_R2 (T : Finset ℕ) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (2 : ℚ)) := by
  have sf6 : Squarefree 6 := by
    show Squarefree (2 * 3)
    rw [Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  obtain ⟨S3, hs3semi, hs3disj, hs3sum⟩ :=
    egyptian_rep_ge3_R2 T 3 (by norm_num) Nat.prime_three.squarefree
  obtain ⟨S6, hs6semi, hs6disj, hs6sum⟩ :=
    egyptian_rep_ge3_R2 (T ∪ S3) 6 (by norm_num) sf6
  obtain ⟨hs6T, hs6S3⟩ := Finset.disjoint_union_right.mp hs6disj
  refine ⟨S3 ∪ S6, ?_, Finset.disjoint_union_left.mpr ⟨hs3disj, hs6T⟩, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hs3semi e h
    · exact hs6semi e h
  · rw [Finset.sum_union hs6S3.symm, hs3sum, hs6sum]; norm_num

/-- `egyptian_rep_ge2` wired to the R2 construction. -/
theorem egyptian_rep_ge2_R2 (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  rcases Nat.eq_or_lt_of_le hb with hb2 | hb3
  · rw [← hb2]; exact egyptian_rep_eq2_R2 T
  · exact egyptian_rep_ge3_R2 T b hb3 hbsf

/-- `exists_semiprime_egyptian_one` (`1 = 1/2 + 1/3 + 1/6` with semiprimes) wired
to the R2 construction. -/
theorem exists_semiprime_egyptian_one_R2 (T : Finset ℕ) :
    ∃ G : Finset ℕ, (∀ e ∈ G, IsSemiprime e) ∧ (∀ e ∈ G, e ∉ T) ∧
      (∑ e ∈ G, (1 : ℚ) / (e : ℚ)) = 1 := by
  have sf6 : Squarefree 6 := by
    show Squarefree (2 * 3)
    rw [Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  obtain ⟨S2, hs2semi, hs2disj, hs2sum⟩ :=
    egyptian_rep_ge2_R2 T 2 (by norm_num) Nat.prime_two.squarefree
  obtain ⟨S3, hs3semi, hs3disj, hs3sum⟩ :=
    egyptian_rep_ge2_R2 (T ∪ S2) 3 (by norm_num) Nat.prime_three.squarefree
  obtain ⟨S6, hs6semi, hs6disj, hs6sum⟩ :=
    egyptian_rep_ge2_R2 (T ∪ S2 ∪ S3) 6 (by norm_num) sf6
  obtain ⟨hs3T, hs3S2⟩ := Finset.disjoint_union_right.mp hs3disj
  obtain ⟨hs6TS2, hs6S3⟩ := Finset.disjoint_union_right.mp hs6disj
  obtain ⟨hs6T, hs6S2⟩ := Finset.disjoint_union_right.mp hs6TS2
  have hd23 : Disjoint S2 S3 := hs3S2.symm
  have hd26 : Disjoint S2 S6 := hs6S2.symm
  have hd36 : Disjoint S3 S6 := hs6S3.symm
  refine ⟨S2 ∪ S3 ∪ S6, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h6
    · rcases Finset.mem_union.mp h with h2 | h3
      · exact hs2semi e h2
      · exact hs3semi e h3
    · exact hs6semi e h6
  · intro e he
    rcases Finset.mem_union.mp he with h | h6
    · rcases Finset.mem_union.mp h with h2 | h3
      · exact Finset.disjoint_left.mp hs2disj h2
      · exact Finset.disjoint_left.mp hs3T h3
    · exact Finset.disjoint_left.mp hs6T h6
  · have hd_23_6 : Disjoint (S2 ∪ S3) S6 := Finset.disjoint_union_left.mpr ⟨hd26, hd36⟩
    rw [Finset.sum_union hd_23_6, Finset.sum_union hd23, hs2sum, hs3sum, hs6sum]
    norm_num

/-- `circle_method_positivity` wired to the R2 construction. -/
theorem circle_method_positivity_R2 (T : Finset ℕ) (b : ℕ) (hb : 0 < b)
    (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · have hb1' : b = 1 := by omega
    subst hb1'
    obtain ⟨G, hsemi, havoid, hsum⟩ := exists_semiprime_egyptian_one_R2 T
    exact ⟨G, hsemi, Finset.disjoint_left.mpr havoid, by rw [Nat.cast_one, div_one]; exact hsum⟩
  · rcases Nat.eq_or_lt_of_le hb2 with hb2' | hb3
    · rw [← hb2']; exact egyptian_rep_eq2_R2 T
    · exact egyptian_rep_ge3_R2 T b hb3 hbsf

end CircleMethod

/-- `fourier_positivity_unconditional` wired to the R2 construction. -/
theorem fourier_positivity_unconditional_R2
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b) :=
  CircleMethod.circle_method_positivity_R2 T b hb hbsf

/-- **Erdős Problem 306 — Unconditional (sorry-free).**  For squarefree `b > 0`
and every `a`, `a/b` has an Egyptian representation as a sum of distinct
squarefree-semiprime unit fractions. -/
theorem erdos_306_unconditional (a b : ℕ) (_ : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator_avoiding
    (fun T b hb hbsf => fourier_positivity_unconditional_R2 T b hb hbsf)
    b hb hbsf a

-- Axiom audit: `erdos_306_unconditional` is sorry-free; it depends only on the
-- standard Lean axioms (propext, Classical.choice, Quot.sound) plus three
-- explicitly-axiomatized analytic-number-theory inputs:
--   GlobalControl.dyadic_prime_density        (dyadic-block prime density, PNT-type)
--   GlobalControl.dyadic_mertens_cumulative   (Mertens-type cumulative estimate)
--   CircleMethod.dyadic_control_recipLoad_eventually_small
#print axioms erdos_306_unconditional
