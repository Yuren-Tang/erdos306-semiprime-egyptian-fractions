import RequestProject.Core.EgyptianRepresentation

open scoped BigOperators Classical

noncomputable section

/-- An avoiding representation theorem for `1 / b` yields distinct-denominator
representations of every natural multiple `a / b`. -/
lemma reduction_to_unit_numerator_avoiding
    (h : ∀ (T : Finset ℕ) (b : ℕ),
      0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b))
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    ∀ a : ℕ, HasEgyptianSemiprimeRepr ((a : ℚ) / b) := by
  intro a
  induction a with
  | zero =>
    refine ⟨∅, ?_, ?_⟩
    · simp
    · simp
  | succ a ih =>
    obtain ⟨S, hSsemi, hSsum⟩ := ih
    obtain ⟨U, hUsemi, hUS, hUsum⟩ := h S b hb hbsf
    refine ⟨S ∪ U, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_union.mp hn with hnS | hnU
      · exact hSsemi n hnS
      · exact hUsemi n hnU
    · rw [Finset.sum_union hUS.symm, hSsum, hUsum]
      simp [add_div]

end
