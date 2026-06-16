/-
# Numerator reduction: from `1/b` to `a/b`

This file contains the elementary, fully machine-verified reduction that turns a
"unit-fraction" representation theorem (every `1/b` is a sum of distinct
squarefree semiprimes, with denominators avoiding any prescribed finite set)
into the general statement for `a/b`.

It is deliberately *independent* of the analytic core: the unit-fraction input
is taken as an explicit hypothesis `h`, so this lemma is reusable by any route
that supplies such an input (here, the unconditional circle-method route in
`FourierPositivity` / `CircleMethod`).
-/
import Mathlib
import RequestProject.Defs

open scoped BigOperators Classical

noncomputable section

/-! ## Reduction from `a/b` to `1/b` via denominator avoidance -/

/-- **Reduction to unit numerator (avoiding version).**

Given a unit-fraction theorem — for every finite obstruction set `T` and
squarefree `b`, there exists a distinct-squarefree-semiprime Egyptian
representation of `1/b` with denominators disjoint from `T` — we deduce that
`a/b` has such a representation for every `a`.

**Proof (induction on `a`).**
* Base `a = 0`: the empty set represents `0 = 0/b`.
* Step `a → a+1`: take `S` for `a/b` (induction hypothesis); apply the avoiding
  input with obstruction set `S` to get `U` for `1/b` with `Disjoint U S`; then
  `S ∪ U` represents `(a+1)/b`. -/
lemma reduction_to_unit_numerator_avoiding
    (h : ∀ (T : Finset ℕ) (b : ℕ),
      0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b))
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    ∀ a : ℕ, HasEgyptianSemiprimeRepr ((a : ℚ) / b) := by
  intro a
  induction' a with a ih
  · exact ⟨∅, by norm_num⟩
  · obtain ⟨S, hS₁, hS₂⟩ := ih
    specialize h S b hb hbsf
    rcases h with ⟨U, hU₁, hU₂, hU₃⟩
    have hSU : Disjoint S U := (Finset.disjoint_left.mpr
      fun x hxS hxU => (Finset.disjoint_left.mp hU₂ hxU) hxS)
    refine ⟨S ∪ U, ?_, ?_⟩
    · exact fun n hn => (Finset.mem_union.mp hn).elim (hS₁ n) (hU₁ n)
    · rw [Finset.sum_union hSU, hS₂, hU₃]
      push_cast; ring

end
