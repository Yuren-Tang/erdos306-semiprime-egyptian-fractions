import Mathlib.Order.Interval.Finset.Nat

/-! Cardinality bounds for finite sets of positive natural numbers. -/

namespace RequestProject

/-- A finite set of positive natural numbers bounded above by `M` has at most
`M` elements. -/
theorem card_le_upper_bound_of_pos (S : Finset ℕ) (M : ℕ)
    (hpos : ∀ n ∈ S, 0 < n) (hupper : ∀ n ∈ S, n ≤ M) :
    S.card ≤ M := by
  calc
    S.card ≤ (Finset.Icc 1 M).card :=
      Finset.card_le_card fun n hn => Finset.mem_Icc.mpr ⟨hpos n hn, hupper n hn⟩
    _ ≤ M := by simp

end RequestProject
