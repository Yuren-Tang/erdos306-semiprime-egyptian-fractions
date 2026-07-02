import RequestProject.Core.Semiprime

open scoped BigOperators

/-- A finite set of distinct semiprimes whose unit fractions sum to `r`. -/
def HasEgyptianSemiprimeRepr (r : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, IsSemiprime n) ∧
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = r

/-- Such a representation whose denominators avoid a prescribed finite set. -/
def HasEgyptianSemiprimeReprAvoiding (T : Finset ℕ) (r : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, IsSemiprime n) ∧
    Disjoint S T ∧
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = r
