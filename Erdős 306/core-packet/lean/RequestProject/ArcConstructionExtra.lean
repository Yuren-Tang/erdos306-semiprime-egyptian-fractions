import RequestProject.ArcConstruction

open Finset BigOperators Classical

noncomputable section

namespace CircleMethod

open GlobalControl

/-!
# Extra-prime support for the R2 construction

The current R2 obstruction is that mass/gadget edges may introduce primes outside
`blockSupport BS`.  This file names the support split needed for the strengthened
minor-arc interface sketched in note 46.
-/

/-- Prime support of the edge denominators, defined through prime factors.  For
semiprime edges this is exactly the two primes in the edge. -/
def edgePrimeSupport (E : Finset ℕ) : Finset ℕ :=
  E.biUnion Nat.primeFactors

/-- Primes appearing in edges but not in the global-control block support. -/
def extraPrimeSupport (BS : BlockSystem) (E : Finset ℕ) : Finset ℕ :=
  edgePrimeSupport E \ blockSupport BS

lemma mem_edgePrimeSupport {E : Finset ℕ} {p : ℕ} :
    p ∈ edgePrimeSupport E ↔ ∃ e ∈ E, p ∈ Nat.primeFactors e := by
  simp [edgePrimeSupport]

lemma extraPrimeSupport_subset_edgePrimeSupport (BS : BlockSystem) (E : Finset ℕ) :
    extraPrimeSupport BS E ⊆ edgePrimeSupport E := by
  intro p hp
  exact (Finset.mem_sdiff.mp hp).1

lemma extraPrimeSupport_disjoint_blockSupport (BS : BlockSystem) (E : Finset ℕ) :
    Disjoint (extraPrimeSupport BS E) (blockSupport BS) := by
  rw [Finset.disjoint_left]
  intro p hp hblock
  exact (Finset.mem_sdiff.mp hp).2 hblock

/-- Every semiprime edge divides the product of the named edge-prime support. -/
lemma semiprime_dvd_edgePrimeSupport_prod {E : Finset ℕ} {e : ℕ}
    (he : e ∈ E) (hsemi : IsSemiprime e) :
    e ∣ ∏ p ∈ edgePrimeSupport E, p := by
  classical
  rw [← Nat.prod_primeFactors_of_squarefree hsemi.squarefree]
  exact Finset.prod_dvd_prod_of_subset
    (by
      intro p hp
      exact mem_edgePrimeSupport.mpr ⟨e, he, hp⟩)

end CircleMethod

end
