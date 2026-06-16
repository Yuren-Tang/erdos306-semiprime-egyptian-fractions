import RequestProject.ArcConstruction
import RequestProject.FiberCount

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

lemma mem_extraPrimeSupport (BS : BlockSystem) (E : Finset ℕ) (p : ℕ) :
    p ∈ extraPrimeSupport BS E ↔ p ∈ edgePrimeSupport E ∧ p ∉ blockSupport BS := by
  simp [extraPrimeSupport]

lemma edgePrimeSupport_mono {E F : Finset ℕ} (hEF : E ⊆ F) :
    edgePrimeSupport E ⊆ edgePrimeSupport F := by
  intro p hp
  rw [mem_edgePrimeSupport] at hp ⊢
  obtain ⟨e, he, hp⟩ := hp
  exact ⟨e, hEF he, hp⟩

lemma edgePrimeSupport_union (E F : Finset ℕ) :
    edgePrimeSupport (E ∪ F) = edgePrimeSupport E ∪ edgePrimeSupport F := by
  ext p
  constructor
  · intro hp
    rw [mem_edgePrimeSupport] at hp
    obtain ⟨e, he, hp⟩ := hp
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact Finset.mem_union_left _ (mem_edgePrimeSupport.mpr ⟨e, he, hp⟩)
    · exact Finset.mem_union_right _ (mem_edgePrimeSupport.mpr ⟨e, he, hp⟩)
  · intro hp
    rw [Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [mem_edgePrimeSupport] at hp ⊢
      obtain ⟨e, he, hp⟩ := hp
      exact ⟨e, Finset.mem_union_left _ he, hp⟩
    · rw [mem_edgePrimeSupport] at hp ⊢
      obtain ⟨e, he, hp⟩ := hp
      exact ⟨e, Finset.mem_union_right _ he, hp⟩

lemma edgePrimeSupport_insert (e : ℕ) (E : Finset ℕ) :
    edgePrimeSupport (insert e E) = Nat.primeFactors e ∪ edgePrimeSupport E := by
  rw [show insert e E = {e} ∪ E by ext p; simp]
  rw [edgePrimeSupport_union]
  ext p
  simp [edgePrimeSupport]

/-- Every semiprime edge divides the product of the named edge-prime support. -/
lemma semiprime_dvd_edgePrimeSupport_prod {E : Finset ℕ} {e : ℕ}
    (he : e ∈ E) (hsemi : IsSemiprime e) :
    e ∣ ∏ p ∈ edgePrimeSupport E, p := by
  classical
  rw [← Nat.prod_primeFactors_of_squarefree hsemi.squarefree]
  exact Finset.prod_dvd_prod_of_subset (Nat.primeFactors e) (edgePrimeSupport E) id
    (fun p hp => mem_edgePrimeSupport.mpr ⟨e, he, hp⟩)

lemma all_edges_dvd_edgePrimeSupport_prod
    (E : Finset ℕ) (hsemi : ∀ e ∈ E, IsSemiprime e) :
    ∀ e ∈ E, e ∣ ∏ p ∈ edgePrimeSupport E, p := by
  intro e he
  exact semiprime_dvd_edgePrimeSupport_prod he (hsemi e he)

lemma edgePrimeSupport_ctrlEdges_subset_blockSupport (BS : BlockSystem) :
    edgePrimeSupport (ctrlEdges BS) ⊆ blockSupport BS := by
  intro r hr
  rw [mem_edgePrimeSupport] at hr
  obtain ⟨e, he, hr⟩ := hr
  rw [ctrlEdges, Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  have hrprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr
  have hrdvd : r ∣ pq.1 * pq.2 := Nat.dvd_of_mem_primeFactors hr
  obtain ⟨hp1, hp2, _hne⟩ := ctrlPairs_distinct_primes BS hpq
  obtain ⟨hmem1, hmem2⟩ := ctrlPairs_mem_blockSupport BS hpq
  rcases (Nat.Prime.dvd_mul hrprime).mp hrdvd with hdiv | hdiv
  · have hr_eq : r = pq.1 := (Nat.prime_dvd_prime_iff_eq hrprime hp1).mp hdiv
    simpa [hr_eq] using hmem1
  · have hr_eq : r = pq.2 := (Nat.prime_dvd_prime_iff_eq hrprime hp2).mp hdiv
    simpa [hr_eq] using hmem2

def primeSupportPeriod (b : ℕ) (P : Finset ℕ) : ℕ :=
  b * ∏ p ∈ P, p

lemma edge_dvd_primeSupportPeriod_of_mem_support
    {b : ℕ} {P : Finset ℕ} {e : ℕ}
    (hdiv : e ∣ ∏ p ∈ P, p) :
    e ∣ primeSupportPeriod b P := by
  exact hdiv.trans (Nat.dvd_mul_left (∏ p ∈ P, p) b)

lemma semiprime_edge_dvd_primeSupportPeriod
    {b : ℕ} {E : Finset ℕ} {e : ℕ}
    (he : e ∈ E) (hsemi : IsSemiprime e) :
    e ∣ primeSupportPeriod b (edgePrimeSupport E) := by
  exact edge_dvd_primeSupportPeriod_of_mem_support
    (semiprime_dvd_edgePrimeSupport_prod he hsemi)

theorem blockSupport_frequency_fiber_card_le
    (BS : BlockSystem) (L M : ℕ)
    (hL : L = M * ∏ p ∈ blockSupport BS, p) :
    ∀ a : GlobalAssignment BS,
      ((Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)).card ≤ M :=
  mainArc_fiber_card_le BS L M hL

end CircleMethod

end
