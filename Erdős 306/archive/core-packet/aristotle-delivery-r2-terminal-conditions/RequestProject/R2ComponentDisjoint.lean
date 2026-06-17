import RequestProject.R2ForbiddenBaseBudget

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 control/gadget disjointness

This thin leaf proves the prime-factor bookkeeping that the residual mass-batch
budget needs: the control edges and the gadget edges are disjoint, provided
every denominator-side gadget prime `r ∈ R` is prime and lies outside the
dyadic block support.

A control edge is a product `p * q` of two primes in `blockSupport BS`.  A gadget
edge is a product `r * s` with `r ∈ R`.  If `r` is prime and divides `p * q`,
then `r` equals one of the prime factors `p`, `q`, hence `r ∈ blockSupport BS`,
contradicting the assumption that `R` is kept outside the block support.
-/

/-- The support factors of a control edge both lie in `blockSupport BS`. -/
lemma mem_ctrlEdges_support_pair
    {BS : BlockSystem} {e : ℕ} (he : e ∈ ctrlEdges BS) :
    ∃ p ∈ blockSupport BS, ∃ q ∈ blockSupport BS, e = p * q := by
  rw [ctrlEdges, Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  obtain ⟨hp, hq⟩ := ctrlPairs_mem_blockSupport BS hpq
  exact ⟨pq.1, hp, pq.2, hq, rfl⟩

/-- **Control/gadget disjointness.** If every gadget prime `r ∈ R` is prime and
outside the block support, then no control edge equals a gadget edge. -/
theorem ctrlEdges_disjoint_gadgetEdges_of_R_outside_blockSupport
    {BS : BlockSystem} {R S : Finset ℕ}
    (hRprime : ∀ r ∈ R, Nat.Prime r)
    (hRout : ∀ r ∈ R, r ∉ blockSupport BS) :
    Disjoint (ctrlEdges BS) (gadgetEdges R S) := by
  rw [Finset.disjoint_left]
  intro e hectrl hegadget
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_ctrlEdges_support_pair hectrl
  rw [mem_gadgetEdges] at hegadget
  obtain ⟨r, hr, s, hs, hrs⟩ := hegadget
  have hrp : Nat.Prime r := hRprime r hr
  have hpp : Nat.Prime p := blockSupport_prime BS hp
  have hqp : Nat.Prime q := blockSupport_prime BS hq
  have hdvd : r ∣ p * q := by
    rw [hrs]
    exact dvd_mul_right r s
  rcases (Nat.Prime.dvd_mul hrp).mp hdvd with hrp' | hrq'
  · have : r = p := (Nat.prime_dvd_prime_iff_eq hrp hpp).mp hrp'
    exact hRout r hr (this ▸ hp)
  · have : r = q := (Nat.prime_dvd_prime_iff_eq hrp hqp).mp hrq'
    exact hRout r hr (this ▸ hq)

/-- Record-facing wrapper: the control/gadget components of an `R2ConcreteData`
record are disjoint as soon as its denominator primes are kept outside the block
support. -/
theorem r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS) :
    Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S) :=
  ctrlEdges_disjoint_gadgetEdges_of_R_outside_blockSupport hRprime hRout

end CircleMethod

