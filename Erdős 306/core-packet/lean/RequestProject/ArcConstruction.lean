import RequestProject.CircleMethodArcs
import RequestProject.BlockSystemConstruction

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2: edge construction foundation

Control edges `ctrlEdges BS = {p·q : (p,q) ∈ ctrlPairs BS}` (squarefree semiprimes),
and the key minor-arc input `QE_ge_Qctrl`: any edge set containing the control edges
has `QE E h ≥ Qctrl BS (a(h))` (the `hQE` hypothesis of `minor_arc_bound`), via the
verified `Qctrl_freq_eq`.
-/

/-- The control edges: products `p·q` of the control pairs. -/
def ctrlEdges (BS : BlockSystem) : Finset ℕ :=
  (ctrlPairs BS).image (fun pq => pq.1 * pq.2)

/-- Control pairs are strictly ordered (`pq.1 < pq.2`). -/
lemma ctrlPairs_lt (BS : BlockSystem) {pq : ℕ × ℕ} (hpq : pq ∈ ctrlPairs BS) :
    pq.1 < pq.2 := by
  simp only [ctrlPairs, Finset.mem_union, Finset.mem_biUnion, internalPairs,
    bipartitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Ico] at hpq
  rcases hpq with ⟨k, _, ⟨_, _⟩, hlt⟩ | ⟨k, _, hp1, hp2⟩
  · exact hlt
  · exact lt_of_lt_of_le (BS.hwindow k pq.1 hp1).2 (BS.hwindow (k + 1) pq.2 hp2).1

/-- Each control edge is a squarefree semiprime. -/
lemma ctrlEdges_semiprime (BS : BlockSystem) {e : ℕ} (he : e ∈ ctrlEdges BS) :
    IsSemiprime e := by
  rw [ctrlEdges, Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  obtain ⟨hp1, hp2, _⟩ := ctrlPairs_distinct_primes BS hpq
  exact ⟨pq.1, pq.2, hp1, hp2, ctrlPairs_lt BS hpq, rfl⟩

/-- The product map `(p,q) ↦ p·q` is injective on control pairs (unique factorization
of a semiprime into its two ordered prime factors). -/
lemma ctrlPairs_prod_injOn (BS : BlockSystem) :
    Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) (ctrlPairs BS) := by
  intro a ha b hb hab
  simp only at hab
  obtain ⟨ha1, ha2, _⟩ := ctrlPairs_distinct_primes BS ha
  obtain ⟨hb1, hb2, _⟩ := ctrlPairs_distinct_primes BS hb
  have halt := ctrlPairs_lt BS ha
  have hblt := ctrlPairs_lt BS hb
  -- a.1 ∣ b.1 * b.2, a.1 prime ⇒ a.1 = b.1 or a.1 = b.2
  have hdvd : a.1 ∣ b.1 * b.2 := ⟨a.2, by rw [← hab]⟩
  have h1 : a.1 = b.1 := by
    rcases (Nat.Prime.dvd_mul ha1).mp hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq ha1 hb1).mp h
    · -- a.1 = b.2 forces contradiction with orderings
      have heq : a.1 = b.2 := (Nat.prime_dvd_prime_iff_eq ha1 hb2).mp h
      have hb2pos : 0 < b.2 := hb2.pos
      have ha2eq : a.2 = b.1 := by
        have h2 : b.2 * a.2 = b.2 * b.1 := by
          calc b.2 * a.2 = a.1 * a.2 := by rw [heq]
            _ = b.1 * b.2 := hab
            _ = b.2 * b.1 := by ring
        exact Nat.eq_of_mul_eq_mul_left hb2pos h2
      omega
  have h2 : a.2 = b.2 := by
    have ha1pos : 0 < a.1 := ha1.pos
    rw [h1] at hab
    exact Nat.eq_of_mul_eq_mul_left (h1 ▸ ha1pos) hab
  exact Prod.ext h1 h2

/-- **`hQE` (the minor-arc energy input).**  If `E` contains all control edges, then
the CRT energy `Qctrl BS (a(h))` is dominated by `QE E h` — exactly the hypothesis
`minor_arc_bound` needs.  Proved from the verified `Qctrl_freq_eq`. -/
lemma QE_ge_Qctrl (BS : BlockSystem) (E : Finset ℕ) (hsub : ctrlEdges BS ⊆ E) (h : ℕ) :
    Qctrl BS (fun p => ((h : ZMod p.1))) ≤ QE E h := by
  rw [Qctrl_freq_eq]
  calc ∑ pq ∈ ctrlPairs BS,
          (GlobalControl.nndist1 ((h : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))) ^ 2
      = ∑ e ∈ ctrlEdges BS, (GlobalControl.nndist1 ((h : ℝ) / (e : ℝ))) ^ 2 := by
        rw [ctrlEdges, Finset.sum_image
          (fun a ha b hb hab => ctrlPairs_prod_injOn BS ha hb hab)]
        refine Finset.sum_congr rfl (fun pq _ => ?_)
        norm_num [Nat.cast_mul]
    _ ≤ QE E h := by
        unfold QE
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by positivity)

end CircleMethod

end
