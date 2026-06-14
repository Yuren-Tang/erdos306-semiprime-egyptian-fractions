import RequestProject.BlockSystemConstruction

open Finset BigOperators

noncomputable section

namespace CircleMethod

/-!
# R2-mass: the block-prime product-load lower bound

The block-aligned mass batch draws from products `p·q` of two distinct block
primes.  Its available reciprocal load is `∑_{p<q} 1/(pq) = (S² − S₂)/2` where
`S = ∑ 1/p`, `S₂ = ∑ 1/p²`.  This file proves the algebraic identity (general)
and will assemble the numeric lower bound `≥ 1/2` from `dyadic_mertens_cumulative`
(`S ≥ 21/20`) plus a tail bound `S₂ ≤ 1/(2^{k₀}−1)`.
-/

/-- **The pair-sum identity.**  `(∑ x)² = ∑ x² + 2·∑_{p<q} xₚxq`.  Pure algebra,
via the diagonal/off-diagonal split of `s ×ˢ s` and the `Prod.swap` symmetry of the
off-diagonal. -/
lemma sq_sum_eq_sum_sq_add_two_sum_lt {α : Type*} [LinearOrder α]
    (s : Finset α) (x : α → ℝ) :
    (∑ p ∈ s, x p) ^ 2
      = (∑ p ∈ s, (x p) ^ 2)
        + 2 * ∑ pq ∈ s.offDiag.filter (fun pq => pq.1 < pq.2), x pq.1 * x pq.2 := by
  classical
  have hexp : (∑ p ∈ s, x p) ^ 2 = ∑ pq ∈ s ×ˢ s, x pq.1 * x pq.2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  rw [hexp, ← Finset.diag_union_offDiag s,
      Finset.sum_union (Finset.disjoint_diag_offDiag s), Finset.sum_diag]
  have hdiag : ∑ p ∈ s, x p * x p = ∑ p ∈ s, (x p) ^ 2 :=
    Finset.sum_congr rfl (fun p _ => by rw [sq])
  rw [hdiag]
  congr 1
  -- remaining: ∑_{offDiag} x.1*x.2 = 2 * ∑_{offDiag, p<q} x.1*x.2
  have hsplit := Finset.sum_filter_add_sum_filter_not s.offDiag
    (fun pq => pq.1 < pq.2) (fun pq => x pq.1 * x pq.2)
  have hswap :
      ∑ pq ∈ s.offDiag.filter (fun pq => ¬ pq.1 < pq.2), x pq.1 * x pq.2
        = ∑ pq ∈ s.offDiag.filter (fun pq => pq.1 < pq.2), x pq.1 * x pq.2 := by
    refine Finset.sum_nbij' (fun pq => Prod.swap pq) (fun pq => Prod.swap pq) ?_ ?_ ?_ ?_ ?_
    · intro pq hpq
      rw [Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
      obtain ⟨⟨h1, h2, hne⟩, hnlt⟩ := hpq
      refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hnlt) hne.symm
    · intro pq hpq
      rw [Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
      obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := hpq
      refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact not_lt.mpr (le_of_lt hlt)
    · intro pq _; simp
    · intro pq _; simp
    · intro pq _; simp only [Prod.fst_swap, Prod.snd_swap]; ring
  rw [← hsplit, hswap]; ring

end CircleMethod

end
