import Mathlib

/-!
# Pair-disjoint family bound (Fisher counting inequality)

## Statement

If `{Sᵢ}_{i ∈ I}` is a family of subsets of a finite set `U`, and no
ordered pair `(u, v)` with `u ≠ v` appears in two different `Sᵢ`, then

  `∑_{i ∈ I} C(|Sᵢ|, 2) ≤ C(|U|, 2)`

where `C(n, 2) = n(n-1)/2` is the binomial coefficient.

## Mathematical context

**Injection into pairs.**
`C(|Sᵢ|, 2)` counts unordered pairs within `Sᵢ`.  The pair-disjoint
condition guarantees these pair-sets are disjoint across different `i`.
Their union is contained in the set of all unordered pairs from `U`,
which has `C(|U|, 2)` elements.

**Fisher's inequality and combinatorial design theory.**
In the theory of combinatorial designs (block designs), the analogous
principle — that `b ≥ v` for a (v,k,1)-design — is called Fisher's
inequality.  Our theorem is the "pair version": each pair is covered
by at most one block.  The bound `∑ C(|Sᵢ|, 2) ≤ C(|U|, 2)` is the
natural accounting identity for this setting.

**Connection to `marked_dual_large_sieve`.**
The `marked_dual_large_sieve` theorem from `BucketCore.lean` is an
instance of this abstract principle, applied to the family
`Sₚₜ = {n ∈ 𝓑 : MC p t n}` indexed by `(p, t) ∈ Ps × Ts`.  The
off-diagonal uniqueness hypothesis ensures pair-disjointness.  The
diagonal uniqueness hypothesis (`_hdiag`) was unused in the original
proof; here we make this explicit by deriving the same statement from
the abstract principle, without `_hdiag`.

**The large sieve inequality.**
The classical large sieve inequality in analytic number theory
  `∑_q ∑_{a mod q} |∑_n aₙ e(an/q)|² ≤ (N + Q² - 1) ∑ |aₙ|²`
shares the same underlying counting structure: each "resonance" pair
is counted at most once.  Our discrete version is the finite
combinatorial core of this principle.
-/

open Finset BigOperators

/-! ## Auxiliary: offDiag card equals 2 × choose 2 -/

/-- The number of ordered pairs of distinct elements equals twice the
    number of unordered pairs. -/
lemma offDiag_card_eq_two_mul_choose {α : Type*} (S : Finset α) :
    S.offDiag.card = 2 * Nat.choose S.card 2 := by
  rw [Finset.offDiag_card, Nat.choose_two_right,
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self S.card)]
  exact (Nat.mul_sub_one S.card S.card).symm

/-! ## Main theorem: ordered-pair version -/

section PairDisjoint

variable {ι U : Type*} [DecidableEq U]

/-- **Pair-disjoint family bound (ordered-pair version).**

If `{Sᵢ}` are subsets of `ambient` and no ordered pair `(u, v)` with
`u ≠ v` appears in two different `Sᵢ`, then
`∑ |offDiag(Sᵢ)| ≤ |offDiag(ambient)|`.

This is the raw counting version; the choose-2 version follows by
dividing both sides by 2. -/
theorem pair_disjoint_offDiag_bound
    (I : Finset ι) (ambient : Finset U)
    (family : ι → Finset U)
    (hSub : ∀ i ∈ I, family i ⊆ ambient)
    (hPairUnique : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ u v, u ∈ family i → v ∈ family i →
             u ∈ family j → v ∈ family j → u = v) :
    ∑ i ∈ I, (family i).offDiag.card ≤ ambient.offDiag.card := by
  have hDisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (family i).offDiag (family j).offDiag := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro ⟨u, v⟩ huv_i huv_j
    simp [Finset.mem_offDiag] at huv_i huv_j
    exact huv_i.2.2 (hPairUnique i hi j hj hij u v
      huv_i.1 huv_i.2.1 huv_j.1 huv_j.2.1)
  calc ∑ i ∈ I, (family i).offDiag.card
      = (I.biUnion fun i => (family i).offDiag).card :=
        (Finset.card_biUnion
          (fun i hi j hj hij => hDisj i hi j hj hij)).symm
    _ ≤ ambient.offDiag.card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr
          fun i hi => Finset.offDiag_mono (hSub i hi))

/-- **Pair-disjoint family bound (choose-2 version, the Fisher inequality).**

If `{Sᵢ}` are subsets of `ambient` and no ordered pair `(u, v)` with
`u ≠ v` appears in two different families, then
`∑ C(|Sᵢ|, 2) ≤ C(|ambient|, 2)`.

This is the clean form of the Fisher counting principle: each unordered
pair is witnessed by at most one family member. -/
theorem pair_disjoint_choose_bound
    (I : Finset ι) (ambient : Finset U)
    (family : ι → Finset U)
    (hSub : ∀ i ∈ I, family i ⊆ ambient)
    (hPairUnique : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ∀ u v, u ∈ family i → v ∈ family i →
             u ∈ family j → v ∈ family j → u = v) :
    ∑ i ∈ I, Nat.choose (family i).card 2 ≤
      Nat.choose ambient.card 2 := by
  have h := pair_disjoint_offDiag_bound I ambient family hSub hPairUnique
  simp_rw [offDiag_card_eq_two_mul_choose] at h
  rw [← Finset.mul_sum] at h
  exact Nat.le_of_mul_le_mul_left h (by norm_num)

end PairDisjoint

/-! ## Derivation of marked_dual_large_sieve

The `marked_dual_large_sieve` from `BucketCore.lean` is an instance of
`pair_disjoint_choose_bound`, applied to the family indexed by `Ps × Ts`:

  `family (p, t) := 𝓑.filter (fun n => MC p t n)`

The off-diagonal uniqueness hypothesis ensures pair-disjointness.  The
diagonal uniqueness hypothesis (`_hdiag`) is **not needed** — it was
already unused (with underscore prefix) in the original proof.  Here we
make this structurally visible by deriving the same statement without it.
-/

section LargeSieve

variable {P T B : Type*}

/-- **Marked dual large sieve, derived from Fisher counting.**

This is the same statement as `marked_dual_large_sieve` from `BucketCore`,
but without the unused diagonal uniqueness hypothesis `_hdiag`, and with
a structurally cleaner proof via the abstract `pair_disjoint_choose_bound`.

Under off-diagonal uniqueness alone (for distinct `n₁, n₂ ∈ 𝓑`, at most
one `(p,t)` satisfies `MC p t n₁ ∧ MC p t n₂`), we have:
  `∑_{p ∈ Ps} ∑_{t ∈ Ts} C(d(p,t), 2) ≤ C(|𝓑|, 2)`. -/
theorem marked_dual_large_sieve_from_fisher
    (MC : P → T → B → Prop)
    [DecidableEq B] [∀ p t, DecidablePred (MC p t)]
    (Ps : Finset P) (Ts : Finset T) (𝓑 : Finset B)
    (hoffdiag : ∀ n₁ ∈ 𝓑, ∀ n₂ ∈ 𝓑, n₁ ≠ n₂ →
      ∀ p₁ ∈ Ps, ∀ t₁ ∈ Ts, ∀ p₂ ∈ Ps, ∀ t₂ ∈ Ts,
      MC p₁ t₁ n₁ → MC p₁ t₁ n₂ →
      MC p₂ t₂ n₁ → MC p₂ t₂ n₂ →
      (p₁, t₁) = (p₂, t₂)) :
    ∑ p ∈ Ps, ∑ t ∈ Ts, Nat.choose (𝓑.filter (MC p t ·)).card 2
      ≤ Nat.choose 𝓑.card 2 := by
  rw [← Finset.sum_product']
  apply pair_disjoint_choose_bound (Ps ×ˢ Ts) 𝓑
    (fun pt => 𝓑.filter (MC pt.1 pt.2 ·))
  · intro ⟨_, _⟩ _; exact Finset.filter_subset _ _
  · intro ⟨p₁, t₁⟩ h₁ ⟨p₂, t₂⟩ h₂ hne n₁ n₂ hn₁ hn₂ hm₁ hm₂
    simp only [Finset.mem_filter] at hn₁ hn₂ hm₁ hm₂
    by_contra hne'
    exact hne (hoffdiag n₁ hn₁.1 n₂ hn₂.1 hne'
      p₁ (Finset.mem_product.mp h₁).1 t₁ (Finset.mem_product.mp h₁).2
      p₂ (Finset.mem_product.mp h₂).1 t₂ (Finset.mem_product.mp h₂).2
      hn₁.2 hn₂.2 hm₁.2 hm₂.2)

end LargeSieve

/-! ## Structural insight

The proof of `pair_disjoint_choose_bound` reduces to three steps:

1. The offDiag sets are pairwise disjoint (from pair-uniqueness).
2. `card(⋃ offDiag(Sᵢ)) = ∑ card(offDiag(Sᵢ))` (by disjointness)
   and `⋃ offDiag(Sᵢ) ⊆ offDiag(ambient)` (by subset hypothesis).
3. Convert from offDiag count to choose-2 by dividing by 2.

This reveals that `marked_dual_large_sieve` is not really about
Kloosterman sums, CRT residues, or modular arithmetic — it is a
purely combinatorial injection-into-pairs principle.  The specific
structure of `MC p t n` (marked congruence) enters only through the
pair-uniqueness hypothesis; the bound itself is universal.

The diagonal uniqueness hypothesis `_hdiag` was always redundant
for this bound.  It may be needed for other parts of the argument
(e.g., controlling the diagonal contribution to the quadratic energy),
but for the pure pair-counting inequality, off-diagonal uniqueness
alone suffices.
-/
