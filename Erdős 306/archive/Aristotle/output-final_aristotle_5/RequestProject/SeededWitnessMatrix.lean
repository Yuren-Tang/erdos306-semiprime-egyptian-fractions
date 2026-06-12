import Mathlib
import RequestProject.TwoCoreBookkeeping
import RequestProject.GeneralizedRankOne
import RequestProject.RankOneRigidity

/-!
# Seeded Witness Matrix: Finite bookkeeping for the ambient-sensitive FIE route

This file formalizes the finite bookkeeping shell for the seeded witness-matrix
inverse inside the ambient-sensitive FIE route for the Erdős 306 conditional proof.

## TwoCoreBookkeeping results (imported, not reproved)

From `TwoCoreBookkeeping.lean` we have:

* `newBucket_capacity_mul_le` — one-core new-bucket capacity bound
* `twoCore_edges_lower_mul` — two-core edge lower bound
* `highDeg_generatedCore_le_seedNeighbours` — generated core gives many seed neighbours

## Contents

* **Goal 1** (`exists_twoSided_commonResidual_large`): Two-sided dependent-random-choice
  averaging.  Given minimum degrees h₀, h₁ into seed sets F₀, F₁, there exist seed
  tuples whose common residual neighbourhood is at least the average.

* **Goal 2** (`zero_mixedDefect_iff_rankOne`): Bridge between vanishing mixed defect
  and additive rank-one decomposition, wrapping `mixedSecondZero_iff`.

* **Goal 3** (`zeroRectangleDefect_iff_additiveRankOne`): Paper-language aliases.

* **Goal 4** (`mixedDefect_eq_rowDiff_sub`, `DividesAllRowDiffs`,
  `DividesAllRowDiffs.mono`): Row-difference and common-divisor shell.

No SBEE, Fourier positivity, or analytic number theory is used.
-/

open Finset BigOperators

-- Verify imports
#check newBucket_capacity_mul_le
#check twoCore_edges_lower_mul
#check highDeg_generatedCore_le_seedNeighbours

/-! ## Goal 1: Two-sided dependent-random-choice averaging -/

section DRC

variable {V S₀ S₁ : Type*} [DecidableEq V] [DecidableEq S₀] [DecidableEq S₁]

/-- Common residual neighbourhood: vertices in Γ adjacent to every seed in both tuples. -/
def commonResidual
    (Γ : Finset V) (Adj₀ : V → S₀ → Prop) [DecidableRel Adj₀]
    (Adj₁ : V → S₁ → Prop) [DecidableRel Adj₁]
    {r : ℕ} (s₀ : Fin r → S₀) (s₁ : Fin r → S₁) : Finset V :=
  Γ.filter (fun v => (∀ i, Adj₀ v (s₀ i)) ∧ (∀ i, Adj₁ v (s₁ i)))

/-
Averaging lemma: if `N ≤ ∑_{x ∈ S} f(x)` and `S` is nonempty,
then some element achieves at least the average (division-free form).
-/
private lemma exists_le_mul_card_of_le_sum
    {ι : Type*} (S : Finset ι) (f : ι → ℕ) (N : ℕ)
    (hne : S.Nonempty) (h : N ≤ S.sum f) :
    ∃ x ∈ S, N ≤ f x * S.card := by
  contrapose! h
  have := Finset.sum_lt_sum_of_nonempty hne h
  simp_all +decide [mul_comm]
  rw [← Finset.sum_mul _ _ _] at this
  nlinarith [Finset.card_pos.2 hne]

/-
Filtering a constant `piFinset` by a pointwise predicate equals the `piFinset`
of the filtered base set.
-/
private lemma piFinset_filter_forall
    {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Finset α) (P : α → Prop) [DecidablePred P] :
    (Fintype.piFinset (fun _ : Fin n => F)).filter (fun s => ∀ i, P (s i)) =
    Fintype.piFinset (fun _ : Fin n => F.filter P) := by
  aesop

/-
Double-counting identity: summing `|commonResidual|` over all seed-tuple pairs
equals summing per-vertex seed-tuple counts over Γ.

Here the per-vertex count for `v` is the number of seed-tuple pairs `(s₀, s₁)`
such that `v` is adjacent to every seed.
-/
private lemma sum_commonResidual_card
    {V S₀ S₁ : Type*} [DecidableEq V] [DecidableEq S₀] [DecidableEq S₁]
    (Γ : Finset V) (F₀ : Finset S₀) (F₁ : Finset S₁)
    (Adj₀ : V → S₀ → Prop) [DecidableRel Adj₀]
    (Adj₁ : V → S₁ → Prop) [DecidableRel Adj₁]
    {r : ℕ} :
    ∑ p ∈ (Fintype.piFinset (fun _ : Fin r => F₀)) ×ˢ
           (Fintype.piFinset (fun _ : Fin r => F₁)),
      (commonResidual Γ Adj₀ Adj₁ p.1 p.2).card =
    ∑ v ∈ Γ,
      ((Fintype.piFinset (fun _ : Fin r => F₀)).filter (fun s => ∀ i, Adj₀ v (s i))).card *
      ((Fintype.piFinset (fun _ : Fin r => F₁)).filter (fun s => ∀ i, Adj₁ v (s i))).card := by
  simp +decide only [commonResidual, card_filter];
  rw [ Finset.sum_comm ];
  simp +decide only [sum_product, sum_mul_sum, mul_boole];
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by split_ifs <;> tauto;

/-
Per-vertex lower bound: for `v ∈ Γ` with minimum degrees `h₀`, `h₁`,
the number of valid seed-tuple pairs is at least `h₀^r * h₁^r`.
-/
private lemma per_vertex_tuples_lower
    {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Finset α) (P : α → Prop) [DecidablePred P]
    (h : ℕ) (hdeg : h ≤ (F.filter P).card) :
    h ^ n ≤ ((Fintype.piFinset (fun _ : Fin n => F)).filter (fun s => ∀ i, P (s i))).card := by
  have h_card_filter : (Fintype.piFinset (fun _ : Fin n => F.filter P)).card ≥ h^n := by
    simpa using Nat.pow_le_pow_left hdeg n;
  convert h_card_filter.le using 1;
  convert congr_arg Finset.card ( piFinset_filter_forall F P ) using 2

/-
**Two-sided dependent-random-choice averaging.**

Given a residual set Γ where every vertex has degree ≥ h₀ into F₀ and ≥ h₁ into F₁,
there exist seed tuples `(s₀, s₁)` whose common residual neighbourhood satisfies
the division-free averaging bound.

Mathematical proof: Count triples (v, s₀, s₁) where v ∈ Γ is adjacent to every
seed. Counting by v gives ≥ |Γ|·h₀ʳ·h₁ʳ. Counting by seed tuples gives
∑ |commonResidual(s₀,s₁)|. By averaging, some tuple achieves ≥ average.
-/
theorem exists_twoSided_commonResidual_large
    [Nonempty S₀] [Nonempty S₁]
    (Γ : Finset V) (F₀ : Finset S₀) (F₁ : Finset S₁)
    (Adj₀ : V → S₀ → Prop) [DecidableRel Adj₀]
    (Adj₁ : V → S₁ → Prop) [DecidableRel Adj₁]
    {r : ℕ} (h₀ h₁ : ℕ)
    (hdeg₀ : ∀ v ∈ Γ, h₀ ≤ (F₀.filter (fun f => Adj₀ v f)).card)
    (hdeg₁ : ∀ v ∈ Γ, h₁ ≤ (F₁.filter (fun f => Adj₁ v f)).card) :
    ∃ (s₀ : Fin r → S₀) (s₁ : Fin r → S₁),
      Γ.card * h₀ ^ r * h₁ ^ r ≤
        (commonResidual Γ Adj₀ Adj₁ s₀ s₁).card * F₀.card ^ r * F₁.card ^ r := by
  by_contra h;
  have h_card : ∑ p ∈ (Fintype.piFinset (fun _ : Fin r => F₀)) ×ˢ (Fintype.piFinset (fun _ : Fin r => F₁)), (commonResidual Γ Adj₀ Adj₁ p.1 p.2).card ≥ Γ.card * h₀ ^ r * h₁ ^ r := by
    rw [ sum_commonResidual_card ];
    refine' le_trans _ ( Finset.sum_le_sum fun v hv => Nat.mul_le_mul ( per_vertex_tuples_lower F₀ _ _ ( hdeg₀ v hv ) ) ( per_vertex_tuples_lower F₁ _ _ ( hdeg₁ v hv ) ) ) ; simp +decide [ mul_assoc ];
  have := exists_le_mul_card_of_le_sum ( ( Fintype.piFinset fun _ : Fin r => F₀ ) ×ˢ Fintype.piFinset fun _ : Fin r => F₁ ) ( fun p => # ( commonResidual Γ Adj₀ Adj₁ p.1 p.2 ) ) ( #Γ * h₀ ^ r * h₁ ^ r ) ?_ h_card;
  · simp_all +decide [ mul_assoc ];
    exact not_lt_of_ge this.choose_spec.choose_spec.2 ( h _ _ );
  · simp +zetaDelta at *;
    constructor <;> intro i <;> contrapose! h <;> simp_all +decide [ commonResidual ];
    · cases r <;> aesop;
    · cases r <;> simp_all +decide

end DRC

/-! ## Goal 2: Witness matrix mixed defect -/

section MixedDefect

variable {R C G : Type*} [AddCommGroup G]

/-- Mixed defect of a matrix at a 2×2 sub-configuration. -/
def mixedDefect (N : R → C → G) (r r' : R) (c c' : C) : G :=
  N r c - N r c' - N r' c + N r' c'

/-
Vanishing mixed defect is equivalent to additive rank-one decomposition.
This is a direct wrapper around `mixedSecondZero_iff` from `GeneralizedRankOne.lean`.
-/
theorem zero_mixedDefect_iff_rankOne
    [Nonempty R] [Nonempty C]
    (N : R → C → G) :
    (∀ r r' c c', mixedDefect N r r' c c' = 0) ↔
    ∃ (a : R → G) (b : C → G), ∀ r c, N r c = a r + b c := by
  convert mixedSecondZero_iff N

end MixedDefect

/-! ## Goal 3: Paper-language aliases -/

section PaperAliases

variable {R C G : Type*} [AddCommGroup G]

/-- A witness matrix is simply a function `R → C → G`. -/
def WitnessMatrix (R C G : Type*) := R → C → G

/-- Zero rectangle defect: all 2×2 mixed defects vanish. -/
def ZeroRectangleDefect (N : R → C → G) : Prop :=
  ∀ r r' c c', mixedDefect N r r' c c' = 0

/-- Additive rank one: the matrix decomposes as `a r + b c`. -/
def AdditiveRankOne (N : R → C → G) : Prop :=
  ∃ (a : R → G) (b : C → G), ∀ r c, N r c = a r + b c

/-
**Paper-language bridge:** zero rectangle defect ↔ additive rank one.
-/
theorem zeroRectangleDefect_iff_additiveRankOne
    [Nonempty R] [Nonempty C]
    (N : R → C → G) :
    ZeroRectangleDefect N ↔ AdditiveRankOne N := by
  convert zero_mixedDefect_iff_rankOne N

end PaperAliases

/-! ## Goal 4: Row-difference and common-divisor shell -/

section RowDiff

variable {R C : Type*}

/-- Row difference relative to a reference column. -/
def rowDiff (N : R → C → ℤ) (c₀ : C) (r : R) (c : C) : ℤ :=
  N r c - N r c₀

/-
The mixed defect equals the difference of row differences.
-/
theorem mixedDefect_eq_rowDiff_sub
    (N : R → C → ℤ) (c₀ : C) (r r' : R) (c : C) :
    mixedDefect N r r' c c₀ = rowDiff N c₀ r c - rowDiff N c₀ r' c := by
  unfold rowDiff mixedDefect; ring;

/-- Predicate: integer `p` divides all row differences of row `r` across columns in `Cols`. -/
def DividesAllRowDiffs
    (N : R → C → ℤ) (Cols : Finset C) (c₀ : C) (r : R) (p : ℤ) : Prop :=
  ∀ c ∈ Cols, p ∣ rowDiff N c₀ r c

/-
`DividesAllRowDiffs` is preserved under taking subsets of columns.
-/
theorem DividesAllRowDiffs.mono
    [DecidableEq C]
    {N : R → C → ℤ} {Cols Cols' : Finset C} {c₀ : C} {r : R} {p : ℤ}
    (h : DividesAllRowDiffs N Cols c₀ r p) (hsub : Cols' ⊆ Cols) :
    DividesAllRowDiffs N Cols' c₀ r p := by
  exact fun c hc => h c ( hsub hc )

end RowDiff