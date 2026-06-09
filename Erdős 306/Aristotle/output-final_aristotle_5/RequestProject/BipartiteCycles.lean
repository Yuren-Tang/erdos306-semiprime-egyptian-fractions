import Mathlib

/-!
# Bipartite double-counting and cycle lower bounds

We work with finite types `A`, `B` equipped with `DecidableEq`, and a bipartite
adjacency relation `Adj : A → B → Prop` with `[DecidableRel Adj]`.

For finite sets `X : Finset A` and `Y : Finset B` we define:

* `degreeRight Adj X y` — the number of vertices in `X` adjacent to `y`.
* `commonNeighboursRight Adj Y x x'` — the number of vertices in `Y` adjacent to both `x` and `x'`.

We prove an ordered double-counting identity and a lower bound.
-/

open Finset

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
  (Adj : A → B → Prop) [DecidableRel Adj]

noncomputable section

/-- Number of vertices in `X` adjacent to `y`. -/
def degreeRight (X : Finset A) (y : B) : ℕ :=
  (X.filter (fun x => Adj x y)).card

/-- Number of vertices in `Y` adjacent to both `x` and `x'`. -/
def commonNeighboursRight (Y : Finset B) (x x' : A) : ℕ :=
  (Y.filter (fun y => Adj x y ∧ Adj x' y)).card

end

section DoubleCounting

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
  (Adj : A → B → Prop) [DecidableRel Adj]

/-
Ordered double-counting identity:
  `∑ y ∈ Y, d(y) * (d(y) - 1) = ∑ x ∈ X, ∑ x' ∈ X \ {x}, cn(x, x')`

where `d(y) = degreeRight Adj X y` and `cn(x,x') = commonNeighboursRight Adj Y x x'`.

Both sides count ordered pairs `(x, x')` of distinct elements of `X` that share a
common neighbour in `Y`.
-/
theorem ordered_double_counting (X : Finset A) (Y : Finset B) :
    ∑ y ∈ Y, (degreeRight Adj X y) * (degreeRight Adj X y - 1) =
    ∑ x ∈ X, ∑ x' ∈ X.filter (fun x' => x' ≠ x),
      commonNeighboursRight Adj Y x x' := by
  simp +decide [ degreeRight, commonNeighboursRight ];
  simp +decide only [card_filter];
  simp +decide only [Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx;
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro y hy; split_ifs <;> simp_all +decide [ Finset.filter_ne', Finset.filter_and ] ;
  rw [ Finset.filter_erase ] ; aesop

/-
Lower bound: if every `y ∈ Y` has degree at least `h`, then the common-neighbour
mass is at least `Y.card * (h * (h - 1))`.
-/
theorem common_neighbour_mass_lower_bound (X : Finset A) (Y : Finset B) (h : ℕ)
    (hmin : ∀ y ∈ Y, h ≤ degreeRight Adj X y) :
    Y.card * (h * (h - 1)) ≤
    ∑ x ∈ X, ∑ x' ∈ X.filter (fun x' => x' ≠ x),
      commonNeighboursRight Adj Y x x' := by
  rw [ ← ordered_double_counting ];
  exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun y hy => Nat.mul_le_mul ( hmin y hy ) ( Nat.sub_le_sub_right ( hmin y hy ) 1 ) )

/-- Rectangle count: number of ordered 4-cycles. -/
def rectangleCount (X : Finset A) (Y : Finset B) : ℕ :=
  ∑ x ∈ X, ∑ x' ∈ X.filter (fun x' => x' ≠ x),
    Nat.choose (commonNeighboursRight Adj Y x x') 2

end DoubleCounting