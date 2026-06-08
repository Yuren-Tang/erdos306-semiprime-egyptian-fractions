/-
# PotentialTree.lean

Formalizes the abstract finite-tree bookkeeping behind the ambient-sensitive FIE recursion.

## Main results

- `BinTree.telescope` : If every internal node satisfies the local potential inequality
    cost v + potential(left v) + potential(right v) ≤ potential v,
  then totalInternalCost + totalLeafPotential ≤ rootPotential.

- `BinTree.telescope_weighted` : Weighted version with an additional "saving" term.
-/
import Mathlib

namespace PotentialTree

/-- A simple finite binary tree. Each node (leaf or internal) carries a label of type `α`. -/
inductive BinTree (α : Type*) where
  | leaf : α → BinTree α
  | node : α → BinTree α → BinTree α → BinTree α

namespace BinTree

variable {α : Type*}

/-- The label at the root of a tree. -/
def root : BinTree α → α
  | leaf a => a
  | node a _ _ => a

/-- An internal node predicate: `(a, l, r)` is an internal node of `t`. -/
inductive IsInternalOf : α → BinTree α → BinTree α → BinTree α → Prop where
  | root : IsInternalOf a l r (node a l r)
  | left {a l r a' l' r'} : IsInternalOf a l r l' → IsInternalOf a l r (node a' l' r')
  | right {a l r a' l' r'} : IsInternalOf a l r r' → IsInternalOf a l r (node a' l' r')

/-! ## Potential and cost functions on trees -/

/-- Total potential at the leaves of a tree. -/
def totalLeafPotential (P : α → ℝ) : BinTree α → ℝ
  | leaf a => P a
  | node _ l r => l.totalLeafPotential P + r.totalLeafPotential P

/-- Total cost at the internal nodes of a tree. -/
def totalInternalCost (C : α → ℝ) : BinTree α → ℝ
  | leaf _ => 0
  | node a l r => C a + l.totalInternalCost C + r.totalInternalCost C

/-
**Telescope theorem.**  If every internal node `v` with children `l`, `r` satisfies

  C(v) + P(root l) + P(root r) ≤ P(v)

then

  totalInternalCost C t + totalLeafPotential P t ≤ P(root t).
-/
theorem telescope (P : α → ℝ) (C : α → ℝ) (t : BinTree α)
    (hlocal : ∀ (a : α) (l r : BinTree α),
      IsInternalOf a l r t →
      C a + P (root l) + P (root r) ≤ P a) :
    totalInternalCost C t + totalLeafPotential P t ≤ P (root t) := by
  revert hlocal;
  induction' t with a l r ihl ihr <;> simp_all +decide [ totalInternalCost, totalLeafPotential ];
  · exact fun _ => le_rfl;
  · intro h;
    -- Apply the induction hypothesis to the left and right subtrees.
    have h_ind_l : totalInternalCost C r + totalLeafPotential P r ≤ P r.root := by
      apply ihr;
      exact fun a l r hr => h a l r ( IsInternalOf.left hr )
    have h_ind_r : totalInternalCost C ihl + totalLeafPotential P ihl ≤ P ihl.root := by
      apply_assumption;
      exact fun a l r hr => h a l r ( IsInternalOf.right hr );
    linarith! [ h l r ihl ( IsInternalOf.root ) ]

/-! ## Weighted version with a "saving" term -/

/-- Total saving at the internal nodes of a tree. -/
def totalInternalSaving (S : α → ℝ) : BinTree α → ℝ
  | leaf _ => 0
  | node a l r => S a + l.totalInternalSaving S + r.totalInternalSaving S

/-
**Weighted telescope theorem.** If every internal node `v` with children `l`, `r` satisfies

  C(v) + S(v) + P(root l) + P(root r) ≤ P(v)

then

  totalInternalCost C t + totalInternalSaving S t + totalLeafPotential P t ≤ P(root t).
-/
theorem telescope_weighted (P : α → ℝ) (C : α → ℝ) (S : α → ℝ) (t : BinTree α)
    (hlocal : ∀ (a : α) (l r : BinTree α),
      IsInternalOf a l r t →
      C a + S a + P (root l) + P (root r) ≤ P a) :
    totalInternalCost C t + totalInternalSaving S t + totalLeafPotential P t
      ≤ P (root t) := by
  induction' t with a l r ihl ihr;
  · simp +decide [ totalInternalCost, totalInternalSaving, totalLeafPotential ];
    rfl;
  · simp +decide [ *, totalInternalCost, totalInternalSaving, totalLeafPotential ];
    linarith! [ hlocal l r ihl IsInternalOf.root, ihr fun a l r h => hlocal a l r ( IsInternalOf.left h ), ‹ ( ∀ a l r, IsInternalOf a l r ihl → C a + S a + P l.root + P r.root ≤ P a ) → totalInternalCost C ihl + totalInternalSaving S ihl + totalLeafPotential P ihl ≤ P ihl.root › fun a l r h => hlocal a l r ( IsInternalOf.right h ) ]

end BinTree

end PotentialTree