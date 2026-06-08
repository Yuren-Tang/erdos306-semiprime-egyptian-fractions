import Mathlib

/-!
# Rank-one rigidity over arbitrary abelian groups

## Statement

If every mixed second difference of `a : X → Y → G` vanishes (where `G` is
any additive abelian group), then `a` decomposes as `α x + β y`.  The converse
also holds.

## Generalization from ℤ

The original `RankOneRigidity.lean` proves this for `G = ℤ`.  Here we prove
it for any `AddCommGroup G`.  Since `ℤ`, `ℚ`, `ℝ`, `ℂ`, `ZMod n`, and every
module are additive abelian groups, this single theorem covers all of them.
The generalization is costless: the proof structure is the same, using
`module` in place of `ring` for the group-arithmetic steps.

## Mathematical context

**Discrete PDE characterization.**
The condition  `a(x,y) - a(x,y') - a(x',y) + a(x',y') = 0`  is the discrete
analogue of the mixed partial derivative equation  `∂²f / ∂x ∂y = 0`,  whose
classical solutions are exactly the additively separable functions
`f(x,y) = g(x) + h(y)`.  Our theorem is the exact discrete version of this
classical PDE fact, valid over any abelian group.

**Additive rank one.**
Viewing `a` as a matrix (indexed by `X × Y`), the vanishing of all 2×2
"additive minors"  `a(x,y) - a(x,y') - a(x',y) + a(x',y')`  characterizes
functions of additive rank at most 1.  Over a field, the multiplicative
analogue `a(x,y)·a(x',y') = a(x,y')·a(x',y)` characterizes multiplicative
rank 1.  The additive version is more natural for group-valued functions
and is the one relevant to the SBEE bucket-container argument.

**Universality.**
No finiteness, decidable equality, or cardinality conditions on `X`, `Y`,
or `G` are needed.  The theorem works for any types whatsoever.
-/

variable {X Y : Type*}

section General

variable {G : Type*} [AddCommGroup G]

/-- Vanishing of all mixed second differences, over any additive abelian group.

This is the discrete analogue of `∂²f/∂x∂y = 0`. -/
def mixedSecondZero (a : X → Y → G) : Prop :=
  ∀ x x' y y', a x y - a x y' - a x' y + a x' y' = 0

/-- **Rank-one decomposition (forward direction), generalized to AddCommGroup.**

If all mixed second differences of `a : X → Y → G` vanish, then `a` decomposes
as `α x + β y` with `α x = a x y₀` and `β y = a x₀ y - a x₀ y₀`.

This is the discrete analogue of: `∂²f/∂x∂y = 0  ⟹  f(x,y) = g(x) + h(y)`. -/
theorem rankOne_decomposition
    (a : X → Y → G) (x₀ : X) (y₀ : Y)
    (h : mixedSecondZero a) :
    let alpha : X → G := fun x => a x y₀
    let beta : Y → G := fun y => a x₀ y - a x₀ y₀
    ∀ x y, a x y = alpha x + beta y := by
  intro alpha beta x y
  have h' := h x x₀ y y₀
  have key : a x y - (a x y₀ + (a x₀ y - a x₀ y₀)) =
             a x y - a x y₀ - a x₀ y + a x₀ y₀ := by abel
  exact eq_of_sub_eq_zero (key ▸ h')

/-- **Rank-one decomposition (converse), generalized to AddCommGroup.**

Any function of the form `α x + β y` has vanishing mixed second differences.
This direction holds in any additive abelian group. -/
theorem mixedSecondZero_of_sum
    (alpha : X → G) (beta : Y → G) :
    mixedSecondZero (fun x y => alpha x + beta y) :=
  fun _ _ _ _ => by module

/-- **Rank-one characterization (iff), generalized to AddCommGroup.**

A function `a : X → Y → G` has vanishing mixed second differences if and only
if it decomposes as `α x + β y` for some `α : X → G` and `β : Y → G`.

This is the full discrete PDE characterization: `∂²f/∂x∂y = 0  ↔  f = g + h`. -/
theorem mixedSecondZero_iff [Nonempty X] [Nonempty Y]
    (a : X → Y → G) :
    mixedSecondZero a ↔
    ∃ (alpha : X → G) (beta : Y → G), ∀ x y, a x y = alpha x + beta y := by
  constructor
  · intro h
    exact ⟨fun x => a x (Classical.arbitrary Y),
           fun y => a (Classical.arbitrary X) y -
                     a (Classical.arbitrary X) (Classical.arbitrary Y),
           rankOne_decomposition a _ _ h⟩
  · rintro ⟨alpha, beta, hab⟩
    intro x x' y y'
    simp only [hab]
    module

end General

/-! ## Specialization to ℤ

The original `RankOneRigidity.lean` works over `ℤ`. Since `ℤ` is an
`AddCommGroup`, the general theorems specialize immediately.

The definitions are definitionally equal (both unfold to the same ∀-statement),
so the original ℤ results follow by identity. -/

example (a : X → Y → ℤ) (x₀ : X) (y₀ : Y)
    (h : mixedSecondZero a) :
    ∀ x y, a x y = a x y₀ + (a x₀ y - a x₀ y₀) :=
  rankOne_decomposition a x₀ y₀ h

/-! ## Specialization to ℝ

Over `ℝ`, the theorem says: a real-valued function on a product has vanishing
mixed second differences iff it is additively separable.  This is the exact
discrete counterpart of the classical PDE theorem for `∂²f/∂x∂y = 0`.

In the SBEE argument, this specialization applies to real-valued log-density
functions on products of prime blocks. -/

example (a : X → Y → ℝ) (x₀ : X) (y₀ : Y)
    (h : mixedSecondZero a) :
    ∀ x y, a x y = a x y₀ + (a x₀ y - a x₀ y₀) :=
  rankOne_decomposition a x₀ y₀ h

/-! ## Specialization to ZMod n

Over `ZMod n`, the theorem gives additive structure of functions on products
modulo n — directly relevant to CRT residue analysis in the SBEE argument,
where residue assignments on products of prime blocks are analyzed modulo
various moduli. -/

example (n : ℕ) [NeZero n] (a : X → Y → ZMod n) (x₀ : X) (y₀ : Y)
    (h : mixedSecondZero a) :
    ∀ x y, a x y = a x y₀ + (a x₀ y - a x₀ y₀) :=
  rankOne_decomposition a x₀ y₀ h

/-! ## Connection to the existing project

The `mixed_second_zero` predicate from `RankOneRigidity.lean` and
`mixedSecondZero` here are definitionally equal when `G = ℤ`:

  `mixed_second_zero a  ↔  mixedSecondZero a`  (by `rfl`)

The `iff` version `mixedSecondZero_iff` is new: it packages both
directions into a single characterization theorem, requiring only
`[Nonempty X]` and `[Nonempty Y]` (to choose base points via
`Classical.arbitrary`).

The bridge theorems in `InfrastructureAudit.lean` (under the names
`zero_rectangle_defect_implies_rankOne` and
`rankOne_implies_zero_rectangle_defect`) now have a generalized
counterpart that applies to any abelian group, not just `ℤ`. -/
