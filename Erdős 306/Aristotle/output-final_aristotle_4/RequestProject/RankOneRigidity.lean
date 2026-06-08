import Mathlib

/-!
# Rank-one rigidity for integer-valued functions on a product

If every mixed second difference of `a : X → Y → ℤ` vanishes, then `a` decomposes
as `α x + β y` for suitable functions `α`, `β` determined by base-point values.
The converse also holds.
-/

variable {X Y : Type*}

/-- Vanishing of all mixed second differences. -/
def mixed_second_zero (a : X → Y → ℤ) : Prop :=
  ∀ x x' y y', a x y - a x y' - a x' y + a x' y' = 0

/-- If all mixed second differences of `a` vanish, then `a` decomposes as `α + β`
with `α x = a x y₀` and `β y = a x₀ y - a x₀ y₀`. -/
theorem rankOne_decomposition_of_mixed_zero
    (a : X → Y → ℤ) (x₀ : X) (y₀ : Y)
    (h : mixed_second_zero a) :
    let alpha : X → ℤ := fun x => a x y₀
    let beta : Y → ℤ := fun y => a x₀ y - a x₀ y₀
    ∀ x y, a x y = alpha x + beta y :=
  fun x y => by linarith [h x x₀ y y₀]

/-- Converse: any function of the form `α x + β y` has vanishing mixed second differences. -/
theorem mixed_zero_of_rankOne_decomposition
    (alpha : X → ℤ) (beta : Y → ℤ) :
    mixed_second_zero (fun x y => alpha x + beta y) :=
  fun _ _ _ _ => by ring
