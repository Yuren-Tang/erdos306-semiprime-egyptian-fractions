import RequestProject.LocalEnergy.CRTModel

/-! The dominant-label predicate for a finite prime block. -/

namespace LocalEnergy

/-- An assignment has a dominant label if one integer residue is carried by at
least a `(1 - rho)` proportion of its prime coordinates, with the label in the
canonical CRT range. -/
def HasDominantLabel (X : ℕ) (P : Finset ℕ) (a : BlockAssignment P) (rho : ℝ) : Prop :=
  ∃ m : ℤ, |m| ≤ (X : ℤ) ^ 2 / 2 ∧
    (1 - rho) * (P.card : ℝ) ≤
      ((P.attach.filter (fun p => a p = (m : ZMod (p : ℕ)))).card : ℝ)

end LocalEnergy
