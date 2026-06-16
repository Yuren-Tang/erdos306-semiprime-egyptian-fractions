import RequestProject.R2ExtraMultiGadget
import RequestProject.FiberCount

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2 extra-minor CRT sibling task

This file is an Aristotle task file.  Please replace the `sorry`s below by
proofs, without adding axioms.
-/

/-- `R` contains every prime divisor of `b`. -/
def CoversPrimeDivisors (R : Finset ℕ) (b : ℕ) : Prop :=
  ∀ r, Nat.Prime r → r ∣ b → r ∈ R

/-- The block-support primes are coprime to the denominator `b`. -/
def BlockSupportCoprimeWith (BS : BlockSystem) (b : ℕ) : Prop :=
  ∀ s ∈ blockSupport BS, Nat.Coprime s b

/-- If block-support residues agree but the global residue modulo
`b * ∏ blockSupport` does not agree, the mismatch occurs at a prime divisor of
`b`, hence inside `R` under `CoversPrimeDivisors`.

Acceptable modifications:
* replace `ZMod` equalities by `Nat.ModEq` throughout;
* split off the squarefree-prime-divisor-to-`b` step into a helper lemma;
* add a squarefree hypothesis on `b` if needed for the prime divisor step.
-/
theorem exists_R_mismatch_of_block_eq_not_global
    (BS : BlockSystem) (R : Finset ℕ) (b L h m : ℕ)
    (hL : L = b * ∏ s ∈ blockSupport BS, s)
    (hbpos : 0 < b)
    (hcover : CoversPrimeDivisors R b)
    (hcop : BlockSupportCoprimeWith BS b)
    (hblock : ∀ s ∈ blockSupport BS, (h : ZMod s) = (m : ZMod s))
    (hnot : (h : ZMod L) ≠ (m : ZMod L)) :
    ∃ r ∈ R, Nat.Prime r ∧ r ∣ b ∧ (h : ZMod r) ≠ (m : ZMod r) := by
  sorry

/-- A fiber over one block assignment has at most `b - 1` non-main siblings,
using `mainArc_fiber_card_le`. -/
theorem extra_sibling_card_le_pred_b
    (BS : BlockSystem) (L b : ℕ)
    (hL : L = b * ∏ p ∈ blockSupport BS, p)
    (a : GlobalAssignment BS)
    (main : ℕ)
    (hmain :
      main ∈ (Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)) :
    (((Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)).erase main).card ≤ b - 1 := by
  sorry

end CircleMethod

end

