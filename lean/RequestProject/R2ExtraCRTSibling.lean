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

/-
For a squarefree modulus `b`, congruence modulo every prime divisor of `b`
implies congruence modulo `b`.  This is the squarefree prime-divisor-to-`b`
step.
-/
lemma modEq_of_modEq_primeDivisors {b h m : ℕ} (hsq : Squarefree b)
    (hp : ∀ p, Nat.Prime p → p ∣ b → h ≡ m [MOD p]) :
    h ≡ m [MOD b] := by
  by_contra h_neq;
  -- Since $b$ is squarefree, we can write it as a product of distinct primes.
  obtain ⟨ps, hps⟩ : ∃ ps : Finset ℕ, (∀ p ∈ ps, Nat.Prime p) ∧ b = ps.prod id := by
    exact ⟨ Nat.primeFactors b, fun p hp => Nat.prime_of_mem_primeFactors hp, Eq.symm <| Nat.prod_primeFactors_of_squarefree hsq ⟩;
  simp_all +decide [ Nat.modEq_iff_dvd ];
  exact h_neq <| Finset.prod_dvd_of_coprime ( fun p hp' q hq' hpq => by have := Nat.coprime_primes ( hps.1 p hp' ) ( hps.1 q hq' ) ; aesop ) fun p hp' => hp p ( hps.1 p hp' ) <| Finset.dvd_prod_of_mem _ hp'

/-
If block-support residues agree but the global residue modulo
`b * ∏ blockSupport` does not agree, the mismatch occurs at a prime divisor of
`b`, hence inside `R` under `CoversPrimeDivisors`.

The statement adds a `Squarefree b` hypothesis: without it the claim is false
(e.g. `b = 4`, `h = 0`, `m = 2` agree modulo the only prime divisor `2` but not
modulo `4`).  The task explicitly allows adding this hypothesis.

The original `hbpos : 0 < b` hypothesis is kept (it was part of the task
statement) but is now redundant, since `Squarefree b` already implies `b ≠ 0`.
-/
theorem exists_R_mismatch_of_block_eq_not_global
    (BS : BlockSystem) (R : Finset ℕ) (b L h m : ℕ)
    (hL : L = b * ∏ s ∈ blockSupport BS, s)
    (_hbpos : 0 < b)
    (hsqfree : Squarefree b)
    (hcover : CoversPrimeDivisors R b)
    (hcop : BlockSupportCoprimeWith BS b)
    (hblock : ∀ s ∈ blockSupport BS, (h : ZMod s) = (m : ZMod s))
    (hnot : (h : ZMod L) ≠ (m : ZMod L)) :
    ∃ r ∈ R, Nat.Prime r ∧ r ∣ b ∧ (h : ZMod r) ≠ (m : ZMod r) := by
  contrapose! hnot; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  -- Since $b$ is squarefree and coprime to each element in the block-support, we can apply the Chinese Remainder Theorem.
  have h_crt : h ≡ m [MOD b] ∧ h ≡ m [MOD ∏ s ∈ blockSupport BS, s] := by
    refine' ⟨ modEq_of_modEq_primeDivisors hsqfree _, _ ⟩;
    · exact fun p pp dp => hnot p ( hcover p pp dp ) pp dp;
    · convert freq_assignment_eq_modEq_blockSupport_prod BS _;
      ext ⟨ p, hp ⟩ ; specialize hblock p hp; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
  rw [ Nat.ModEq.symm ];
  rw [ ← Nat.modEq_and_modEq_iff_modEq_mul ] ; tauto;
  exact Nat.Coprime.prod_right fun x hx => hcop x hx |> Nat.Coprime.symm

/-
A fiber over one block assignment has at most `b - 1` non-main siblings,
using `mainArc_fiber_card_le`.
-/
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
  convert Nat.sub_le_sub_right ( CircleMethod.mainArc_fiber_card_le BS L b hL a ) 1 using 1;
  exact Finset.card_erase_of_mem hmain

end CircleMethod

end
