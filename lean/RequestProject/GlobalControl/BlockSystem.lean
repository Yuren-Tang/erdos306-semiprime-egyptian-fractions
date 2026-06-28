import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic

open Finset Classical

noncomputable section

namespace GlobalControl

/-- A finite system of prime blocks indexed by consecutive dyadic scales. -/
structure BlockSystem where
  k0 : ℕ
  K : ℕ
  hk : k0 ≤ K
  hk0 : 1 ≤ k0
  P : ℕ → Finset ℕ
  hprime : ∀ k, ∀ p ∈ P k, Nat.Prime p
  hwindow : ∀ k, ∀ p ∈ P k, 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)
  hdensity : ∀ k, k0 ≤ k → k ≤ K →
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ (P k).card

/-- The finite set of primes occurring in a block system. -/
def blockSupport (BS : BlockSystem) : Finset ℕ :=
  (Finset.Icc BS.k0 BS.K).biUnion (fun k => BS.P k)

/-- A residue assignment on precisely the primes occurring in the system. -/
abbrev GlobalAssignment (BS : BlockSystem) :=
  (p : {p : ℕ // p ∈ blockSupport BS}) → ZMod p.1

/-- Every prime in the support inherits primality from its block. -/
lemma blockSupport_prime (BS : BlockSystem) {p : ℕ} (hp : p ∈ blockSupport BS) :
    Nat.Prime p := by
  rw [blockSupport, Finset.mem_biUnion] at hp
  obtain ⟨k, _, hpk⟩ := hp
  exact BS.hprime k p hpk

instance instNeZeroBlockSupport (BS : BlockSystem)
    (p : {p : ℕ // p ∈ blockSupport BS}) : NeZero p.1 :=
  ⟨(blockSupport_prime BS p.2).ne_zero⟩

/-- Number of dyadic blocks in the system. -/
def numBlocks (BS : BlockSystem) : ℕ := BS.K + 1 - BS.k0

/-- The scale range is long enough to carry the construction and grows at most
linearly with its initial scale. -/
def admissibleGlobalRange (BS : BlockSystem) : Prop :=
  2 * BS.k0 ≤ BS.K ∧ BS.K ≤ 3 * BS.k0

end GlobalControl

end
