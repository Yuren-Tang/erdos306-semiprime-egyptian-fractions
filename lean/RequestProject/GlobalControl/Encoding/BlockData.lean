import RequestProject.GlobalControl.Basic

/-!
# Global block energy data

Per-block energies, hot blocks, energy shells, and the numerical scales used by
the global encoding argument.
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-- Per-block internal energy of a global assignment. -/
def blockEnergy (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  QP (BS.P k) (restrict BS a k)

/-- The cold/hot threshold `R_w(k) = c2·2^k/log³(2^k)` (Theorem-B floor). -/
def Rw (c2 : ℝ) (k : ℕ) : ℝ := c2 * 2 ^ k / (Real.log (2 ^ k)) ^ 3

/-- Hot block: internal energy at least the forcing floor. -/
def isHot (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (k : ℕ) : Prop :=
  Rw c2 k ≤ blockEnergy BS a k

instance instDecidableIsHot (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (k : ℕ) : Decidable (isHot BS c2 a k) := Classical.dec _

/-- The hot set: scales in `[k0,K]` whose block is hot. -/
def hotSet (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Icc BS.k0 BS.K).filter (isHot BS c2 a)
/-- Integer energy shell of each block. -/
def shellVec (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℕ :=
  ⌊blockEnergy BS a k⌋₊

/-- The number of primes in block `k` on which the assignment has residue
class `m`. -/
def classCount (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) (m : ℤ) : ℕ :=
  ((BS.P k).attach.filter
    (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card

/-- The exception-reduced boundary penalty floor `Π(k)`. -/
def Pifloor (BS : BlockSystem) (e0 : ℝ) (k : ℕ) : ℝ :=
  (((BS.P (k+1)).card : ℝ) - e0 - 1) * (((BS.P k).card : ℝ) - e0) ^ 3 /
    (2 ^ 13 * ((2:ℝ) ^ k) ^ 2)

/-- Label range at a segment start (L3 + cold threshold; note 38 §3 L3c). -/
def labelRange (c2 : ℝ) (k : ℕ) : ℤ := ⌈(168:ℝ) * Real.sqrt c2 *
    ((2:ℝ) ^ k) ^ (3/2 : ℝ) / Real.sqrt (Real.log (2 ^ k))⌉

end GlobalControl

end
