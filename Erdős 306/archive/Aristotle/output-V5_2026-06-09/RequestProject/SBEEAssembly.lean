/-
# SBEE Assembly: the faithful target `SBEEPartitionBound` and `single_block_counting`

This file formalizes **P3**: the faithful single-block counting target of
`28 Faithful SBEE Statement …md` and its assembly from Theorems A + B + C
(`30 §2`).

## Status overview

* `IrvingGood` — the faithful pruning/regime hypothesis (no free labeling).
* `SBEEPartitionBound` — the faithful target predicate (uniform `C`, pruning
  hypothesis, no labeling), exactly as designed in note 28 §3.
* `single_block_counting` — `SBEEPartitionBound c`.  `sorry`: the assembly
  `A (R < R_w) + C (R ≥ R_w) + trivial`, the mesh `R_C < R_w`, and the Laplace
  transform from the level-set bound to the partition-function bound.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEDispersion
import RequestProject.SBEEForcing

open Finset

namespace SBEEAssembly

open scoped Classical

/-- **Irving-good / pruning hypothesis** (faithful, no free labeling).

    The block `P` is a set of primes lying in a dyadic window `[X, 2X]` of
    near-maximal density `|P| ≥ X/(2 log X)`.  This is the regime hypothesis that
    the unconditional proof of `29`/`30` actually uses (it replaces note 28 §4's
    original abstract reciprocal-dispersion form: `29`/`30` show this geometric
    condition *implies* the required dispersion via the deterministic Lemma D, so
    no Kloosterman/Irving input is needed).  It is genuinely restrictive — sparse
    or non-dyadic blocks fail it — so the target below is **not** vacuous. -/
def IrvingGood (P : Finset ℕ) : Prop :=
  ∃ X : ℕ, 0 < X ∧ (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) ∧
    (X:ℝ) / (2 * Real.log X) ≤ P.card

/-- **Faithful SBEE partition-function target** (note 28 §3).

    A *single* block-independent constant `C` such that for every Irving-good
    prime block `P` with at least two primes, the Gaussian partition function
    saves: `∑_a exp(-c·Q_P(a)) ≤ C / σ_P`.

    `C` is quantified *outside* `∀ P` (fixing the vacuity failure 2 of note 28),
    `IrvingGood P` is a genuine hypothesis (fixing the too-strong failure 3), and
    there is **no** free labeling in the statement (the dominant/non-dominant
    split is internal proof structure). -/
def SBEEPartitionBound (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p),
      IrvingGood P → 2 ≤ P.card →
        blockPartFun P hP c ≤ C / sigmaP P

/-- **Single-block counting = SBEE** (`30 §2`, assembled).

    The faithful target `SBEEPartitionBound c` holds.

    Proof (`30 §2`): trichotomy on `R` against the window floor `R_w ≍ X/log³X`
    (Theorem B) and the fingerprint threshold `R_C ≍ X^{2/3}log^{4/3}X`
    (Theorem C), with the mesh `R_C ≪ R_w` (asymptotic in `X`):
    * `R < R_w`: every level-set assignment is dominant
      (`SBEEForcing.theorem_B_nondominant_forcing`); apply Theorem A
      (`SBEEForcing.theorem_A_dominant_count`).
    * `R_w ≤ R ≤ R_triv`: `SBEEFingerprint.fingerprint_count` (Theorem C, proved).
    * `R > R_triv`: trivial.
    Integrating the resulting level-set bound against `c·e^{-cR}` (Laplace) yields
    the partition-function bound `∑_a e^{-cQ_P(a)} ≤ C/σ_P`.

    **Status**: `sorry`.  Rests on the P1/P2 sorries (`fingerprint_count`,
    `theorem_A_dominant_count`, `theorem_B_nondominant_forcing`) plus the mesh
    `R_C < R_w` and the Laplace transform from level sets to the partition
    function. -/
theorem single_block_counting (c : ℝ) (hc : 0 < c) :
    SBEEPartitionBound c := by
  sorry

end SBEEAssembly
