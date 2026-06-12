/-
# Single-Block Counting Skeleton (Revised)

This file provides the abstract single-block counting framework and
connects it to the faithful CRT encoding in `BlockCRTEnergy.lean`.

The key insight: the original `BlockEnergyData`-based framework allowed
trivial proofs (e.g., `≤ N` since each `exp(-c·E(a)) ≤ 1`). The
faithful encoding in `BlockCRTEnergy.lean` uses concrete CRT energy
`QP` and block deviation `sigmaP`, with assignment space of size `∏ p`,
making the trivial bound useless.

## Architecture

- **Abstract framework** (this file): label classes, dominance,
  partition function decomposition — these are proved abstractly.
- **Faithful bounds** (`BlockCRTEnergy.lean`): dominant/tiny/non-dominant
  case bounds against QP/sigmaP — these require genuine energy analysis.
- **Assembly**: `single_block_counting_faithful` in `BlockCRTEnergy.lean`
  combines the three cases. No laundering.
-/
import Mathlib
import RequestProject.SBEE
import RequestProject.BlockCRTEnergy

open scoped BigOperators Classical
open Finset

noncomputable section

/-! ## Label partition setup -/

/-- A labeling of assignments: each assignment gets an integer label. -/
structure BlockLabeling (B : BlockEnergyData) where
  assignments : Finset (ℕ → ℤ)
  label : (ℕ → ℤ) → ℤ

variable {B : BlockEnergyData}

/-- The label class: assignments with a given label m. -/
def labelClass (bl : BlockLabeling B) (m : ℤ) : Finset (ℕ → ℤ) :=
  bl.assignments.filter (fun a => bl.label a = m)

/-- The set of labels that appear. -/
def activeLabels (bl : BlockLabeling B) : Finset ℤ :=
  bl.assignments.image bl.label

/-- A label m is "dominant" if its class covers ≥ (1-ρ) fraction of assignments. -/
def isDominantLabel (bl : BlockLabeling B) (m : ℤ) (ρ : ℝ) : Prop :=
  (1 - ρ) * (bl.assignments.card : ℝ) ≤ (labelClass bl m).card

/-- A label class is "substantial" if it has at least threshold elements. -/
def isSubstantialClass (bl : BlockLabeling B) (m : ℤ) (threshold : ℕ) : Prop :=
  threshold ≤ (labelClass bl m).card

/-! ## Partition functions -/

/-- Partition function restricted to a label class. -/
def classPartitionFun (B : BlockEnergyData) (bl : BlockLabeling B)
    (m : ℤ) (c : ℝ) : ℝ :=
  ∑ a ∈ labelClass bl m, Real.exp (-c * B.energy a)

/-- Full partition function over all assignments. -/
def fullPartitionFun (B : BlockEnergyData) (bl : BlockLabeling B)
    (c : ℝ) : ℝ :=
  ∑ a ∈ bl.assignments, Real.exp (-c * B.energy a)

/-! ## Helper: exp bound -/

theorem exp_neg_energy_le_one (B : BlockEnergyData) (a : ℕ → ℤ) (c : ℝ)
    (hc : 0 ≤ c) :
    Real.exp (-c * B.energy a) ≤ 1 := by
  rw [Real.exp_le_one_iff]; nlinarith [B.energy_nonneg a]

/-! ## Dominant case (abstract — remainder bound only) -/

/-- Assignments NOT in the dominant class. -/
def nonDominantAssignments (bl : BlockLabeling B) (m : ℤ) : Finset (ℕ → ℤ) :=
  bl.assignments.filter (fun a => bl.label a ≠ m)

theorem labelClass_union_nonDominant (bl : BlockLabeling B) (m : ℤ) :
    labelClass bl m ∪ nonDominantAssignments bl m = bl.assignments := by
  ext a; simp [labelClass, nonDominantAssignments]; tauto

theorem labelClass_disjoint_nonDominant (bl : BlockLabeling B) (m : ℤ) :
    Disjoint (labelClass bl m) (nonDominantAssignments bl m) := by
  unfold labelClass nonDominantAssignments
  rw [Finset.disjoint_filter]
  intro a _ h1 h2; exact h2 h1

theorem nonDominant_card_le (bl : BlockLabeling B) (m : ℤ) (ρ : ℝ)
    (_hρ : 0 ≤ ρ) (_hρ1 : ρ ≤ 1)
    (hdom : isDominantLabel bl m ρ) :
    ((nonDominantAssignments bl m).card : ℝ) ≤ ρ * bl.assignments.card := by
  convert sub_le_sub_left hdom ( bl.assignments.card : ℝ ) using 1;
  · rw [ eq_sub_iff_add_eq', ← Nat.cast_add, ← Finset.card_union_of_disjoint ( labelClass_disjoint_nonDominant bl m ), labelClass_union_nonDominant ];
  · ring

/-- Full partition function splits as dominant-class + non-dominant remainder. -/
theorem partitionFun_split_dominant (B : BlockEnergyData) (bl : BlockLabeling B)
    (m : ℤ) (c : ℝ) :
    fullPartitionFun B bl c =
      classPartitionFun B bl m c +
      ∑ a ∈ nonDominantAssignments bl m, Real.exp (-c * B.energy a) := by
  unfold fullPartitionFun classPartitionFun
  rw [← Finset.sum_union (labelClass_disjoint_nonDominant bl m),
      labelClass_union_nonDominant]

/-- **Abstract remainder bound**: if label m is dominant (covers ≥ (1-ρ)N),
    then the full partition function ≤ class-m function + ρ·N.

    NOTE: This is the abstract decomposition only. The bound ρ·N is
    **not** the saving bound. The genuine saving bound for the dominant
    case is in `BlockCRTEnergy.dominant_case_saving`, which uses the
    Irving majority correction against the concrete CRT energy. -/
theorem dominant_case_bound (B : BlockEnergyData) (bl : BlockLabeling B)
    (m : ℤ) (ρ : ℝ) (c : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc : 0 ≤ c)
    (hdom : isDominantLabel bl m ρ) :
    fullPartitionFun B bl c ≤
      classPartitionFun B bl m c + ρ * bl.assignments.card := by
  rw [partitionFun_split_dominant]
  gcongr
  calc ∑ a ∈ nonDominantAssignments bl m, Real.exp (-c * B.energy a)
      ≤ ∑ _a ∈ nonDominantAssignments bl m, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => exp_neg_energy_le_one B a c hc)
    _ = (nonDominantAssignments bl m).card := by simp
    _ ≤ ρ * bl.assignments.card := nonDominant_card_le bl m ρ hρ hρ1 hdom

/-! ## Trivial bound (useless for saving — kept for reference)

NOTE: The bound `fullPartitionFun ≤ N` is the trivial bound that
each exp(-c·E(a)) ≤ 1. Against the faithful CRT encoding
(`BlockCRTEnergy.lean`), where N = ∏_{p ∈ P} p, this bound is
far too weak to establish the saving bound ≤ C/σ_P.
The genuine bounds are in `BlockCRTEnergy.lean`. -/

/-- Trivial bound: full partition function ≤ N (each term ≤ 1). -/
theorem trivial_bound (B : BlockEnergyData) (bl : BlockLabeling B)
    (c : ℝ) (hc : 0 ≤ c) :
    fullPartitionFun B bl c ≤ bl.assignments.card := by
  unfold fullPartitionFun
  calc ∑ a ∈ bl.assignments, Real.exp (-c * B.energy a)
      ≤ ∑ _a ∈ bl.assignments, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => exp_neg_energy_le_one B a c hc)
    _ = bl.assignments.card := by simp

/-! ## Non-dominant substantial case

The genuine non-dominant bound is stated in `BlockCRTEnergy.sbee_nondominant'`,
against the concrete CRT energy QP and block deviation sigmaP.
The abstract version below is superseded. -/

/-- **Non-dominant substantial case** (abstract version — superseded).

This abstract statement uses `BlockEnergyData` which carries no CRT
structure. The genuine, faithful version is `BlockCRTEnergy.sbee_nondominant'`,
which states the bound against QP and sigmaP.

**Status**: `sorry` — see `BlockCRTEnergy.sbee_nondominant'`. -/
theorem sbee_nondominant
    (B : BlockEnergyData) (bl : BlockLabeling B)
    (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hno_dom : ∀ m ∈ activeLabels bl, ¬ isDominantLabel bl m ρ)
    (hsubst : ρ * bl.assignments.card ≤
      ∑ m ∈ (activeLabels bl).filter
        (fun m => isSubstantialClass bl m
          (Nat.ceil (ρ * bl.assignments.card))),
        (labelClass bl m).card) :
    ∃ (C : ℝ), 0 < C ∧
      fullPartitionFun B bl c ≤ C / Real.sqrt B.variance := by
  sorry

/-! ## Assembly

The genuine single-block counting theorem is
`BlockCRTEnergy.single_block_counting_faithful`, which assembles the
three cases against the concrete CRT energy.

The old `single_block_counting_assembled` was a laundering lemma that
assumed `N ≤ C/√variance` as a hypothesis. It has been removed.
The following connects the abstract and concrete frameworks. -/

/-- Construct `ConditionSBEE` from its two fields. -/
theorem conditionSBEE_of_partition_and_fourier
    (h_partition : ∀ (B : BlockEnergyData) (c : ℝ), 0 < c →
      ∃ (C : ℝ), 0 < C ∧
        ∀ (assignments : Finset (ℕ → ℤ)),
          (∑ a ∈ assignments, Real.exp (-c * B.energy a)) ≤
            C / Real.sqrt B.variance)
    (h_fourier : ∀ (T : Finset ℕ) (b : ℕ), 0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b)) :
    ConditionSBEE :=
  ⟨h_partition, h_fourier⟩

end
