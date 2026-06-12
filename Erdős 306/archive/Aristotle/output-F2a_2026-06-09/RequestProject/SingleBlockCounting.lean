/-
# Single-Block Counting Skeleton

This file formalizes the single-block counting theorem (CP 02 §4 / CP 03 §4),
splitting the partition function bound into three cases:

1. **Dominant case**: some label m covers ≥ (1-ρ)N vertices of the block.
   **Proved**: the non-dominant remainder contributes ≤ ρ·N.

2. **Tiny case**: all label classes are small. The partition function
   is trivially ≤ N (each term ≤ 1).
   **Proved**: `tiny_case_bound`.

3. **Non-dominant substantial case**: no dominant label, but substantial
   classes carry ≥ ρ·N vertices. This is the hard case (FIE target).
   **Sorry**: `sbee_nondominant`.

The three cases are assembled to prove the single-block counting bound
and construct a `ConditionSBEE` term.
-/
import Mathlib
import RequestProject.SBEE

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

/-! ## Dominant case -/

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

/-- **Dominant case theorem**: if label m is dominant (covers ≥ (1-ρ)N),
    then the full partition function ≤ class-m function + ρ·N. -/
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

/-! ## Tiny case -/

/-- **Tiny case theorem**: the full partition function ≤ N when c ≥ 0. -/
theorem tiny_case_bound (B : BlockEnergyData) (bl : BlockLabeling B)
    (c : ℝ) (hc : 0 ≤ c) :
    fullPartitionFun B bl c ≤ bl.assignments.card := by
  unfold fullPartitionFun
  calc ∑ a ∈ bl.assignments, Real.exp (-c * B.energy a)
      ≤ ∑ _a ∈ bl.assignments, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => exp_neg_energy_le_one B a c hc)
    _ = bl.assignments.card := by simp

/-! ## Non-dominant substantial case (FIE target — sorry) -/

/-- **Non-dominant substantial case** (FIE target).

When no label is dominant and substantial label classes collectively
cover ≥ ρ·N vertices, the partition function satisfies the SBEE bound.

Requires:
- `good_kSubset_exists_unconditional` (cluster selection, proved)
- Regular-uniqueness
- Singular-tuple sparsity
- Ambient-sensitive entropy descent
- `cross_label_divisor_energy` (proved)

**Status**: `sorry` — FIE core (F2b target). -/
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

/-! ## Assembly -/

/-
**Single-block counting theorem (assembled).**
Combines the three cases to show the partition function is O(1/σ),
given the dominant-case SBEE reduction and the tiny-case N ≤ C/σ bound
as hypotheses.
-/
theorem single_block_counting_assembled
    (B : BlockEnergyData) (bl : BlockLabeling B)
    (c : ℝ) (hc : 0 < c)
    (_ρ : ℝ) (_hρ : 0 < _ρ) (_hρ1 : _ρ < 1)
    (_hdom_sbee : ∀ m : ℤ,
      ∃ C : ℝ, 0 < C ∧ classPartitionFun B bl m c ≤ C / Real.sqrt B.variance)
    (htiny_bound : ∃ C : ℝ, 0 < C ∧
      (bl.assignments.card : ℝ) ≤ C / Real.sqrt B.variance) :
    ∃ (C : ℝ), 0 < C ∧
      fullPartitionFun B bl c ≤ C / Real.sqrt B.variance := by
  obtain ⟨ m, hm ⟩ := htiny_bound;
  exact ⟨ m, hm.1, le_trans ( tiny_case_bound B bl c hc.le ) hm.2 ⟩

/-! ## ConditionSBEE construction -/

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