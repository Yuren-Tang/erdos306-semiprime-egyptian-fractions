/-
# Faithful CRT Energy Encoding for Single-Block Counting

This file defines the concrete CRT energy objects for the single-block
counting theorem (CP 02 §1), with genuine CRT structure:

- **Block** `P : Finset ℕ` of primes
- **Assignment** `a : ∀ p : P, ZMod p.1` — element of `∏_{p ∈ P} ZMod p`
- **CRT representative** `crtRepr p q ap aq : ℤ` with
    `H ≡ ap (mod p)`, `H ≡ aq (mod q)`, `|H| ≤ p*q/2`
- **Energy** `QP P a = ∑_{p < q ∈ P} (H / (p·q))²`
- **Block deviation** `sigmaP P = √(∑_{p < q ∈ P} 1/(p·q)²)`

The assignment space has cardinality `∏_{p ∈ P} p`, so the trivial
bound `∑_a exp(-c·QP(a)) ≤ ∏ p` is *useless* — any genuine bound
must exhibit a saving over this product.

## References

- CP 02 §1 (CRT energy definitions)
- CP 03 §4 (single-block counting theorem)
-/
import Mathlib
import RequestProject.SBEE

open Finset BigOperators Classical

noncomputable section

/-! ## CRT representative -/

/-- For distinct primes p, q: coprimality. -/
theorem primes_coprime_of_ne {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) : Nat.Coprime p q :=
  (hp.coprime_iff_not_dvd).mpr fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)

/-- Centered CRT representative: H with H ≡ ap (mod p), H ≡ aq (mod q),
    centered in (-pq/2, pq/2]. Returns 0 when p, q are not coprime. -/
def crtRepr (p q : ℕ) (ap : ZMod p) (aq : ZMod q) : ℤ :=
  if hcop : Nat.Coprime p q then
    let n := p * q
    let combined : ZMod n := (ZMod.chineseRemainder hcop).symm (ap, aq)
    let raw : ℤ := (combined.val : ℤ)
    if raw > (n : ℤ) / 2 then raw - n else raw
  else 0

/-
Helper: centering an integer in [0, n) to (-n/2, n/2].
-/
theorem center_abs_le {n : ℕ} {raw : ℤ} (h0 : 0 ≤ raw) (hlt : raw < n) :
    |if raw > (n : ℤ) / 2 then raw - n else raw| ≤ (n : ℤ) / 2 := by
  split_ifs <;> rw [ abs_le ] <;> constructor <;> omega

/-- |crtRepr| ≤ pq/2 when p, q are coprime and positive. -/
theorem crtRepr_abs_le (p q : ℕ) (ap : ZMod p) (aq : ZMod q)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (hq : 0 < q) :
    |crtRepr p q ap aq| ≤ ↑(p * q) / 2 := by
  unfold crtRepr; rw [dif_pos hcop]
  haveI : NeZero (p * q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp hq)⟩
  apply center_abs_le (Int.natCast_nonneg _)
  exact_mod_cast ZMod.val_lt _

/-
Centering doesn't change the ZMod cast: for n dividing m,
    casting (if raw > m/2 then raw - m else raw) to ZMod n
    equals casting raw to ZMod n.
-/
theorem center_cast_eq {m n : ℕ} {raw : ℤ} (hdvd : (n : ℤ) ∣ m) :
    ((if raw > (m : ℤ) / 2 then raw - m else raw : ℤ) : ZMod n) =
      (raw : ZMod n) := by
  cases hdvd ; aesop

/-- crtRepr cast to ZMod p equals ap (the left CRT component). -/
theorem crtRepr_congr_left (p q : ℕ) (ap : ZMod p) (aq : ZMod q)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (hq : 0 < q) :
    (crtRepr p q ap aq : ZMod p) = ap := by
  simp only [crtRepr, dif_pos hcop]
  set combined := (ZMod.chineseRemainder hcop).symm (ap, aq)
  haveI : NeZero (p * q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp hq)⟩
  have val_cast : ((combined.val : ℕ) : ZMod p) = ap := by
    have h1 : ((combined.val : ℕ) : ZMod p) = ZMod.cast combined := by
      exact_mod_cast ZMod.natCast_val combined
    have h2 : (ZMod.cast combined : ZMod p) = (ZMod.chineseRemainder hcop combined).1 := by
      simp [ZMod.chineseRemainder]
    have h3 : (ZMod.chineseRemainder hcop combined).1 = ap := by
      simp [combined, RingEquiv.apply_symm_apply]
    rw [h1, h2, h3]
  split_ifs
  · simp only [Int.cast_sub, Int.cast_natCast]
    have : ((p * q : ℕ) : ZMod p) = 0 := by simp [Nat.cast_mul, zero_mul]
    rw [this, sub_zero, val_cast]
  · rw [Int.cast_natCast, val_cast]

/-- crtRepr cast to ZMod q equals aq (the right CRT component). -/
theorem crtRepr_congr_right (p q : ℕ) (ap : ZMod p) (aq : ZMod q)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (hq : 0 < q) :
    (crtRepr p q ap aq : ZMod q) = aq := by
  simp only [crtRepr, dif_pos hcop]
  set combined := (ZMod.chineseRemainder hcop).symm (ap, aq)
  haveI : NeZero (p * q) := ⟨Nat.ne_of_gt (Nat.mul_pos hp hq)⟩
  have val_cast : ((combined.val : ℕ) : ZMod q) = aq := by
    have h1 : ((combined.val : ℕ) : ZMod q) = ZMod.cast combined := by
      exact_mod_cast ZMod.natCast_val combined
    have h2 : (ZMod.cast combined : ZMod q) = (ZMod.chineseRemainder hcop combined).2 := by
      simp [ZMod.chineseRemainder]
    have h3 : (ZMod.chineseRemainder hcop combined).2 = aq := by
      simp [combined, RingEquiv.apply_symm_apply]
    rw [h1, h2, h3]
  split_ifs
  · simp only [Int.cast_sub, Int.cast_natCast]
    have : ((p * q : ℕ) : ZMod q) = 0 := by rw [Nat.cast_mul]; simp
    rw [this, sub_zero, val_cast]
  · rw [Int.cast_natCast, val_cast]

/-! ## CRT assignment space -/

/-- A block assignment: for each prime p ∈ P, a residue class mod p. -/
abbrev BlockAssignment (P : Finset ℕ) := ∀ p : P, ZMod p.1

/-! ## CRT energy and block deviation -/

/-- Ordered pairs from P.attach: pairs (p, q) with p.1 < q.1. -/
def orderedPrimePairsA (P : Finset ℕ) : Finset (P × P) :=
  (P.attach ×ˢ P.attach).filter fun pq => pq.1.1 < pq.2.1

/-- The CRT energy for an assignment a on a prime block P:

    `QP P a = ∑_{p < q ∈ P} (crtRepr(p,q,a(p),a(q)) / (p·q))²`

    This is the real quadratic form on the CRT product space.
    The nontrivial structure ensures that the trivial bound
    `≤ ∏ p` (the size of the assignment space) is far from the
    desired saving bound `≤ C / sigmaP`. -/
def QP (P : Finset ℕ) (a : BlockAssignment P) : ℝ :=
  ∑ pq ∈ orderedPrimePairsA P,
    ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ) /
      ((pq.1.1 : ℝ) * pq.2.1)) ^ 2

/-- QP is nonneg (sum of squares). -/
theorem QP_nonneg (P : Finset ℕ) (a : BlockAssignment P) :
    0 ≤ QP P a :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The block standard deviation:

    `sigmaP P = √(∑_{p < q ∈ P} 1/(p·q)²)` -/
def sigmaP (P : Finset ℕ) : ℝ :=
  Real.sqrt (∑ pq ∈ orderedPrimePairsA P,
    (1 : ℝ) / ((pq.1.1 : ℝ) * pq.2.1) ^ 2)

/-- sigmaP is nonneg. -/
theorem sigmaP_nonneg (P : Finset ℕ) : 0 ≤ sigmaP P :=
  Real.sqrt_nonneg _

/-
sigmaP is positive when P has at least 2 distinct primes.
-/
theorem sigmaP_pos_of_two (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (h2 : 1 < P.card) :
    0 < sigmaP P := by
  refine' Real.sqrt_pos.mpr _;
  refine' Finset.sum_pos _ _;
  · exact fun i hi => one_div_pos.mpr ( sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ i.1.2 ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ i.2.2 ) ) ) ) );
  · obtain ⟨ p, hp, q, hq, hpq ⟩ := Finset.one_lt_card.mp h2; cases lt_trichotomy p q <;> simp_all +decide [ orderedPrimePairsA ] ;
    · exact ⟨ ⟨ ⟨ p, hp ⟩, ⟨ q, hq ⟩ ⟩, by aesop ⟩;
    · exact ⟨ ⟨ ⟨ q, hq ⟩, ⟨ p, hp ⟩ ⟩, by aesop ⟩

/-! ## Assignment space cardinality -/

/-
The cardinality of the block assignment space is ∏_{p ∈ P} p.
-/
theorem blockAssignment_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
    Fintype.card (BlockAssignment P) = ∏ p ∈ P, p := by
  convert Fintype.card_pi;
  refine' Finset.prod_bij ( fun p hp => ⟨ p, hp ⟩ ) _ _ _ _ <;> aesop

/-! ## Partition function with saving bound -/

/-- The Gaussian-weighted partition function over the CRT assignment space:

    `blockPartFun P hP c = ∑_{a ∈ BlockAssignment P} exp(-c · QP(P, a))`

    The trivial bound is `≤ ∏_{p ∈ P} p` (each term ≤ 1).
    The SBEE saving bound is `≤ C / sigmaP(P)`, which is
    much smaller than `∏ p` for large blocks. -/
def blockPartFun (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (c : ℝ) : ℝ :=
  haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
  ∑ a : BlockAssignment P, Real.exp (-c * QP P a)

/-- **SBEE saving bound** (the real target — single-block counting theorem).

    `∑_a exp(-c·QP(a)) ≤ C / sigmaP(P)` -/
def SBEESavingBound (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (c : ℝ) : Prop :=
  ∃ (C : ℝ), 0 < C ∧ blockPartFun P hP c ≤ C / sigmaP P

/-! ## Label partition -/

/-- A labeling of the CRT assignment space. -/
structure BlockLabeling' (P : Finset ℕ) where
  label : BlockAssignment P → ℤ

variable {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)

/-- The label class: assignments with label m. -/
def labelClass' (bl : BlockLabeling' P) (m : ℤ) : Finset (BlockAssignment P) :=
  haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
  Finset.univ.filter fun a => bl.label a = m

/-- The active labels. -/
def activeLabels' (bl : BlockLabeling' P) : Finset ℤ :=
  haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
  Finset.univ.image bl.label

/-- A label is dominant if its class covers ≥ (1-ρ) fraction. -/
def isDominantLabel' (bl : BlockLabeling' P) (m : ℤ) (ρ : ℝ) : Prop :=
  haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
  (1 - ρ) * (Fintype.card (BlockAssignment P) : ℝ) ≤
    ((labelClass' hP bl m).card : ℝ)

/-- A label class is substantial if it has ≥ threshold elements. -/
def isSubstantialClass' (bl : BlockLabeling' P) (m : ℤ) (threshold : ℕ) : Prop :=
  threshold ≤ (labelClass' hP bl m).card

/-! ## Case analysis for single-block counting -/

/-- **Dominant case**: when label m covers ≥ (1-ρ)·N assignments,
    the partition function satisfies the saving bound via Irving
    majority correction (exception entropy O(log X) paid by energy).

    **Status**: `sorry` — requires the Irving majority correction. -/
theorem dominant_case_saving
    (bl : BlockLabeling' P) (m : ℤ) (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hdom : isDominantLabel' hP bl m ρ)
    (h2 : 1 < P.card) :
    SBEESavingBound P hP c := by
  sorry

/-- **Tiny case**: when all label classes are small (≤ T elements each),
    the short list is large, forcing R to be large enough to pay the
    crude entropy.

    **Status**: `sorry` — requires the short-list / energy tradeoff. -/
theorem tiny_case_saving
    (bl : BlockLabeling' P) (c : ℝ) (hc : 0 < c)
    (T : ℕ) (hT : 0 < T)
    (htiny : ∀ m ∈ activeLabels' hP bl, (labelClass' hP bl m).card ≤ T)
    (h2 : 1 < P.card) :
    SBEESavingBound P hP c := by
  sorry

/-- **Non-dominant substantial case** (FIE target).

When no label is dominant and substantial label classes collectively
cover ≥ ρ·N vertices, the partition function satisfies the saving bound.

This is the hard case requiring:
- `good_kSubset_exists_unconditional` (cluster selection, proved)
- Regular-uniqueness
- Singular-tuple sparsity
- Ambient-sensitive entropy descent
- `cross_label_divisor_energy` (proved)

**Status**: `sorry` — FIE core (F2b target). -/
theorem sbee_nondominant'
    (bl : BlockLabeling' P) (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hno_dom : ∀ m ∈ activeLabels' hP bl,
      ¬ isDominantLabel' hP bl m ρ)
    (hsubst :
      haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
      ρ * (Fintype.card (BlockAssignment P) : ℝ) ≤
        ∑ m ∈ (activeLabels' hP bl).filter
          (fun m => isSubstantialClass' hP bl m
            (Nat.ceil (ρ * Fintype.card (BlockAssignment P)))),
          ((labelClass' hP bl m).card : ℝ))
    (h2 : 1 < P.card) :
    SBEESavingBound P hP c := by
  sorry

/-! ## Assembly -/

/-- **Single-block counting theorem (assembled).**

Combines the three cases (dominant, tiny, non-dominant substantial)
to show the full partition function satisfies the saving bound
`∑_a exp(-c·QP(a)) ≤ C / sigmaP(P)`.

Each case is proved (or honestly sorry'd) against the genuine
CRT energy QP and block deviation sigmaP. No laundering:
the conclusion is NOT assumed as a hypothesis.

**Status**: depends on the three case theorems above. -/
theorem single_block_counting_faithful
    (c : ℝ) (hc : 0 < c) (h2 : 1 < P.card) :
    SBEESavingBound P hP c := by
  -- Case analysis on the label structure:
  -- 1. Dominant: some label covers ≥ (1-ρ)N → dominant_case_saving
  -- 2. Tiny: all labels ≤ T → tiny_case_saving
  -- 3. Non-dominant substantial → sbee_nondominant'
  sorry

end