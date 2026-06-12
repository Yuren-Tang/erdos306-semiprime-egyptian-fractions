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

/-- **VACUOUS per-block predicate — DO NOT use as the SBEE target.**

    `SBEESavingBound P hP c := ∃ C, 0 < C ∧ blockPartFun P hP c ≤ C / sigmaP P`.

    The constant `C` is quantified *inside* the per-block statement, so for any
    single finite block `P` with `1 < P.card` one may simply take
    `C = blockPartFun P hP c * sigmaP P + 1` (using `sigmaP P > 0`).  Hence this
    predicate carries **no** dispersion content whatsoever and is retained only
    for reference.  The faithful, block-independent target is
    `SBEEUniformSaving` below, whose constant is quantified *outside* the `∀ P`. -/
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

/-- The substantial classes (those with `≥ ⌈ρ·N⌉` elements) collectively cover
    `≥ ρ·N` assignments, where `N = ∏_{p ∈ P} p` is the assignment-space size. -/
def substantialCoverage' (bl : BlockLabeling' P) (ρ : ℝ) : Prop :=
  haveI : ∀ p : P, NeZero p.1 := fun p => ⟨(hP p.1 p.2).ne_zero⟩
  ρ * (Fintype.card (BlockAssignment P) : ℝ) ≤
    ∑ m ∈ (activeLabels' hP bl).filter
      (fun m => isSubstantialClass' hP bl m
        (Nat.ceil (ρ * Fintype.card (BlockAssignment P)))),
      ((labelClass' hP bl m).card : ℝ)

/-! ## Faithful UNIFORM saving predicate (F2a''')

The per-block `SBEESavingBound` above is **vacuous** (see its docstring): its
constant `C` is quantified *inside* the per-block statement, so any single finite
block satisfies it.  The faithful predicate fixes a single block-independent
constant `C` *outside* the universal quantifier over all prime blocks `P`.  For
a fixed `C`, "for every block `P`" is then a genuine constraint encoding the real
dispersion content (and is **not** dischargeable by a per-block `∃C` trick). -/

/-- **Faithful uniform SBEE saving predicate** (the real single-block target).

    There is a single, block-independent constant `C > 0` such that for *every*
    prime block `P` with at least two primes,
    `blockPartFun P hP c = ∑_a exp(-c·QP(P,a)) ≤ C / sigmaP P`.

    Because `C` is quantified *before* `∀ P`, this is a genuine (non-vacuous)
    constraint.  Computation check for `P = {p,q}`:
    `∑_a exp(-c(H/pq)²) ≈ pq·√(π/c) = √(π/c)/sigmaP P`, so the true uniform
    constant is `C ≈ √(π/c)`, depending only on `c`. -/
def SBEEUniformSaving (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p), 2 ≤ P.card →
      blockPartFun P hP c ≤ C / sigmaP P

/-! ## Case analysis for single-block counting (against the UNIFORM predicate)

Each case below provides a single, block-independent constant `C` (quantified
*outside* the `∀ P`), and asserts the per-block bound `blockPartFun ≤ C / sigmaP`
for every prime block `P` whose canonical labeling satisfies the corresponding
case hypothesis.  These are the **real** theorems: proving them requires genuine
dispersion/energy content and they cannot be discharged by a per-block `∃C`
trick.  They are left as clearly-named honest `sorry`s.

**DEPRECATED / SUPERSEDED (Phase W).** The `*_uniform` stubs below
(`dominant_case_uniform`, `tiny_case_uniform`, `sbee_nondominant_uniform`,
`single_block_counting_uniform`) are superseded by the verified
`SBEEAssembly.single_block_counting`.  They are retained for documentation only
and are not part of the `erdos_306` dependency chain.  (The CRT-energy
*definitions* above — `crtRepr`, `QP`, `sigmaP`, `blockPartFun` — remain in active
use, including by `GlobalControl.lean`.) -/

/-- **Dominant case (uniform).**

    There is a block-independent constant `C` such that every prime block `P`
    that carries a dominant label (one class covering ≥ (1-ρ)·N assignments)
    satisfies the saving bound `blockPartFun ≤ C / sigmaP`.

    Genuine content (Irving majority correction): the dominant Gaussian peak
    contributes `≤ C/sigmaP`, while the ≤ρ-fraction of exceptions each carry CRT
    energy `QP ≫ |P|`, so their `exp(-c·QP)` contribution is exponentially small
    and their `O(log)` choice/residue entropy is paid by that energy.  Since `C`
    is fixed *outside* `∀ P`, this is **not** dischargeable per-block.

    **Status**: honest `sorry` — uniform dispersion content. -/
theorem dominant_case_uniform (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p), 2 ≤ P.card →
        ∀ (bl : BlockLabeling' P) (m : ℤ), isDominantLabel' hP bl m ρ →
          blockPartFun P hP c ≤ C / sigmaP P := by
  sorry

/-- **Tiny case (uniform).**

    There is a block-independent constant `C` such that every prime block `P`
    all of whose label classes are small (≤ T elements each, for some positive
    `T` allowed to depend on the block) satisfies `blockPartFun ≤ C / sigmaP`.

    Genuine content (CP 03 §7 / base-list lower bound): an almost-all-tiny
    profile forces the short list — hence the level `R` — to be large enough to
    pay the crude entropy.  Since `C` is fixed *outside* `∀ P`, this is **not**
    dischargeable per-block.

    **Status**: honest `sorry` — uniform short-list / energy tradeoff content. -/
theorem tiny_case_uniform (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p), 2 ≤ P.card →
        ∀ (bl : BlockLabeling' P) (T : ℕ), 0 < T →
          (∀ m ∈ activeLabels' hP bl, (labelClass' hP bl m).card ≤ T) →
            blockPartFun P hP c ≤ C / sigmaP P := by
  sorry

/-- **Non-dominant substantial case (uniform)** — the FIE core (F2b target).

    There is a block-independent constant `C` such that every prime block `P`
    with no dominant label, but whose substantial label classes collectively
    cover ≥ ρ·N assignments, satisfies `blockPartFun ≤ C / sigmaP`.

    This is the decisive case, requiring:
    - `good_kSubset_exists_unconditional` (cluster selection, proved)
    - Regular-uniqueness (no short kernel ⇒ ≤1 witness per residual prime)
    - Singular-tuple sparsity
    - Ambient-sensitive entropy descent
    - `cross_label_divisor_energy` (proved)

    Since `C` is fixed *outside* `∀ P`, this is **not** dischargeable per-block.

    **Status**: honest `sorry` — FIE core (F2b target). -/
theorem sbee_nondominant_uniform (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p), 2 ≤ P.card →
        ∀ (bl : BlockLabeling' P),
          (∀ m ∈ activeLabels' hP bl, ¬ isDominantLabel' hP bl m ρ) →
          substantialCoverage' hP bl ρ →
          blockPartFun P hP c ≤ C / sigmaP P := by
  sorry

/-! ## Assembly -/

/-- **Single-block counting theorem (assembled, uniform).**

The genuine single-block counting bound: a single block-independent constant `C`
works for *every* prime block `P`, i.e. `SBEEUniformSaving c`.

This is assembled from the three uniform cases (`dominant_case_uniform`,
`tiny_case_uniform`, `sbee_nondominant_uniform`): for each block one chooses a
canonical labeling and a trichotomy places it into exactly one case, with the
final constant the maximum of the three case constants.  The conclusion is NOT
assumed as a hypothesis (no laundering).

**Status**: honest `sorry` — the case-selection trichotomy plus the three
uniform cases (themselves honest sorries) supply the genuine content. -/
theorem single_block_counting_uniform (c : ℝ) (hc : 0 < c) :
    SBEEUniformSaving c := by
  sorry

end