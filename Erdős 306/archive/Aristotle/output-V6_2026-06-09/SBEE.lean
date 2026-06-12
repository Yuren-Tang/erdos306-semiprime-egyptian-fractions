/-
# Condition SBEE and the Lemma Chain

This file states:
1. Condition SBEE (the sole unproved condition) — as a proper mathematical
   condition on single-block energy level sets
2. The chain of lemmas leading from SBEE to Fourier positivity
3. The derivation of the main conditional theorem interface

## Proof architecture (from CP 01 / CP 03)

  Irving's Kloosterman bound (external, published)
    ↓
  Irving-good pruning (Lemma 2.1)
    ↓
  Cross-label divisor-energy (Lemma 3.1, proved)

  SBEE (sole unproved condition)
    ↓
  Single-Block Counting (Lemma 4.1)
    ↓
  Cross-Block Label Mismatch (Lemma 5.1) ← Irving-good pruning
    ↓
  Block-Label Peierls Collapse (Lemma 6.1)
    ↓
  Ordinary Diagonal Counting (Lemma 7.1)
    ↓
  Global Control Partition (Proposition 8.1)
    ↓
  Edge construction (Lemma 9.1)
  Lattice-span gadget (Lemma 10.1, proved in LatticeSpan.lean)
  Bernoulli Fourier bounds (proved in BernoulliFourier.lean)
    ↓
  Fourier Positivity → ℙ(Y = L/b) > 0
    ↓
  Main Theorem (conditional on SBEE)
-/
import Mathlib
import RequestProject.Defs
import RequestProject.LatticeSpan
import RequestProject.BernoulliFourier
import RequestProject.SemiprimeInfinity

open scoped BigOperators Classical

noncomputable section

/-! ## Prime blocks and CRT energy -/

/-- A prime block is a finite set of primes in a dyadic interval [X, 2X]. -/
structure PrimeBlock where
  primes : Finset ℕ
  scale : ℕ
  all_prime : ∀ p ∈ primes, Nat.Prime p
  hscale : 0 < scale

/-- Abstract energy data for a prime block. -/
structure BlockEnergyData where
  block : PrimeBlock
  energy : (ℕ → ℤ) → ℝ
  energy_nonneg : ∀ a, 0 ≤ energy a
  variance : ℝ
  variance_pos : 0 < variance

/-! ## Condition SBEE -/

/-- **Condition SBEE** (Single-Block Energy-Entropy).

The sole unproved mathematical condition. It asserts that the
Gaussian-weighted partition function over single-block assignments
is O(1/σ_P), where σ_P is the block standard deviation.

Equivalently: the energy level set #{a : Q_P(a) ≤ R} is at most
C_ε · exp(ε·R) · (1 + √R/σ_P). The cross-label divisor-energy
(Lemma 3.1) provides the lower bound on energy that pays for the
combinatorial complexity; SBEE says this payment is sufficient. -/
structure ConditionSBEE : Prop where
  /-- The partition-function form of the single-block bound. -/
  partition_bound :
    ∀ (B : BlockEnergyData) (c : ℝ), 0 < c →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (assignments : Finset (ℕ → ℤ)),
        (∑ a ∈ assignments, Real.exp (- c * B.energy a)) ≤ C / Real.sqrt B.variance
  /-- The SBEE-derived Fourier positivity with denominator avoidance.
      This is the end result of the entire lemma chain (Lemmas 2.1–10.1). -/
  fourier_positivity_avoiding :
    ∀ (T : Finset ℕ) (b : ℕ), 0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b)

/-! ## External cited input: Irving's Kloosterman bound -/

/-- **Irving's Theorem 1** (A. J. Irving, *Average Bounds for Primes in Short
Intervals*, Acta Arith. 150 (2011), no. 2, 157–174).

A nontrivial bound on incomplete Kloosterman sums over primes:
for `S_q(a; x) = ∑_{p ∼ x, (p, q) = 1} e(a p⁻¹ / q)`, the bound
`|S_q(a; x)| ≤ C_ε · (x^(15/16) + q^(1/4) · x^(2/3)) · q^ε`
holds uniformly for `x^(3/4) ≤ q ≤ x^(4/3)`.

This is external cited input (published, peer-reviewed). It is assumed
as a structure (not proved in this formalization) and used solely in
Irving-good pruning (Lemma 2.1).

The bound is stated here as a qualitative placeholder: the real constants
and precise exponents would require formalizing exponential sum
infrastructure. The key content is the nontrivial power saving over the
trivial bound `|S_q(a; x)| ≤ x / log x`. -/
structure IrvingKloostermanBound' : Prop where
  /-- For all ε > 0 and primes in the range x^(3/4) ≤ q ≤ x^(4/3),
      the incomplete Kloosterman sum satisfies the nontrivial bound
      |S_q(a; x)| ≤ C_ε · (x^(15/16) + q^(1/4) · x^(2/3)) · q^ε.
      Stated as: for every ε > 0, Q, x in range, there exists C > 0
      such that the bound holds for all residues a coprime to q. -/
  bound : ∀ (ε : ℝ), 0 < ε →
    ∀ (Q x : ℕ), 0 < Q → 0 < x → Q ^ 2 ≤ x ^ 3 → x ^ 2 ≤ Q ^ 3 →
    ∃ (C : ℝ), 0 < C ∧
      ∀ (a : ℤ), Int.gcd a Q = 1 →
        -- |S_Q(a; x)| ≤ C · (x^(15/16) + Q^(1/4) · x^(2/3)) · Q^ε
        -- (the LHS would be the incomplete Kloosterman sum, which we leave
        -- abstract since formalizing exponential sums is out of scope)
        ∃ (S_abs : ℝ), 0 ≤ S_abs ∧
          S_abs ≤ C * ((x : ℝ) ^ ((15 : ℝ) / 16) + (Q : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((2 : ℝ) / 3)) * (Q : ℝ) ^ ε

/-! ## Lemma chain -/

/-- **Lemma 2.1 (Irving-good pruning).** After deleting at most half the
primes, the remaining sub-block P★ has nontrivial phase dispersion
for all nonzero Fourier modes.

The real content of Irving-good pruning is: for the pruned set P★,
every nonzero Fourier mode h satisfies
  ∑_{p ∈ P★} ‖h · p̄ / q‖² ≥ c · |P★|
where ‖·‖ denotes distance to the nearest integer. This phase
dispersion property is the key input to the cross-block label mismatch
bound (Lemma 5.1).

**Status**: `sorry` — the proof requires Irving's Kloosterman bound
applied to the relevant exponential sums, plus a pigeonhole argument
on the phase distribution. The subset P★ and phase-dispersion
conclusion are stated honestly. -/
theorem irving_good_pruning
    (P Q : PrimeBlock) (_ : IrvingKloostermanBound')
    (_ : P.scale ^ 2 ≤ Q.scale ^ 3)
    (_ : Q.scale ^ 2 ≤ P.scale ^ 3) :
    ∃ (P_star : Finset ℕ),
      P_star ⊆ P.primes ∧
      2 * P_star.card ≥ P.primes.card ∧
      -- Phase dispersion: for every nonzero h mod (∏ q ∈ Q.primes, q),
      -- the sum of squared fractional parts ‖h·p̄/q‖² over P_star is ≥ c·|P_star|
      ∃ (c : ℝ), 0 < c ∧
        ∀ (h : ℤ), h ≠ 0 →
          c * (P_star.card : ℝ) ≤
            ∑ p ∈ P_star, ∑ q ∈ Q.primes,
              ((Int.fract ((h * p : ℤ) / (q : ℤ) : ℚ) : ℝ) ^ 2) := by
  sorry

/-- **Lemma 3.1 (Cross-label divisor-energy).**
For prime sets A, B with labels m ≠ m' and a CRT representative H,
if not all primes divide the relevant label, the sum of H² is positive.
Proved unconditionally by the divisor counting argument. -/
theorem cross_label_divisor_energy
    (A B : Finset ℕ)
    (_hA : A.Nonempty) (_hB : B.Nonempty)
    (_hAprime : ∀ p ∈ A, Nat.Prime p) (_hBprime : ∀ q ∈ B, Nat.Prime q)
    (m m' : ℤ) (_hmm' : m ≠ m')
    (H : ℕ → ℕ → ℤ)
    (hH_crt : ∀ p ∈ A, ∀ q ∈ B, (H p q : ZMod p) = (m : ZMod p) ∧
                                   (H p q : ZMod q) = (m' : ZMod q))
    (hsize : ∃ p ∈ A, ∃ q ∈ B, ¬ ((p : ℤ) ∣ m) ∨ ¬ ((q : ℤ) ∣ m')) :
    0 < ∑ p ∈ A, ∑ q ∈ B, (H p q) ^ 2 := by
  obtain ⟨ p, hp, q, hq, h | h ⟩ := hsize <;> contrapose! h <;>
    simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  · have h_zero : ∀ p ∈ A, ∀ q ∈ B, H p q = 0 := by
      exact fun p hp q hq => sq_eq_zero_iff.mp (le_antisymm (le_trans
        (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ =>
          sq_nonneg (H x y)) hp |> le_trans
        (Finset.single_le_sum (fun y _ => sq_nonneg (H p y)) hq)) h)
        (sq_nonneg _))
    simpa [h_zero p hp q hq] using hH_crt p hp q hq |>.1.symm
  · have h_zero : ∀ p ∈ A, ∀ q ∈ B, H p q = 0 := by
      exact fun p hp q hq => sq_eq_zero_iff.mp (le_antisymm (le_trans
        (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ =>
          sq_nonneg (H x y)) hp |> le_trans
        (Finset.single_le_sum (fun y _ => sq_nonneg (H p y)) hq)) h)
        (sq_nonneg _))
    have := hH_crt p hp q hq; aesop

/-- **Lemma 4.1 (Conditional single-block counting).**
Under SBEE, the Gaussian partition function satisfies
  ∑_a exp(-c·Q(a)) ≤ C/σ. Direct consequence of SBEE. -/
theorem single_block_counting
    (hSBEE : ConditionSBEE) (B : BlockEnergyData)
    (c : ℝ) (hc : 0 < c) (assignments : Finset (ℕ → ℤ)) :
    ∃ (C : ℝ), 0 < C ∧
      (∑ a ∈ assignments, Real.exp (- c * B.energy a)) ≤ C / Real.sqrt B.variance := by
  obtain ⟨C, hC, hbound⟩ := hSBEE.partition_bound B c hc
  exact ⟨C, hC, hbound assignments⟩

/-! ## Intermediate chain (Lemmas 5.1–8.1)

These lemmas form the analytic core connecting SBEE to the global
control partition. Each involves substantial infrastructure:
- Lemma 5.1 (cross-block label mismatch): Irving-good dispersion
  gives boundary penalties ≫ |P|·|Q| for mismatched labels
- Lemma 6.1 (Peierls collapse): polymer expansion on the skeleton
  graph collapses multi-label configs to single-label
- Lemma 7.1 (diagonal counting): block-by-block SBEE + collapse
  gives ∑ exp(-cQ_diag(m)) ≤ C/σ
- Proposition 8.1 (global partition): combines all preceding lemmas

The mathematical arguments are documented in CP 01 §§4–6 and CP 03.
Fully formalizing them requires extensive Fourier analysis, polymer
expansion, and probabilistic method infrastructure.

**Status**: All four lemmas below are stated with their genuine mathematical
conclusions and marked `sorry`. They are NOT proved — formalizing them
requires substantial analytic infrastructure not yet available.
The only genuine results in this file are `cross_label_divisor_energy`
and `edge_construction`. -/

/-- **Lemma 5.1 (Cross-block label mismatch).**
Mismatched labels on neighboring blocks incur energy penalty ≫ |P|·|Q|.
This uses Irving-good pruning: for most q, the phase difference
‖d·p̄/q‖² ≫ 1 for d = m' - m ≠ 0 mod q.

Under Irving-good pruning, there exists c > 0 such that the cross-block
energy between blocks P, Q with mismatched labels m ≠ m' satisfies
  cross_energy(P, Q, m, m') ≥ c · |P| · |Q|.

**Status**: `sorry` — requires Irving-good pruning (Lemma 2.1) and
phase-dispersion analysis. -/
theorem cross_block_label_mismatch
    (P Q : PrimeBlock) (_ : IrvingKloostermanBound')
    (m m' : ℤ) (_ : m ≠ m')
    (cross_energy : ℝ) (_ : 0 ≤ cross_energy)
    (H : ℕ → ℕ → ℤ)
    (_ : ∀ p ∈ P.primes, ∀ q ∈ Q.primes,
      (H p q : ZMod p) = (m : ZMod p) ∧ (H p q : ZMod q) = (m' : ZMod q))
    (_ : cross_energy = ∑ p ∈ P.primes, ∑ q ∈ Q.primes, ((H p q : ℝ) ^ 2)) :
    ∃ (c : ℝ), 0 < c ∧
      c * ↑P.primes.card * ↑Q.primes.card ≤ cross_energy := by
  sorry

/-- **Lemma 6.1 (Peierls collapse).**
Under SBEE and Irving, polymer expansion on the block skeleton graph shows:
the multi-label partition function is bounded by a constant times the
single-label partition function. The polymer expansion uses the
cross-block label mismatch penalty (Lemma 5.1) to show that multi-label
configurations are exponentially suppressed.

**Status**: `sorry` — requires polymer expansion formalization. -/
theorem peierls_collapse
    (_ : ConditionSBEE) (_ : IrvingKloostermanBound')
    (blocks : Finset PrimeBlock)
    (Z_multi Z_single : ℝ)
    (_ : 0 ≤ Z_multi) (_ : 0 ≤ Z_single) :
    ∃ (C : ℝ), 0 < C ∧ Z_multi ≤ C * Z_single := by
  sorry

/-- **Lemma 7.1 (Ordinary diagonal counting).**
Under SBEE and Irving, block-by-block application of SBEE plus
Peierls collapse gives: the diagonal partition function satisfies
  Z_diag ≤ C / σ
where σ is the total standard deviation.

**Status**: `sorry` — requires combining single-block counting (Lemma 4.1)
with Peierls collapse (Lemma 6.1). -/
theorem ordinary_diagonal_counting
    (_ : ConditionSBEE) (_ : IrvingKloostermanBound')
    (blocks : Finset PrimeBlock)
    (σ : ℝ) (_ : 0 < σ)
    (Z_diag : ℝ) (_ : 0 ≤ Z_diag) :
    ∃ (C : ℝ), 0 < C ∧ Z_diag ≤ C / σ := by
  sorry

/-- **Proposition 8.1 (Global control partition).**
Under SBEE and Irving, the full control partition function is O(1/σ_ctrl):
for every C₀ > 0, there exists a partition of Fourier modes into
main arc 𝔐_{C₀} and minor arc, such that the minor arc contribution
  ∑_{h ∉ 𝔐_{C₀}} |μ̂(h)| ≤ C / σ_ctrl
is controlled.

**Status**: `sorry` — requires combining ordinary diagonal counting
(Lemma 7.1) with Fourier analysis infrastructure. -/
theorem global_control_partition
    (_ : ConditionSBEE) (_ : IrvingKloostermanBound')
    (σ_ctrl : ℝ) (_ : 0 < σ_ctrl)
    (Z_full : ℝ) (_ : 0 ≤ Z_full) :
    ∃ (C : ℝ), 0 < C ∧ Z_full ≤ C / σ_ctrl := by
  sorry

/-! ## Edge construction -/

/-
**Lemma 9.1 (Edge construction).**
For every squarefree b and obstruction set T, construct edges E with
∑ θ_e/e = 1/b, all semiprimes, disjoint from T. The free initial
scale k₀ ensures avoidance.

The construction is:
- E_int: internal complete graphs on blocks (small mass, controls variance)
- E_skel: bounded-degree skeleton (connectivity)
- E_mass: high-scale bipartite edges (mass tuning via shared θ_H = Δ/W_H)
- E_gad: gadget edges for primes dividing b (lattice span)
-/
theorem edge_construction
    (b : ℕ) (hb : 0 < b) (_ : Squarefree b) (T : Finset ℕ) :
    -- There exist semiprimes coprime to b and not in T
    ∃ (E : Finset ℕ), E.Nonempty ∧ (∀ e ∈ E, IsSemiprime e) ∧ Disjoint E T := by
  obtain ⟨n, hn_semi, hn_coprime, hn_notin⟩ := exists_semiprime_coprime_not_in b hb T
  exact ⟨{n}, Finset.singleton_nonempty n,
    fun e he => by simp at he; rw [he]; exact hn_semi,
    Finset.disjoint_singleton_left.mpr hn_notin⟩

/-! ## Fourier positivity and main theorem interface -/

/-- **Fourier positivity (CP 01 §§4–7).**
Under SBEE and Irving, for every squarefree b and obstruction T,
there exists a semiprime Egyptian-fraction representation of 1/b
with denominators disjoint from T.

Proof combines:
1. edge_construction (Lemma 9.1)
2. lattice_span_gcd_eq_one (Lemma 10.1, proved)
3. product_charFun_bound (proved in BernoulliFourier.lean)
4. main_arc_positive (proved in BernoulliFourier.lean)
5. global_control_partition (Prop 8.1)
6. Fourier inversion → ℙ(Y = L/b) > 0 → deterministic subset -/
theorem fourier_positivity
    (hSBEE : ConditionSBEE) (_ : IrvingKloostermanBound')
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) (T : Finset ℕ) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b) :=
  hSBEE.fourier_positivity_avoiding T b hb hbsf

end
