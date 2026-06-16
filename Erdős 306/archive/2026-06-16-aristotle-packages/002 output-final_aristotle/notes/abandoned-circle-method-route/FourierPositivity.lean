/-
# Fourier Positivity (Unconditional)

**STATUS (current phase).** `fourier_positivity_unconditional` is no longer a
`sorry`: it is now *proved* by `CircleMethod.circle_method_positivity`
(`CircleMethod.lean`, note 35 C5).  The circle-method decomposition reduces it to
the single precisely-named analytic residual
`CircleMethod.exists_arcConstruction` (the edge construction +
main/minor-arc positivity, fed by the Phase-G global control of
`GlobalControl.lean`).  The deterministic extraction layer (C0/C5) and the finite
Fourier orthogonality identity (C0) are fully proved.

The remainder of this docstring records the original proof sketch and the
dependency analysis (CP 01 §§3–7), which the new files translate.

This file isolates the analytic core of the Erdős 306
formalization. That core has been verified to be irreducible to
simpler correct sub-lemmas without formalizing substantial
Fourier-analytic infrastructure.

## Statement

For every squarefree b > 0 and every finite obstruction set T,
there exists a finite set S of distinct squarefree semiprimes,
disjoint from T, with ∑_{n∈S} 1/n = 1/b.

## Why this sorry cannot be trivially decomposed

**Failed decomposition 1 (abstract subset sum):**
The Bernoulli subset sum theorem — "given weights with gcd 1 and a
feasible Bernoulli target, a 0-1 solution exists" — is FALSE without
a lower bound on the number of weights (counterexample: w=[3,5], m=4,
gcd=1, θ=[2/3,2/5], but no subset of {3,5} sums to 4).

**Failed decomposition 2 (exceed-then-extract):**
The lemma "given semiprimes E with ∑ 1/e ≥ 1/b, extract S ⊆ E with
∑ 1/e = 1/b" is FALSE (counterexample: E={6,10}, b=5: ∑=4/15 ≥ 1/5
but no subset sums to exactly 1/5).

The actual proof requires the FULL Fourier-analytic argument with:
- Edge construction with mass tuning (CP 03 §9)
- Lattice span condition (proved in LatticeSpan.lean)
- Bernoulli Fourier bounds (proved in BernoulliFourier.lean)
- Main arc Taylor expansion (CP 01 §5)
- Minor arc bound via SBEE + global control (CP 01 §6, CP 02)
- SBEE unconditional via cross-label energy (CP 02 §2, proved
  qualitatively in CrossLabelEnergy.lean)
- Positivity conclusion (CP 01 §7)

Formalizing these requires Fourier analysis on ℤ/Lℤ, a Bernoulli
probability space, and quantitative prime distribution estimates —
infrastructure not yet available in Mathlib at the required level.

## Proof sketch (CP 01 §§3–7)

Given squarefree b > 0 and finite T:

**Step 1 (Edge construction, CP 03 §9).**
Choose initial scale k₀ > log₂(max T + 1). Build:
- Internal edges E_int: complete graphs on prime blocks
  P_k ⊆ [2^k, 2^{k+1}] for k = k₀, …, K.
- Skeleton edges E_skel: bounded-degree across blocks.
- Mass edges E_mass: high-scale bipartite edges with common
  parameter θ_H = Δ/W_H ∈ [1/3, 1/2] tuning ∑ θ_e/e = 1/b.
- Gadget edges E_gad = {r·s_r : r | b} for lattice span.
All semiprimes have both prime factors > 2^{k₀} > max T, so
they are automatically disjoint from T.

**Step 2 (Fourier inversion, CP 01 §4).**
Let P = all primes used, L = ∏ P, Y = ∑ ξ_e · L/e.
By Fourier inversion on ℤ/Lℤ:
  ℙ(Y = L/b) = (1/L) ∑_{h mod L} μ̂(h) · e(-h/b)
where μ̂(h) = ∏_{e∈E} (1 - θ_e + θ_e · e(hL/(eL))) =
              ∏ (1 - θ_e + θ_e · e(h·w_e/L))
with w_e = L/e.

**Step 3 (Main arc, CP 01 §5).**
For |m| ≤ C/σ_E, Taylor expansion:
  log μ̂(m) = 2πim/b - 2π²σ²m² + o(1).
Phase cancellation with e(-m/b):
  μ̂(m)·e(-m/b) = exp(-2π²σ²m² + o(1)).
Gaussian sum: ∑_{main} ≈ 1/σ > 0.

**Step 4 (Minor arc, CP 01 §6).**
|μ̂(h)| ≤ exp(-c·Q_E(a)) by Bernoulli bound (BernoulliFourier.lean).
Global control partition (CP 03 §8, conditional on SBEE):
  ∑_{h ∉ main} |μ̂(h)| = o_C(1/σ).

**Step 5 (SBEE unconditional, CP 02 §2).**
Cross-label divisor-energy (CrossLabelEnergy.lean) gives:
for two substantial classes C_m, C_{m'} at scale X,
  S_sub ≫ |C_m|·|C_{m'}| · min(1, |C_m|²|C_{m'}|²/(X⁴L_X⁴)).
With |C_m|·|C_{m'}| ≥ (ρN/s)² and N ≈ X/log X:
  S_sub ≫ X²/(log X)^O(1) → ∞.
For X large enough (depending on R), S_sub > R, making
Q_P(a) ≤ R impossible. SBEE is vacuously true for large blocks.

**Step 6 (Positivity, CP 01 §7).**
Main arc (≈ 1/σ > 0) dominates minor arc (= o(1/σ)):
  ℙ(Y = L/b) > 0.
Extract deterministic S ⊆ E with ∑ 1/e = 1/b.

## Dependency graph

```
fourier_positivity_unconditional
├── Edge construction (CP 03 §9)
│   └── exists_semiprime_coprime_not_in (SemiprimeInfinity.lean) ✓
├── Lattice span (CP 03 §10)
│   └── lattice_span_gcd_eq_one (LatticeSpan.lean) ✓
├── Bernoulli Fourier bound (CP 03 §1)
│   └── product_charFun_bound (BernoulliFourier.lean) ✓
├── Main arc positivity (CP 01 §5)
│   └── main_arc_positive (BernoulliFourier.lean) ✓
├── Minor arc bound (CP 01 §6)
│   ├── Global control partition (CP 03 §8)
│   │   └── SBEE chain (Lemmas 4.1–7.1)
│   └── SBEE unconditional (CP 02 §2)
│       └── cross_label_energy_pos (CrossLabelEnergy.lean) ✓
└── Deterministic extraction (CP 01 §7)
```

Items marked ✓ are proved in the project. The remaining gap is
the glue connecting these proved components through the Fourier
inversion framework on ℤ/Lℤ with a Bernoulli probability space.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.SemiprimeInfinity
import RequestProject.LatticeSpan
import RequestProject.BernoulliFourier
import RequestProject.CrossLabelEnergy
import RequestProject.CircleMethod
import RequestProject.CircleMethodAssembly

open scoped BigOperators Classical

noncomputable section

/-- **The Last Sorry: Fourier Positivity (Unconditional).**

For every squarefree b > 0 and every finite obstruction set T,
there exists a finite set S of distinct squarefree semiprimes,
disjoint from T, with ∑_{n∈S} 1/n = 1/b.

This is the full content of Erdős Problem 306 (Lichtman 2024).
See the module docstring for the complete proof sketch and
dependency analysis. -/
theorem fourier_positivity_unconditional
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b) :=
  CircleMethod.circle_method_positivity T b hb hbsf

end
