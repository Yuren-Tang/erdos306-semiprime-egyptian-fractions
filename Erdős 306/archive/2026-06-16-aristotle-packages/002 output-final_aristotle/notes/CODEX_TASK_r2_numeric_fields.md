# Task: R2 Numeric/Main-Arc Field Helpers

Work in the current Lean package.  Create a new file:

```lean
RequestProject/R2NumericFields.lean
```

Import:

```lean
import RequestProject.R2AssemblyFields
```

Goal: prove abstract, reusable helper lemmas for the large-window fields
`hN`, `htw`, and `hsmall` in `ArcConstruction`.  Do not touch the minor arc and
do not attempt the final `exists_arcConstruction`.

## Required Lemmas

Use names close to the following.  Adjust statements if Lean needs a cleaner
form, but keep the mathematical content.

### 1. Main-window nonnegativity and period size

Package the hypotheses needed by `exists_mainArcFields`:

```lean
lemma mainArc_N_nonneg_of_inv_sqrt_le
    (E : Finset ℕ) (theta : ℕ → ℝ) (N : ℤ)
    (hN : (1 : ℝ) / Real.sqrt (sigmaE2 E theta) ≤ (N : ℝ)) :
    0 ≤ N
```

This should use positivity of `1 / sqrt(...)` if possible; if positivity of
`sigmaE2` is needed, state it explicitly as a hypothesis:

```lean
(hσ : 0 < Real.sqrt (sigmaE2 E theta))
```

### 2. `htw` from a uniform edge lower bound

```lean
lemma htw_of_window_edge_lower
    (E : Finset ℕ) (N : ℤ)
    (hNnonneg : 0 ≤ N)
    (hedge : ∀ e ∈ E, (10 : ℝ) * (N : ℝ) ≤ (e : ℝ)) :
    ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E,
      |(m : ℝ) / (e : ℝ)| ≤ 1 / 10
```

You may need an explicit positivity hypothesis for edges:

```lean
(he0 : ∀ e ∈ E, 0 < e)
```

### 3. `hsmall` from a cubic load bound

A flexible version is enough:

```lean
lemma hsmall_of_cubic_sum_bound
    (E : Finset ℕ) (N : ℤ)
    (hbound : ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10) :
    ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10
```

This one is trivial but gives the final assembly a stable name.

Also try a stronger useful version:

```lean
lemma hsmall_of_uniform_ratio_bound
    (E : Finset ℕ) (N : ℤ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ)
    (hratio : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E,
      |(m : ℝ) / (e : ℝ)| ≤ ρ)
    (hcard : (E.card : ℝ) * 100000 * ρ ^ 3 ≤ 1 / 10) :
    ∀ m ∈ Finset.Icc (-N) N,
      (∑ e ∈ E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10
```

### 4. Combined package

Define a structure:

```lean
structure MainArcNumericFields (E : Finset ℕ) (theta : ℕ → ℝ) (N : ℤ) where
  hN : (1 : ℝ) / Real.sqrt (sigmaE2 E theta) ≤ (N : ℝ)
  hNnonneg : 0 ≤ N
  htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E,
    |(m : ℝ) / (e : ℝ)| ≤ 1 / 10
  hsmall : ∀ m ∈ Finset.Icc (-N) N,
    (∑ e ∈ E, 100000 * |(m : ℝ) / (e : ℝ)| ^ 3) ≤ 1 / 10
```

and one constructor from the above hypotheses.

## Build

Verify only:

```bash
lake build RequestProject.R2NumericFields
```

No axiom trace is needed unless the theorem statements unexpectedly require
nonstandard assumptions.

