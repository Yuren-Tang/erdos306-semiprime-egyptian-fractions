# Codex Task: R2 Base-Load Upper Socket

## Context

Work in the Lean project:

```text
/Users/david/erdos-lean-build
```

The current mass-batch branch has been reduced to one explicit condition:

```lean
D.baseLoad < 3 / (2 * (b : ℝ))
```

for `D : R2ConcreteData T b`, where

```lean
D.baseLoad =
  R2ConcreteData.recipLoad (ctrlEdges D.BS ∪ gadgetEdges D.R D.S)
```

Recent completed leaves:

```lean
RequestProject/R2ComponentDisjoint.lean
RequestProject/R2EventualScale.lean
RequestProject/R2ForbiddenBaseBudget.lean
```

Do not work on G5/G7/C.  Do not rewrite the thick final assembly spine.  This
task is about the base-load upper interface only.

## Goal

Create a thin Lean leaf, preferably:

```lean
RequestProject/R2BaseLoadUpper.lean
```

Import as narrowly as possible.  A reasonable starting import is:

```lean
import RequestProject.R2ComponentDisjoint
```

The target should build with:

```bash
lake build RequestProject.R2BaseLoadUpper
```

No `sorry`, `admit`, or new theorem-sized fake proofs.  If a genuinely analytic
estimate is needed, state it as a clearly named axiom/input with an honest
docstring, then prove the downstream Lean consequences from that input.

## Mathematical Diagnosis

The control edges are:

```lean
ctrlPairs BS =
  ⋃ k ∈ Icc BS.k0 BS.K, internalPairs BS k
  ∪ ⋃ k ∈ Ico BS.k0 BS.K, bipartitePairs BS k

internalPairs BS k = {(p,q) ∈ BS.P k × BS.P k : p < q}
bipartitePairs BS k = BS.P k × BS.P (k+1)
```

The first-power reciprocal load is therefore morally bounded by

```text
Σ_k (Σ_{p∈P_k} 1/p)^2
+ Σ_k (Σ_{p∈P_k} 1/p)(Σ_{q∈P_{k+1}} 1/q).
```

A crude cardinality/window bound is too weak.  We need a dyadic prime
reciprocal upper estimate, e.g. something like:

```lean
∃ C K0, 0 < C ∧ ∀ k ≥ K0,
  ∑ p ∈ dyadicBlock k, (1 : ℝ) / (p : ℝ) ≤ C / (k : ℝ)
```

or a direct eventual bound on the above control sum.  Existing
`dyadic_prime_density` and `dyadic_mertens_cumulative` are lower-bound inputs;
they do not imply this upper bound.

The gadget part should be kept separate:

```lean
R2ConcreteData.recipLoad (gadgetEdges D.R D.S)
```

Do not hide control and gadget under one opaque assumption unless you also
provide a split theorem.  The point is to keep the future construction honest.

## Desired Lean Endpoints

Names can vary, but try to provide these or close analogues.

### 1. Base-load split wrapper

Use existing `baseLoad_eq_ctrl_add_gadget_of_disjoint` and
`r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport` to prove:

```lean
theorem baseLoad_eq_ctrl_add_gadget_of_R_outside
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS) :
    D.baseLoad =
      R2ConcreteData.recipLoad (ctrlEdges D.BS) +
        R2ConcreteData.recipLoad (gadgetEdges D.R D.S)
```

### 2. Component-budget implication

This finite arithmetic endpoint is important:

```lean
structure R2BaseLoadBudget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b) where
  Cctrl : ℝ
  Cgadget : ℝ
  hctrl : R2ConcreteData.recipLoad (ctrlEdges D.BS) ≤ Cctrl
  hgadget : R2ConcreteData.recipLoad (gadgetEdges D.R D.S) ≤ Cgadget
  hsum : Cctrl + Cgadget < 3 / (2 * (b : ℝ))
```

and:

```lean
theorem baseLoad_lt_of_budget
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS)
    (B : R2BaseLoadBudget D) :
    D.baseLoad < 3 / (2 * (b : ℝ))
```

### 3. Control-side exact finite decomposition

If feasible, prove an exact or upper-bound decomposition for the control
reciprocal load:

```lean
R2ConcreteData.recipLoad (ctrlEdges BS)
  ≤
    (sum over internalPairs BS k of 1/(p*q))
    + (sum over bipartitePairs BS k of 1/(p*q))
```

Even better, prove the factorized upper bounds:

```lean
∑ pq ∈ internalPairs BS k, 1 / ((pq.1 : ℝ) * pq.2)
  ≤ (∑ p ∈ BS.P k, 1 / (p : ℝ)) ^ 2

∑ pq ∈ bipartitePairs BS k, 1 / ((pq.1 : ℝ) * pq.2)
  =
    (∑ p ∈ BS.P k, 1 / (p : ℝ)) *
    (∑ q ∈ BS.P (k+1), 1 / (q : ℝ))
```

For the internal inequality, exact equality with `p<q` has a factor `1/2`, but
the square upper bound is sufficient and easier.

### 4. Optional analytic input socket

If you can cleanly formulate the dyadic reciprocal upper input and prove the
control-load eventual smallness from it, do so.  A direct input is acceptable if
it is honest:

```lean
axiom dyadic_control_recipLoad_eventually_small :
  ∀ ε : ℝ, 0 < ε →
    ∃ k0min : ℕ, ∀ BS : BlockSystem, k0min ≤ BS.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS) ≤ ε
```

If using this direct input, prove the bridge:

```lean
theorem exists_k0_controlLoad_lt
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k0min : ℕ, ∀ BS : BlockSystem, k0min ≤ BS.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS) ≤ ε
```

This is not meant to be the final analytic proof, but it names the exact
analytic socket and lets the rest of R2 proceed conditionally.

## Build Discipline

Do not run `lake build` after every tiny edit.  Work locally, then build the
single new target when the file is coherent.  Poll at minute scale; many builds
take 3-5 minutes on this project.  Avoid touching thick upstream files unless
absolutely necessary.

## Deliverable

Report:

- new file(s);
- theorem names;
- whether `lake build RequestProject.R2BaseLoadUpper` is green;
- whether any new axiom/input was introduced, with its exact name and statement;
- no axiom traces are needed unless the build is unexpectedly suspicious.

