# Aristotle Task: R2 Control/Gadget Disjointness

## Goal

Create a new Lean file:

```lean
RequestProject/R2ComponentDisjoint.lean
```

The task is pure finite-set / prime-factor bookkeeping.  Do **not** modify thick
upstream files.  Import the current downstream socket:

```lean
import RequestProject.R2ForbiddenBaseBudget
```

Open the usual namespaces:

```lean
open Finset BigOperators GlobalControl

noncomputable section
namespace CircleMethod
```

Build target:

```bash
lake build RequestProject.R2ComponentDisjoint
```

No `sorry`, `admit`, or new axioms.

## Mathematical Statement

The control edges are products of two primes in `blockSupport BS`.  The gadget
edges are products `r*s` with `r ∈ R` and `s ∈ S`.  If every `r ∈ R` is prime and
outside `blockSupport BS`, then no control edge can equal a gadget edge, provided
the gadget factorization is genuine.

The key theorem should be:

```lean
theorem ctrlEdges_disjoint_gadgetEdges_of_R_outside_blockSupport
    {BS : BlockSystem} {R S : Finset ℕ}
    (hRprime : ∀ r ∈ R, Nat.Prime r)
    (hRout : ∀ r ∈ R, r ∉ blockSupport BS) :
    Disjoint (ctrlEdges BS) (gadgetEdges R S) := by
  ...
```

It is okay if Lean needs an additional harmless hypothesis such as
`∀ s ∈ S, Nat.Prime s`; but try first without it.  The proof should only use
`hRprime`, `hRout`, and the fact that control-edge prime factors lie in
`blockSupport BS`.

## Helpful Lemmas To Prove

You will probably want a helper exposing the support factors of control edges:

```lean
lemma mem_ctrlEdges_support_pair
    {BS : BlockSystem} {e : ℕ} (he : e ∈ ctrlEdges BS) :
    ∃ p ∈ blockSupport BS, ∃ q ∈ blockSupport BS, e = p * q := by
  ...
```

Suggested proof:

1. Unfold `ctrlEdges`.
2. Use `Finset.mem_image` to obtain `pq ∈ ctrlPairs BS` and `e = pq.1 * pq.2`.
3. Apply `ctrlPairs_mem_blockSupport BS` to get both endpoints in
   `blockSupport BS`.

Then prove the disjointness theorem:

1. Use `rw [Finset.disjoint_left]`.
2. Suppose `e ∈ ctrlEdges BS` and `e ∈ gadgetEdges R S`.
3. From the control helper, get `e = p*q` with `p,q ∈ blockSupport BS`.
4. From `mem_gadgetEdges`, get `e = r*s` with `r ∈ R`.
5. Since `r` is prime and `r ∣ r*s = p*q`, `Nat.Prime.dvd_mul.mp` gives
   `r ∣ p` or `r ∣ q`.
6. Since `p` and `q` are prime by `blockSupport_prime BS`, divisibility implies
   equality (`Nat.prime_dvd_prime_iff_eq` is often useful).
7. Thus `r ∈ blockSupport BS`, contradicting `hRout r hr`.

## Optional Endpoint

If the main theorem compiles, also add the record-facing wrapper:

```lean
theorem r2Concrete_ctrl_gadget_disjoint_of_R_outside_blockSupport
    {T : Finset ℕ} {b : ℕ} (D : R2ConcreteData T b)
    (hRprime : ∀ r ∈ D.R, Nat.Prime r)
    (hRout : ∀ r ∈ D.R, r ∉ blockSupport D.BS) :
    Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S) := by
  exact ctrlEdges_disjoint_gadgetEdges_of_R_outside_blockSupport hRprime hRout
```

## Why This Matters

`RequestProject/R2ForbiddenBaseBudget.lean` already proves:

```lean
exists_massBatchSupply_of_basePieces_forbiddenBudget
```

It requires:

```lean
Disjoint (ctrlEdges D.BS) (gadgetEdges D.R D.S)
```

Your theorem supplies this from the natural construction condition that the
denominator primes `R` are kept outside the dyadic block support.

