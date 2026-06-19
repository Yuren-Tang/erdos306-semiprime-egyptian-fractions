# R2 Extra Support Bookkeeping Task

Back to [[46 R2 Construction Design - Multiplicity Is Not Enough]].

This is a bounded task suitable for Aristotle or another Codex.  Do **not**
attempt `exists_arcConstruction`.  The goal is only to strengthen
`RequestProject/ArcConstructionExtra.lean` with finite support and divisibility
bookkeeping needed by the next R2 minor-arc interface.

## Context

Already available:

- `RequestProject/ArcConstruction.lean`
- `RequestProject/ArcConstructionExtra.lean`
- `RequestProject/FiberCount.lean`

Current definitions in `ArcConstructionExtra.lean`:

```lean
def edgePrimeSupport (E : Finset ℕ) : Finset ℕ :=
  E.biUnion Nat.primeFactors

def extraPrimeSupport (BS : BlockSystem) (E : Finset ℕ) : Finset ℕ :=
  edgePrimeSupport E \ blockSupport BS
```

Current proved lemmas:

```lean
mem_edgePrimeSupport
extraPrimeSupport_subset_edgePrimeSupport
extraPrimeSupport_disjoint_blockSupport
semiprime_dvd_edgePrimeSupport_prod
```

## Task

Extend `RequestProject/ArcConstructionExtra.lean`.  Keep the file sorry-free.
Use only standard axioms.

### 1. Basic support lemmas

Prove:

```lean
lemma mem_extraPrimeSupport (BS : BlockSystem) (E : Finset ℕ) (p : ℕ) :
    p ∈ extraPrimeSupport BS E ↔ p ∈ edgePrimeSupport E ∧ p ∉ blockSupport BS

lemma edgePrimeSupport_mono {E F : Finset ℕ} (hEF : E ⊆ F) :
    edgePrimeSupport E ⊆ edgePrimeSupport F

lemma edgePrimeSupport_union (E F : Finset ℕ) :
    edgePrimeSupport (E ∪ F) = edgePrimeSupport E ∪ edgePrimeSupport F

lemma edgePrimeSupport_insert (e : ℕ) (E : Finset ℕ) :
    edgePrimeSupport (insert e E) = Nat.primeFactors e ∪ edgePrimeSupport E
```

These should be mostly `simp [edgePrimeSupport, extraPrimeSupport]`.

### 2. All semiprime edges divide the support product

Package the existing one-edge lemma:

```lean
lemma all_edges_dvd_edgePrimeSupport_prod
    (E : Finset ℕ) (hsemi : ∀ e ∈ E, IsSemiprime e) :
    ∀ e ∈ E, e ∣ ∏ p ∈ edgePrimeSupport E, p
```

This is just `semiprime_dvd_edgePrimeSupport_prod`.

### 3. Control-edge support lies in block support

Prove:

```lean
lemma edgePrimeSupport_ctrlEdges_subset_blockSupport (BS : BlockSystem) :
    edgePrimeSupport (ctrlEdges BS) ⊆ blockSupport BS
```

Proof idea:

1. Take `r ∈ edgePrimeSupport (ctrlEdges BS)`.
2. Then `r ∈ Nat.primeFactors e` for some `e ∈ ctrlEdges BS`.
3. Unfold `ctrlEdges`: `e = pq.1 * pq.2` for `pq ∈ ctrlPairs BS`.
4. Use `ctrlPairs_distinct_primes BS hpq` to get both primes and membership
   data.  If that lemma does not expose block-support membership directly, use
   the definition of `ctrlPairs` and `blockSupport`.
5. Since `r ∈ Nat.primeFactors (pq.1 * pq.2)`, `r ∣ pq.1 * pq.2`; because `r`
   is prime, `r ∣ pq.1` or `r ∣ pq.2`; by prime divisibility, `r = pq.1` or
   `r = pq.2`.  Either coordinate lies in `blockSupport BS`.

This lemma is important: it says the control skeleton has no extra primes.

### 4. A period divisibility helper

Define, if useful:

```lean
def primeSupportPeriod (b : ℕ) (P : Finset ℕ) : ℕ :=
  b * ∏ p ∈ P, p
```

Prove:

```lean
lemma edge_dvd_primeSupportPeriod_of_mem_support
    {b : ℕ} {P : Finset ℕ} {e : ℕ}
    (hdiv : e ∣ ∏ p ∈ P, p) :
    e ∣ primeSupportPeriod b P

lemma semiprime_edge_dvd_primeSupportPeriod
    {b : ℕ} {E : Finset ℕ} {e : ℕ}
    (he : e ∈ E) (hsemi : IsSemiprime e) :
    e ∣ primeSupportPeriod b (edgePrimeSupport E)
```

The second is `semiprime_dvd_edgePrimeSupport_prod` followed by the first.

### 5. Fiber-count alias

In a small section importing `RequestProject.FiberCount`, add an alias theorem
if imports permit:

```lean
theorem blockSupport_frequency_fiber_card_le
    (BS : BlockSystem) (L M : ℕ)
    (hL : L = M * ∏ p ∈ blockSupport BS, p) :
    ∀ a : GlobalAssignment BS,
      ((Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)).card ≤ M :=
  mainArc_fiber_card_le BS L M hL
```

If this creates an import cycle or slows the file, put it in a new file
`RequestProject/ArcConstructionExtraFiber.lean`.

## Deliverable

Return:

1. files changed;
2. exact theorem names proved;
3. `lake build RequestProject.ArcConstructionExtra` result;
4. if you add `ArcConstructionExtraFiber.lean`, also build that file;
5. `#print axioms` for the new nontrivial theorems, especially
   `edgePrimeSupport_ctrlEdges_subset_blockSupport`.
