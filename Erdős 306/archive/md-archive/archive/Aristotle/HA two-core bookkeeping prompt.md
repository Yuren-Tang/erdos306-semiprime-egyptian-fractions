# Aristotle prompt: two-core bookkeeping for ambient FIE

Copy the following to Aristotle when useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306 conditional proof.

This task is **not** to prove SBEE, Fourier positivity, divisor-energy estimates, or any analytic number theory. It is a finite incidence-bookkeeping task supporting the ambient-sensitive FIE route.

Create a new file:

```text
RequestProject/TwoCoreBookkeeping.lean
```

and import the existing finite infrastructure, especially:

```lean
import RequestProject.BucketCore
import RequestProject.BucketContainer
import RequestProject.BipartiteCycles
```

If `RequestProject/PotentialTree.lean` exists from the previous run, you may import it too, but this task does not require it.

## Mathematical background

We have a finite vertex set `V`, a finite bucket set `B`, and an incidence relation

```lean
Inc : V → B → Prop
```

with `[DecidableRel Inc]`.

The key uniqueness hypothesis is:

> For any two distinct buckets `b₀ ≠ b₁`, at most one vertex is incident to both.

This abstracts the marked dual uniqueness used in the bucket argument.

## Goal 1: one-core new-bucket capacity

For a bucket core `Core : Finset B`, define the high-degree container:

```lean
def highDegInto
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (h : ℕ) : Finset V :=
  U.filter (fun v => h ≤ (Core.filter (fun c => Inc v c)).card)
```

Prove the following theorem in a division-free form:

```lean
theorem newBucket_capacity_mul_le
    {V B : Type*} [DecidableEq V] [DecidableEq B]
    (Inc : V → B → Prop) [DecidableRel Inc]
    (U : Finset V) (Core : Finset B) (n : B) (h : ℕ)
    (hn : n ∉ Core)
    (huniq : ∀ c ∈ Core, ∀ v₁ ∈ U, ∀ v₂ ∈ U,
      Inc v₁ n → Inc v₁ c → Inc v₂ n → Inc v₂ c → v₁ = v₂) :
    ((highDegInto Inc U Core h).filter (fun v => Inc v n)).card * h ≤ Core.card
```

Proof idea:

Let

```lean
S = (highDegInto Inc U Core h).filter (fun v => Inc v n)
```

Each `v ∈ S` has at least `h` incidences into `Core`, so

```lean
S.card * h ≤ ∑ v ∈ S, (Core.filter (fun c => Inc v c)).card.
```

Swap the sum over `v` and `c`. For each fixed `c ∈ Core`, the uniqueness hypothesis says at most one `v ∈ S` is incident to both `n` and `c`, so the inner count is at most `1`. Therefore the sum is at most `Core.card`.

This theorem formalizes:

$$
\#\{v\in A_h(\mathcal C): n\in\mathcal B(v)\}\cdot h\le |\mathcal C|.
$$

## Goal 2: two-core edge lower bound

Define the set of bucket pairs realized by a residual vertex:

```lean
def twoCoreEdges
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Core₀ Core₁ : Finset B) : Finset (B × B) :=
  (Core₀.product Core₁).filter
    (fun bc => ∃ v ∈ Γ, Inc v bc.1 ∧ Inc v bc.2)
```

Prove:

```lean
theorem twoCore_edges_lower_mul
    {V B : Type*} [DecidableEq V] [DecidableEq B]
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Γ : Finset V) (Core₀ Core₁ : Finset B) (h₀ h₁ : ℕ)
    (hdeg₀ : ∀ v ∈ Γ, h₀ ≤ (Core₀.filter (fun c => Inc v c)).card)
    (hdeg₁ : ∀ v ∈ Γ, h₁ ≤ (Core₁.filter (fun c => Inc v c)).card)
    (huniq : ∀ c₀ ∈ Core₀, ∀ c₁ ∈ Core₁, ∀ v₁ ∈ Γ, ∀ v₂ ∈ Γ,
      Inc v₁ c₀ → Inc v₁ c₁ → Inc v₂ c₀ → Inc v₂ c₁ → v₁ = v₂) :
    Γ.card * h₀ * h₁ ≤ (twoCoreEdges Inc Γ Core₀ Core₁).card
```

Proof idea:

Each `v ∈ Γ` contributes at least

```lean
h₀ * h₁
```

pairs `(c₀,c₁) ∈ Core₀ × Core₁` incident to `v`. The uniqueness hypothesis says that the pair-sets contributed by distinct vertices are disjoint. Hence the union, which is contained in `twoCoreEdges`, has cardinal at least `Γ.card * h₀ * h₁`.

This theorem formalizes:

$$
e(G_\Gamma(\mathcal C_0,\mathcal C_1))\ge |\Gamma|h_0h_1.
$$

## Goal 3: generated core gives many seed neighbours

This goal is also high priority if feasible.

Define the seed-neighbour set:

```lean
def seedNeighbours
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Buckets : Finset B) (F : Finset V) (v : V) : Finset V :=
  F.filter (fun f => ∃ b ∈ Buckets, Inc v b ∧ Inc f b)
```

Use the existing `generatedBuckets` definition from `BucketContainer.lean`, or
redefine it if needed:

```lean
def generatedBuckets
    (Inc : V → B → Prop) [DecidableRel Inc]
    (F : Finset V) (Buckets : Finset B) : Finset B :=
  Buckets.filter (fun b => ∃ f ∈ F, Inc f b)
```

Prove:

```lean
theorem highDeg_generatedCore_le_seedNeighbours
    {V B : Type*} [DecidableEq V] [DecidableEq B]
    (Inc : V → B → Prop) [DecidableRel Inc]
    (Buckets : Finset B) (F : Finset V) (v : V) (h : ℕ)
    (hdeg : h ≤ ((generatedBuckets Inc F Buckets).filter (fun b => Inc v b)).card)
    (huniq : ∀ f ∈ F, ∀ b₁ ∈ Buckets, ∀ b₂ ∈ Buckets,
      Inc v b₁ → Inc f b₁ → Inc v b₂ → Inc f b₂ → b₁ = b₂) :
    h ≤ (seedNeighbours Inc Buckets F v).card
```

Proof idea:

Each bucket in `generatedBuckets Inc F Buckets` incident to `v` has at least one
seed `f ∈ F` incident to it. Choose one such seed. The uniqueness hypothesis says
the same seed cannot be assigned to two distinct buckets, because that would make
`v` and `f` share two buckets. Therefore the number of seed neighbours is at
least the number of generated-core buckets incident to `v`, and hence at least
`h`.

This theorem formalizes the paper-side implication:

$$
v\in A_h(N(F))
\Longrightarrow
\#\{f\in F:v\sim_\tau f\}\ge h.
$$

## Goal 4: optional dense rectangle lower bound

If practical, add a theorem connecting edge density to ordered rectangle count in a bipartite graph. A division-free or real-valued version is acceptable.

One useful target is:

```lean
def bipEdgeSet
    (Adj : A → B → Prop) [DecidableRel Adj]
    (X : Finset A) (Y : Finset B) : Finset (A × B) :=
  (X.product Y).filter (fun xy => Adj xy.1 xy.2)
```

Then prove a convexity-style lower bound of the form:

```text
if |E| ≥ δ |X||Y|, then rectangleCount Adj X Y is large.
```

Do not get stuck on sharp constants. A clean lemma with extra hypotheses, natural-number floors, or rational/real density variables is fine. If this is too much for Lean in one run, leave it out and complete Goals 1--3 with no `sorry`.

## Expected result

- `RequestProject/TwoCoreBookkeeping.lean` compiles with no `sorry`.
- Goals 1 and 2 are mandatory.
- Goal 3 is strongly preferred.
- Goal 4 is optional.
- Please include a short summary explaining how these theorems support the paper-side statement:

$$
\text{persistent second saturation}
\Longrightarrow
\text{dense two-core bucket-pair graph and many seed common-neighbours}.
$$

Again: do not introduce SBEE as an axiom and do not work on Fourier positivity. This is purely finite incidence bookkeeping.
