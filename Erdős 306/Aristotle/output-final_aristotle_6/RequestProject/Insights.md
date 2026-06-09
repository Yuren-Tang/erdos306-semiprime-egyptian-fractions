# Structural Insights: Patterns and Generalizations

This document records the deeper mathematical patterns that emerge
from the formalized combinatorial infrastructure, and the generalizations
implemented in `GeneralizedRankOne.lean` and `FisherCounting.lean`.

---

## 1. Rank-One Rigidity is the Discrete PDE Theorem

**Original:** `RankOneRigidity.lean` — over ℤ.
**Generalized:** `GeneralizedRankOne.lean` — over any `AddCommGroup G`.

The condition `a(x,y) - a(x,y') - a(x',y) + a(x',y') = 0` is the
discrete analogue of the mixed partial derivative equation

$$\frac{\partial^2 f}{\partial x \, \partial y} = 0$$

whose solutions in classical analysis are exactly the **additively
separable** functions $f(x,y) = g(x) + h(y)$.  Our theorem is the
exact discrete version, and it holds in maximal generality: any
additive abelian group, any types X and Y, no finiteness needed.

The `iff` version (`mixedSecondZero_iff`) gives a clean
characterization:

> A function $a : X \times Y \to G$ has vanishing mixed second
> differences iff it is additively separable.

This is the **discrete PDE characterization theorem**.

### Why AddCommGroup is the right level

- `AddCommGroup` is needed for both directions: the forward direction
  uses subtraction (`a x₀ y - a x₀ y₀`), the converse uses that
  addition is commutative.
- `Ring` or `Field` structure is not needed — the proofs use only
  `module` and `abel`, not `ring`.
- This means the theorem applies to ℤ, ℚ, ℝ, ℂ, `ZMod n`,
  arbitrary modules, and any other abelian group, at zero additional
  cost.

### Connection to the SBEE argument

In the SBEE bucket-container argument, CRT residue assignments on
products of prime blocks produce functions $a : P_k \times P_\ell \to
\mathbb{Z}/q\mathbb{Z}$.  The generalized theorem applies directly
to these modular-arithmetic-valued functions on products, giving additive
structure over `ZMod q` without needing to lift to ℤ first.

---

## 2. The Marked Dual Large Sieve is Fisher Counting

**Original:** `BucketCore.lean`, `marked_dual_large_sieve`.
**Abstracted:** `FisherCounting.lean`, `pair_disjoint_choose_bound`.

The `marked_dual_large_sieve` looks specific to its setting — marked
congruences, prime blocks, label types.  But strip away the notation
and the theorem says:

> If you have a family of subsets {S_i} of a finite set U, and no
> unordered pair {u,v} appears in more than one S_i, then
> $\sum_i \binom{|S_i|}{2} \le \binom{|U|}{2}$.

This is **Fisher's counting inequality** — the pair version of the
principle that packing non-overlapping objects into a container gives a
volume bound.

### The proof in three lines

1. The offDiag sets `{(u,v) : u,v ∈ S_i, u ≠ v}` are pairwise disjoint.
2. Their union ⊆ offDiag(U).
3. Divide by 2 to convert from ordered to unordered pairs.

The entire structure of `MC p t n`, the product index `Ps × Ts`, and
the specific form of the off-diagonal uniqueness hypothesis — all of
this is just instantiation of the abstract principle.

### The unused `_hdiag` hypothesis

The original `marked_dual_large_sieve` carries a **diagonal uniqueness**
hypothesis `_hdiag` that is not used by the proof (hence the underscore
prefix).  The `marked_dual_large_sieve_from_fisher` in `FisherCounting.lean`
makes this explicit: the bound holds under off-diagonal uniqueness alone.

The diagonal hypothesis may be needed elsewhere (e.g., to bound the
diagonal contribution to the quadratic energy), but for the pure
pair-counting inequality, it is redundant.

### Connection to the large sieve inequality

The classical (analytic) large sieve inequality

$$\sum_{q \le Q} \sum_{\substack{a \bmod q \\ \gcd(a,q)=1}} \left|\sum_{n \le N} a_n \, e(an/q)\right|^2 \le (N + Q^2 - 1) \sum_{n \le N} |a_n|^2$$

shares the same combinatorial core: each "resonance" between two
integers $n_1, n_2$ is witnessed by at most one pair $(a, q)$.  The
discrete Fisher inequality is the finite combinatorial skeleton of this
analytic principle.

---

## 3. Double Counting is Sum-Swap

Three separate theorems in the project are all instances of
`Finset.sum_comm` — the interchange of summation order:

| File | Theorem | What it counts |
|------|---------|----------------|
| `BucketCore` | `bucketIncidenceMass_eq_sum_degrees` | Incidences by bucket vs. by vertex |
| `BucketFingerprint` | `incidenceMass_eq_sum_contributions` | Same, in the fingerprint language |
| `BipartiteCycles` | `ordered_double_counting` | Ordered pairs sharing a neighbour |

In each case, the identity has the form

$$\sum_{b \in B} f(b) = \sum_{v \in V} g(v)$$

where $f(b)$ counts vertices incident to bucket $b$, and $g(v)$ counts
buckets incident to vertex $v$.  This is the **bipartite double-counting
identity**, also known as the **handshaking lemma** in graph theory.

The first two are even definitionally equal (recorded by
`incidenceMass_eq_bucketIncidenceMass` in `BucketBudget`).

---

## 4. Averaging is the First Moment Method

Two theorems use the same averaging / pigeonhole principle:

| Theorem | Statement |
|---------|-----------|
| `exists_vertex_above_average` | ∃ vertex with contribution ≥ average |
| `exists_subset_sum_ge` | ∃ top-r subset with sum ≥ r × average |

Both are instances of the **first moment method**: if the average of a
nonneg function is $\mu$, then some element achieves $\ge \mu$.

The second (`exists_subset_sum_ge`) is the iterated / greedy version:
pick the top element, remove it, repeat.  This is a **deterministic
replacement for the probabilistic method** — instead of random sampling,
greedy selection gives the same order-of-magnitude guarantee.

---

## 5. Budget Bound is Mass Conservation

The `budget_bound_combined` theorem

$$\text{rounds} \times m_{\min} \le |U| \times M_{\max}$$

is an instance of the general principle:

> If you pack $k$ disjoint items, each of mass $\ge m$, into a
> container of $n$ slots each of capacity $\le M$, then $k \cdot m
> \le n \cdot M$.

This is **mass conservation** applied to the incidence graph: the total
incidence mass is bounded above (by vertex degree) and below (by the
sum of core masses).  The same principle appears in:

- **Turán-type counting**: bounding the number of dense subgraphs.
- **Energy methods**: total energy = sum of local energies ≤ global bound.
- **The probabilistic method**: expected value bounds feasibility.

---

## 6. Summary Table of Generalizations

| Component | Original scope | Generalized scope | File |
|-----------|---------------|-------------------|------|
| Rank-one rigidity | ℤ | Any AddCommGroup | `GeneralizedRankOne.lean` |
| Marked dual large sieve | MC / Ps×Ts with `_hdiag` | Pair-disjoint families, no `_hdiag` | `FisherCounting.lean` |

Both generalizations are **costless**: the generalized proofs are no
longer or more complex than the originals.  They are also **strictly
stronger**: every application of the original theorems can use the
generalized versions instead.

---

## 7. What Remains Domain-Specific

Not everything in the project admits clean generalization:

- The **greedy fingerprint** (`greedy_fingerprint`) depends on the
  specific interaction between `capturedMass` and `incidenceMass`.
  While the underlying `exists_subset_sum_ge` is general, the
  fingerprint-to-mass coupling is application-specific.

- The **edge construction** and **Fourier positivity** are inherently
  number-theoretic; they cannot be abstracted to a purely combinatorial
  setting.

- The **IsSemiprime** definition and the **necessity of squarefree
  denominators** are arithmetic facts that resist abstraction.

The combinatorial infrastructure (double counting, Fisher inequality,
budget bound, rank-one rigidity) forms a **portable toolkit** that
could be reused in other incidence-geometry or additive-combinatorics
proofs.  The number-theoretic components remain tied to the specific
problem of Egyptian fractions with semiprime denominators.
