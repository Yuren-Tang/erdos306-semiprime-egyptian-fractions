# Aristotle prompt: adaptive cluster selection bookkeeping

Copy this to Aristotle after `ClusterCoverBookkeeping.lean`, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306 conditional proof.

This task is **not** to prove SBEE, divisor-energy estimates, prime estimates,
or reciprocal-cluster codegree bounds. It formalizes finite selection and
incidence bookkeeping around the cluster-cover lemma.

Create a new file:

```text
RequestProject/AdaptiveClusterSelection.lean
```

Useful imports:

```lean
import Mathlib
import RequestProject.ClusterCoverBookkeeping
```

## Background

`ClusterCoverBookkeeping.lean` proves that if a fixed set `T` has low cluster
codegree, and every one-point extension `insert v T` is covered by some cluster,
then the seed pool `F` is covered by few clusters.

The paper-side use now needs a clean finite dichotomy:

1. either there is a good `k`-set of seeds not covered by any cluster;
2. or some `(k-1)`-set has low codegree, so `ClusterCoverBookkeeping` covers the
   seed pool;
3. or every `(k-1)`-set has high codegree, producing many cluster--subset
   incidences that must be ruled out by arithmetic.

Please formalize this finite framework.

## Goal 1: cluster codegree

Define:

```lean
def clusterCodegree
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (T : Finset U) : ℕ :=
  (clustersContaining Clusters T).card
```

and prove the obvious equivalence:

```lean
clusterCodegree Clusters T = (clustersContaining Clusters T).card
```

or make it reducible by definition.

## Goal 2: good tuple / all-covered dichotomy

Define:

```lean
def allKSubsetsCovered
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ) : Prop :=
  ∀ S : Finset U, S ⊆ F → S.card = k → coveredBySomeCluster Clusters S
```

Define:

```lean
def hasGoodKSubset
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ) : Prop :=
  ∃ S : Finset U, S ⊆ F ∧ S.card = k ∧ ¬ coveredBySomeCluster Clusters S
```

Prove:

```lean
theorem good_or_allKSubsetsCovered
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (k : ℕ) :
    hasGoodKSubset Clusters F k ∨ allKSubsetsCovered Clusters F k
```

This is classical logic but useful as an interface.

## Goal 3: low-codegree cover dichotomy for a chosen T

Prove a theorem of the following shape:

```lean
theorem allCovered_lowCodegree_gives_card_bound
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U) (k L R : ℕ)
    (hTsub : T ⊆ F)
    (hTcard : T.card + 1 = k)
    (hall : allKSubsetsCovered Clusters F k)
    (hR : clusterCodegree Clusters T ≤ R)
    (hL : ∀ C ∈ clustersContaining Clusters T, C.card ≤ L) :
    F.card ≤ T.card + R * L
```

Use `ksubset_cover_gives_extension_cover` and
`card_le_of_extension_cover'` from `ClusterCoverBookkeeping.lean`.

## Goal 4: incidence ledger for high codegree

Define the incidence count between `(k-1)`-subsets of `F` and clusters:

```lean
def subsetClusterIncidence
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (m : ℕ) : ℕ :=
  ∑ T in F.powerset.filter (fun T => T.card = m),
    clusterCodegree Clusters T
```

Prove lower bound:

```lean
theorem incidence_lower_of_all_high_codegree
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F : Finset U) (m R : ℕ)
    (hhigh : ∀ T, T ⊆ F → T.card = m → R ≤ clusterCodegree Clusters T) :
    (F.powerset.filter (fun T => T.card = m)).card * R
      ≤ subsetClusterIncidence Clusters F m
```

Then prove the double-counting identity or upper bound:

```lean
theorem incidence_eq_sum_cluster_subsets
    ...
```

with a statement equivalent to:

$$
\sum_{\substack{T\subset F\\ |T|=m}}
\#\{C:T\subset C\}
=
\sum_{C\in\mathrm{Clusters}}
\#\{T\subset F\cap C: |T|=m\}.
$$

If exact equality is hard, prove the upper bound:

```lean
subsetClusterIncidence Clusters F m
  ≤ ∑ C in Clusters, ((F ∩ C).powerset.filter (fun T => T.card = m)).card
```

Equality is preferred, but an upper bound is enough.

## Goal 5: optional cardinal upper bound

If every cluster intersects `F` in at most `L` points, prove:

```lean
subsetClusterIncidence Clusters F m
  ≤ Clusters.card * Nat.choose L m
```

or a comparable bound using powerset-card lemmas.

## Expected result

- `RequestProject/AdaptiveClusterSelection.lean` compiles with no `sorry`.
- Goals 1--4 are most important.
- Goal 5 is optional but useful.
- No number theory or SBEE.

Paper-side meaning:

$$
\text{no good tuple}
\Longrightarrow
\text{low-codegree cover or high-codegree incidence mass}.
$$

The arithmetic reciprocal-cluster estimate will be plugged into the
high-codegree incidence mass.
