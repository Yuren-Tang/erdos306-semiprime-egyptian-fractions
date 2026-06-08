# Aristotle prompt: cluster-cover bookkeeping

Copy this to Aristotle after `SeededWitnessMatrix.lean`, if useful.

---

Please continue from the existing Lean 4 / Mathlib project for the Erdős 306 conditional proof.

This task is **not** to prove SBEE, divisor-energy estimates, prime estimates, or the reciprocal-cluster arithmetic bound. It only formalizes a finite set-system lemma needed for the current reciprocal-cluster selection step.

Create a new file:

```text
RequestProject/ClusterCoverBookkeeping.lean
```

Useful imports:

```lean
import Mathlib
```

## Background

The paper-side situation is:

- `U` is a finite universe of possible seed vertices;
- `Clusters : Finset (Finset U)` is a finite family of clusters;
- a seed pool `F : Finset U` is bad if every `k`-tuple or every `k`-subset of `F` lies inside some cluster;
- if a fixed `(k-1)`-subset `T ⊆ F` belongs to only a few clusters, then all of `F` is covered by the union of those clusters plus `T`.

This is pure finite bookkeeping. The arithmetic task of bounding cluster codegrees remains outside Lean.

## Goal 1: cluster membership and cover definitions

Define:

```lean
def coveredBySomeCluster
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (S : Finset U) : Prop :=
  ∃ C ∈ Clusters, S ⊆ C

def clustersContaining
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (T : Finset U) : Finset (Finset U) :=
  Clusters.filter (fun C => T ⊆ C)

def unionClusters
    {U : Type*} [DecidableEq U]
    (Cs : Finset (Finset U)) : Finset U :=
  Cs.biUnion id
```

You may adjust definitions if Mathlib prefers another shape.

## Goal 2: one-set extension cover lemma

Prove:

```lean
theorem covered_extension_subset_unionContaining
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U)
    (hT : T ⊆ F)
    (hcover : ∀ v ∈ F, coveredBySomeCluster Clusters (insert v T)) :
    F ⊆ T ∪ unionClusters (clustersContaining Clusters T)
```

Proof idea:

Take `v ∈ F`. If `v ∈ T`, done. Otherwise `insert v T` is contained in some cluster `C`. Then `T ⊆ C`, so `C ∈ clustersContaining Clusters T`, and hence `v` lies in the union of clusters containing `T`.

This is the key finite lemma:

$$
\bigl[\forall v\in F,\ T\cup\{v\}\subset C_v\bigr]
\Longrightarrow
F\subset T\cup\bigcup_{C\supset T}C.
$$

## Goal 3: cardinal cover bound

Assume every cluster has size at most `L`, and at most `R` clusters contain `T`.
Prove a cardinal consequence such as:

```lean
theorem card_le_of_extension_cover
    {U : Type*} [DecidableEq U]
    (Clusters : Finset (Finset U)) (F T : Finset U) (L R : ℕ)
    (hT : T ⊆ F)
    (hcover : ∀ v ∈ F, coveredBySomeCluster Clusters (insert v T))
    (hR : (clustersContaining Clusters T).card ≤ R)
    (hL : ∀ C ∈ clustersContaining Clusters T, C.card ≤ L) :
    F.card ≤ T.card + R * L
```

Constants do not need to be sharp. A slightly different bound, e.g.
`F.card ≤ (T ∪ unionClusters ...).card` plus
`(unionClusters ...).card ≤ R * L`, is also fine.

## Goal 4: k-subset corollary if practical

If practical, add a corollary:

If `T ⊆ F` has size `k-1` and every `k`-set `S ⊆ F` is covered by some cluster,
then `hcover : ∀ v ∈ F, coveredBySomeCluster Clusters (insert v T)` follows.

You may formulate this with `T.card = k - 1` and `v ∉ T`, or avoid cardinal
bookkeeping and state the corollary directly with the `insert v T` hypothesis.
Goal 2 and Goal 3 are the priority.

## Expected result

- `RequestProject/ClusterCoverBookkeeping.lean` compiles with no `sorry`.
- No SBEE, no number theory, no analytic assumptions.
- The final summary should say this supports the paper-side reciprocal-cluster selection step:

$$
\text{all seed tuples singular}
\Longrightarrow
\text{seed pool covered by few clusters, once cluster codegrees are bounded}.
$$
