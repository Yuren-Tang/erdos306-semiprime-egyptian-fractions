# G5 Cover Layer - Local Proof Memo

Back to [[00 README]]. This note records the current local reduction of the
`global_levelset` proof after [[40 G5 Endgame - Remaining Holes Quartered]].
It is meant as a working proof script for us and as a translation guide for
Aristotle.

## 0. Engineering Point

Local `import RequestProject.GlobalControl` is currently slow enough that
small interactive checks should not be done by repeatedly rebuilding
`GlobalControl.lean`. The better layout is:

1. keep the proved core in `GlobalControl.lean`;
2. develop G5 helper lemmas in small files importing it;
3. only splice the final proved lemmas back into `GlobalControl.lean`, or let
   `global_levelset` import a helper file once the helper file is stable.

The new local helper `RequestProject/GlobalControlG5Data.lean` follows the
total-function interface of `fiber`: shell data has type `ℕ → ℕ`, label data
has type `ℕ → ℤ`. This avoids repeatedly proving that dependent-pi data agrees
with its zero-extension.

## 1. Data Layer

Use total data:

```lean
admH       : Finset (Finset ℕ)
admB       : Finset (Finset ℕ)
admShells  : Finset (ℕ → ℕ)
admLabels  : Finset (ℕ → ℤ)
```

where:

- `admH` is the powerset of `Finset.Icc BS.k0 BS.K`, filtered by
  `∑ k ∈ H, Rw c2 k ≤ R`;
- `admB` is the powerset of `Finset.Ico BS.k0 BS.K`, filtered by
  `∑ k ∈ B, Pifloor BS e0 k ≤ R`;
- `admShells` is the image of the dependent pi over `[k0,K]`, extended by zero
  outside `[k0,K]`, and filtered by
  `∑ k ∈ Finset.Icc BS.k0 BS.K, (v k : ℝ) ≤ R` and
  `k ∈ H -> Rw c2 k ≤ (v k : ℝ) + 1`;
- `admLabels` is the image of the dependent pi over `segStarts BS H B`,
  extended by zero outside `segStarts BS H B`.

The initial label window must be

```lean
L0 BS R = ⌈(7 : ℝ) * Real.sqrt R / sigmaP (BS.P BS.k0)⌉
```

not the local `labelRange`.

## 2. Cover Lemma

The clean target is:

```lean
lemma cover_card_le
    (BS : BlockSystem) (c2 e0 R : ℝ) :
    ((Finset.univ.filter
      (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ)
      ≤
    ∑ H ∈ admH BS c2 R,
    ∑ B ∈ admB BS e0 R,
    ∑ v ∈ admShells BS c2 R H,
    ∑ ell ∈ admLabels BS c2 R H B,
      ((fiber BS H B v ell).card : ℝ)
```

Do not prove disjointness. Use only covering.

First prove the generic finite lemma:

```lean
lemma card_le_sum_fibers_of_cover
    (S : Finset α) (I : Finset ι) (F : ι → Finset α)
    (hcover : S ⊆ I.biUnion F) :
    S.card ≤ ∑ i ∈ I, (F i).card
```

Proof: `S.card ≤ (I.biUnion F).card` by `Finset.card_le_card hcover`, then
`(I.biUnion F).card ≤ ∑ i ∈ I, (F i).card` by `Finset.card_biUnion_le`.

For four levels, either apply this lemma four times or define one index type:

```lean
Σ H : Finset ℕ,
Σ B : Finset ℕ,
Σ v : ℕ → ℕ,
  ℕ → ℤ
```

and filter it by the four admissibility predicates. The sigma-index version is
often easier for Lean; the final nested-sum form follows by `Finset.sum_sigma`
and `Finset.sum_filter`.

## 3. Encoder Membership

For `a` with `Qctrl BS a ≤ R`, define:

```lean
H := hotSet BS c2 a
B := boundarySet BS c2 a
v := shellVec BS a
ell := coldLabel BS a
```

Then prove:

```lean
lemma mem_fiber_encode
    (hR : Qctrl BS a ≤ R) :
    a ∈ fiber BS H B v ell
```

Unfold `fiber`. For every `k ∈ Finset.Icc BS.k0 BS.K`:

1. Energy shell:
   `blockEnergy BS a k ≤ (shellVec BS a k : ℝ) + 1`.
   This is the standard floor inequality, since
   `shellVec BS a k = Nat.floor (blockEnergy BS a k)`.

2. Cold class:
   assume `k ∉ H`. The fiber asks for the class of
   `ell (segStart BS H B k)`, i.e.
   `coldLabel BS a (segStart BS H B k)`.
   Use `segStart_run` and `coldLabel_eq_segStart` to rewrite this as
   `coldLabel BS a k`. Then use `coldLabel_spec` and `cold_isDominant` to get
   the `(3/4) * #(BS.P k)` lower bound.

This proof uses no new number theory.

## 4. Encoder Admissibility

Prove:

```lean
lemma encoder_data_admissible
    (hR : Qctrl BS a ≤ R) :
    hotSet BS c2 a ∈ admH BS c2 R ∧
    boundarySet BS e0 a ∈ admB BS e0 R ∧
    shellVec BS a ∈ admShells BS c2 R (hotSet BS c2 a) ∧
    coldLabel BS a ∈ admLabels BS c2 R
      (hotSet BS c2 a) (boundarySet BS e0 a)
```

Pieces:

- `hotSet ∈ admH`: unfold `admH`; use `hotSet ⊆ Icc` and
  `sum_Rw_hot_le`.
- `boundarySet ∈ admB`: unfold `admB`; use `boundarySet ⊆ Ico` and the
  packaged sum bound from `boundary_penalty_per_k` plus `sum_bipartite_le`.
  If not packaged, isolate:

```lean
lemma sum_Pifloor_boundary_le
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ boundarySet BS e0 a, Pifloor BS e0 k ≤ R
```

- `shellVec ∈ admShells`: use `sum_shellVec_le`, `shellVec_le_floorR`, and
  for hot `k`, `Rw c2 k ≤ blockEnergy BS a k ≤ shellVec BS a k + 1`.
- `coldLabel ∈ admLabels`: for every segment start, split `s = BS.k0` and
  `s ≠ BS.k0`.

## 5. Label Membership

Initial start:

```lean
lemma coldLabel_mem_labelFin_initial
    (hR : Qctrl BS a ≤ R) :
    coldLabel BS a BS.k0 ∈ labelFin BS c2 R BS.k0
```

Use the existing `theoremA_label_range` at block `BS.k0` with
`blockEnergy BS a BS.k0 ≤ R`. Constants are deliberately slack:
`5 / (1 - 1/4) = 20/3 ≤ 7`.

Non-initial start:

```lean
lemma coldLabel_mem_labelFin_noninitial
    (hs : s ∈ segStarts BS H B) (hne : s ≠ BS.k0)
    (hR : Qctrl BS a ≤ R) :
    coldLabel BS a s ∈ labelFin BS c2 R s
```

It is enough to prove:

```lean
|(coldLabel BS a s : ℝ)| ≤ (labelRange c2 s : ℝ)
```

Use `theoremA_label_range` with local energy
`blockEnergy BS a s < Rw c2 s` whenever `s` is cold. Then combine with
`inv_sigmaP_bound`:

```text
1 / sigmaP (BS.P s) ≤ 16 * 2^s * log(2^s).
```

The resulting bound is

```text
|m| ≤ C * sqrt(Rw c2 s) * 2^s * log(2^s)
    = C * sqrt(c2) * 2^(3s/2) / sqrt(log(2^s)),
```

which is below `labelRange c2 s` by the large constant in `labelRange`.

## 6. What Remains After Covering

Once `cover_card_le` is proved, the remaining G5 work is no longer structural.
It is just three estimates:

1. `label_initial_card`: cardinality of the `L0` window gives
   `1 + sqrt R / sigmaCtrl BS`.
2. `label_noninitial_card`: non-initial label windows are swallowed by the
   Peierls weights of the immediately preceding hot/boundary block.
3. constant absorption: all polynomial factors in `k0`, block count, and fixed
   constants are absorbed into `Real.exp (A * numBlocks BS)`.

This is important: if Aristotle returns more obstacles, they should be
classified under these three headings unless the cover lemma itself failed.

