# Active Prompt for Aristotle: Finish G5 Without Rediscovery

Work in `RequestProject/GlobalControl.lean`.  Do not redo closed support
lemmas.  The current source already proves:

- `hot_factor`;
- `sum_blockEnergy_le`, `sum_shellVec_le`, `shellVec_le_floorR`;
- `sum_Rw_hot_le`, `sum_bipartite_le`;
- `excSet`, `cold_exceptions_small`, `cold_label_size64`,
  `cold_block_facts`, `boundary_penalty_per_k`;
- `fiber_card_le`, `cold_factor`, `segStart_*`, `coldLabel_*`.

The immediate goal is to close `global_levelset`.  Translate note 40, but use
the following local plan so that no exploration is needed.

## 1. Add The Data Finsets

Add definitions immediately before `global_levelset`.

Define:

```lean
def admH (BS : BlockSystem) (c2 R : ℝ) : Finset (Finset ℕ)
def admB (BS : BlockSystem) (e0 R : ℝ) : Finset (Finset ℕ)
def L0 (BS : BlockSystem) (R : ℝ) : ℤ
def labelFin (BS : BlockSystem) (c2 R : ℝ) (k : ℕ) : Finset ℤ
```

Use note 40 §3 exactly:

- `admH` is powerset of `Finset.Icc BS.k0 BS.K`, filtered by
  `∑ k ∈ H, Rw c2 k ≤ R`.
- `admB` is powerset of `Finset.Ico BS.k0 BS.K`, filtered by
  `∑ k ∈ B, Pifloor BS e0 k ≤ R`.
- `L0 BS R = ⌈(7 : ℝ) * Real.sqrt R / sigmaP (BS.P BS.k0)⌉`.
- `labelFin` uses `Finset.Icc (-(L0 BS R)) (L0 BS R)` when `k = BS.k0`,
  otherwise `Finset.Icc (-(labelRange c2 k)) (labelRange c2 k)`.

For shell and label data, prefer total-function versions to avoid dependent-pi
API pain:

```lean
def admShells (BS : BlockSystem) (c2 R : ℝ) (H : Finset ℕ) :
    Finset (ℕ → ℕ) :=
  ((Finset.Icc BS.k0 BS.K).pi
      (fun k => Finset.range (Nat.floor R + 1))).image
    (fun v k => if h : k ∈ Finset.Icc BS.k0 BS.K then v k h else 0)
  -- then filter by total shell sum and hot-consistency.

def admLabels (BS : BlockSystem) (c2 R : ℝ) (H B : Finset ℕ) :
    Finset (ℕ → ℤ) :=
  (segStarts BS H B).pi (fun k => labelFin BS c2 R k)
  -- then image to total functions, defaulting to 0 outside segStarts.
```

If the total-function image is awkward, use note 40's dependent-pi version and
add small `extV` / `extL` definitions.  Either route is acceptable; keep the
final `fiber BS H B v ℓ` interface total.

## 2. Prove Encoder Membership And Admissibility

Add these lemmas with statements adjusted to the exact `admShells` /
`admLabels` representation chosen above:

```lean
lemma hotSet_mem_admH ...
lemma boundarySet_mem_admB ...
lemma shellVec_mem_admShells ...
lemma coldLabel_mem_labelFin_initial ...
lemma coldLabel_mem_labelFin_noninitial ...
lemma labels_mem_admLabels ...
lemma mem_fiber_encode ...
lemma encoder_data_admissible ...
```

Proof instructions:

- `hotSet_mem_admH`: unfold `admH`; use `hotSet ⊆ Icc` and
  `sum_Rw_hot_le`.
- `boundarySet_mem_admB`: unfold `admB`; use `boundarySet ⊆ Ico` and
  `boundary_penalty_per_k` termwise plus `sum_bipartite_le`.  If this exact
  lemma is not already packaged, create `sum_Pi_boundary_le` from note 40
  §2.3d-iv.
- `shellVec_mem_admShells`: use `sum_shellVec_le`, `shellVec_le_floorR`, and
  hot-consistency:
  `k ∈ hotSet BS c2 a → Rw c2 k ≤ blockEnergy BS a k ≤ shellVec BS a k + 1`.
  The second inequality is `Nat.lt_floor_add_one` / `Nat.floor_le` arithmetic.
- Initial label: use the existing `theoremA_label_range`/local label-range
  lemma if present; otherwise state a precise named helper
  `coldLabel_mem_labelFin_initial` and leave only that helper if necessary.
- Non-initial label: use `cold_label_size64` or the already available
  `labelRange` bound.  If the final numeric comparison is the obstacle,
  isolate it as `labelRange_contains_coldLabel`.
- `mem_fiber_encode`: unfold `fiber`.  For the energy coordinate use
  `blockEnergy ≤ shellVec + 1`.  For the cold-label coordinate use
  `segStart_run` and `coldLabel_eq_segStart`, then `coldLabel_spec` /
  `cold_isDominant`.

## 3. Prove The Covering Bound

Add:

```lean
lemma cover_card_le ... :
  ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ)
    ≤
  ∑ H ∈ admH BS c2 R,
  ∑ B ∈ admB BS e0 R,
  ∑ v ∈ admShells BS c2 R H,
  ∑ ℓ ∈ admLabels BS c2 R H B,
    ((fiber BS H B v ℓ).card : ℝ)
```

Proof instructions:

1. Define the encoding map
   `a ↦ (hotSet BS c2 a, boundarySet BS c2 a, shellVec BS a, coldLabel BS a)`
   with whatever restrictions are needed by the chosen data Finsets.
2. Use `mem_fiber_encode` and `encoder_data_admissible` to show every
   level-set element lies in one of the indexed fibers.
3. Use `Finset.card_le_card` against the nested `biUnion`.
4. Use `Finset.card_biUnion_le` / `Finset.card_bind_le` style estimates four
   times.  Do not try to prove disjointness of fibers.

If Lean's nested `biUnion` API burns time, create a helper:

```lean
lemma card_le_sum_fibers_of_cover
    (S : Finset α) (I : Finset ι) (F : ι → Finset α)
    (hcover : S ⊆ I.biUnion F) :
    S.card ≤ ∑ i ∈ I, (F i).card
```

Prove it once by `Finset.card_le_card hcover` followed by
`Finset.card_biUnion_le`.

## 4. Prove Label Product Numerics

Add:

```lean
lemma label_initial_card ...
lemma label_noninitial_card ...
lemma label_prod_le ...
```

Proof instructions:

- `label_initial_card`: unfold `labelFin`, split `k = BS.k0`, use
  `Int.card_Icc`, `Int.ceil_le`, and the existing `sigmaCtrl_le_sigmaP_k0` /
  `sigmaCtrl_le_one` style lemmas.  Target can be very wasteful:
  `15 * csig * BS.k0 * (1 + Real.sqrt R / sigmaCtrl BS)`.
- `label_noninitial_card`: use crude bound
  `card (Icc (-labelRange) labelRange) ≤ 2 * |labelRange| + 1 ≤ 2^(2*k)`,
  then dominate by `Real.exp (eps * weight)`.  If the exponential domination is
  the hard part, isolate it as a numeric threshold lemma:

```lean
lemma label_noninitial_card_numeric ...
```

- `label_prod_le`: split `segStarts` into the initial start and non-initial
  starts.  Map every non-initial start `s` to `s - 1`; by the definition of
  `segStarts`, this lies in `H ∪ B`.  Overpay by the full products over `H`
  and `B`; all exponential factors are at least `1`.

## 5. Assemble `global_levelset`

Inside `global_levelset`:

1. Choose `c2`, `e0`, and all thresholds from existing support lemmas.
2. Apply `cover_card_le`.
3. Apply `fiber_card_le` to each fiber.
4. For hot blocks, use `hot_factor`; its hot-consistency hypothesis comes from
   `admShells`.
5. For cold blocks, use `cold_factor`.
6. Sum over labels via `label_prod_le`.
7. Sum over shell vectors using `GlobalPeierlsBookkeeping.shell_sum_bound`.
8. Sum over `H` and `B` using
   `GlobalPeierlsBookkeeping.weighted_subset_entropy`.
9. Collect constants into `A`, using `admissibleGlobalRange BS` to absorb
   polynomial factors such as `BS.k0` into `Real.exp (A * numBlocks BS)`.
10. Finish with `Real.exp (7 * eps * R) ≤ Real.exp (8 * eps * R)`.

Do not introduce a trivial-regime split.  Note 40 explains why it is no longer
needed.

## Failure Policy

If the full G5 assembly does not close, the best partial result is:

1. all data Finsets defined;
2. `cover_card_le` proved;
3. any remaining obstacle isolated as one of:
   - `coldLabel_mem_labelFin_initial`;
   - `labelRange_contains_coldLabel`;
   - `label_noninitial_card_numeric`;
   - `shell_sum_bound_reindex`;
   - `global_levelset_constant_absorption`.

Do not leave unnamed `sorry`s.
