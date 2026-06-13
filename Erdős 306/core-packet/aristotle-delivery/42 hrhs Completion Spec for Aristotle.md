# hrhs Completion Spec (for Aristotle)

Back to [[00 README]]. The G5 cover layer, admissibility, route-closure, and the
hard mechanical bridges of the ε-budget assembly (`hrhs`) are **proved and
locally verified** in `GlobalControlG5Data.lean` and the new leaf
`GlobalControlG5Assembly.lean`. This note specifies the remaining `hrhs`
sub-lemmas. **Work in `GlobalControlG5Assembly.lean`** (imports the cached
`GlobalControlG5Data`); build with `lake build RequestProject.GlobalControlG5Assembly`.
Do NOT touch the frozen cover layer. Keep all hypotheses; leave precisely-named
sorries if a numeric chase resists; verify each lemma compiles.

## Already proved (build on these — do not redo)

In `GlobalControlG5Data.lean`: the data Finsets (`admH`, `admB`, `admShells`,
`admLabels`, `labelFin`, `labelBound`, `L0`, `extShell`, `extLabel`), the cover
(`cover_card_le`), all admissibility (`hotSet_mem_admH`, `boundarySet_mem_admB`,
`extShell_mem_admShells`, `extLabel_mem_admLabels`, `cold_class_of_isDominant`),
the label window membership (`coldLabel_mem_labelFin`, `coldLabel_abs_bound`),
`fiber_prod_bound`, `shell_sum_le`, `hrhs_inner`, `global_levelset_route`.
In `GlobalControlG5Assembly.lean`: `admLabels_card`, `sum_subset_charge_le`.
In `GlobalControl.lean`: `hot_factor`, `cold_factor`, `inv_sigmaP_bound`,
`sigmaCtrl_le_sigmaP_k0`, `cold_block_facts`, `boundary_penalty_per_k`,
`cold_isDominant`. In `GlobalPeierlsBookkeeping.lean`: `weighted_subset_entropy`,
`shell_sum_bound`.

## Remaining sub-lemmas (in dependency order)

### N1. Per-label charge (numeric threshold) — two lemmas
For a segment start `s ≠ k0`, the window size is dominated by the Peierls energy
of the predecessor block `s-1`:
```
lemma labelBound_charge_hot (c2 eps : ℝ) (heps : 0 < eps) (hc2 : 0 < c2) :
    ∃ k0min : ℕ, ∀ s : ℕ, k0min ≤ s →
      (2 * (labelBound c2 s : ℝ) + 1) ≤ Real.exp (eps * Rw c2 (s - 1))
```
and the analogous `labelBound_charge_boundary` with `Pifloor BS e0 (s-1)` (needs
`Pifloor (s-1) ≥ c·2^{s-1}/poly` from block density; carry `BS`, `e0`, and a
density hypothesis). **Proof:** `labelBound c2 s ≤ (20/3)√(c2·2^s)·16·2^s·log(2^s)+1`
(`Int.ceil_le`/`Int.le_ceil`); take logs; `Rw c2 (s-1) = c2·2^{s-1}/log(2^{s-1})³`;
the comparison `(3s/2)log2 + O(log s) ≤ ε·c2·2^{s-1}/log³` holds eventually
(`2^s` beats every polynomial — pattern of `SBEEForcing.exists_X0_const_logbnd`
/ `theoremB_logthreshold`). Lavish constants. If the chase is long, isolate the
clean analytic core as a named lemma `pow_beats_poly_log`.

### N2. Label-size for cold_factor (numeric)
```
lemma labelBound_le_block (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ k0min : ℕ, ∀ (BS : BlockSystem) (s k : ℕ), k0min ≤ BS.k0 →
      s ≤ k → BS.k0 ≤ k → k ≤ BS.K → (X : density gives N_k) →
      |(? : ℝ)| ≤ ((BS.P k).card : ℝ) * (2^k) / 16
```
i.e. `labelBound c2 s ≤ N_k·2^k/16` and `L0 BS R ≤ N_{k0}·2^{k0}/16` for `s ≤ k`.
Same `2^k` vs poly chase + density `N_k ≥ 2^k/(2 log 2^k)`. Used to discharge
`cold_factor`'s `|m| ≤ N·X/16` hypothesis with `m = ℓ(segStart k)`.

### N3. Per-fiber discharge
```
lemma fiber_card_exp_bound : ∃ X0 : ℝ, 0 < X0 ∧ ∀ (BS …) (v ∈ admShells …)
    (ℓ ∈ admLabels …), X0 ≤ 2^BS.k0 → … →
    ((fiber BS H B v ℓ).card : ℝ) ≤ ∏ k ∈ Icc, Real.exp (2*eps*((v k:ℝ)+1))
```
**Proof:** apply `fiber_prod_bound`; discharge its `hcnt` per block:
for `k ∈ H` use `hot_factor` (the `admShells` hot-consistency `Rw c2 k ≤ v k+1`
is available since `v ∈ admShells`); for `k ∉ H` use `cold_factor` with
`m = ℓ(segStart k)` (label size from `admLabels` membership + N2), then
`exp(ε(v k+1)) ≤ exp(2ε(v k+1))`. The fiber filter's cold conjunct is dropped
for `k ∈ H` (filter weakening).

### N4. Label-product bound `LC1` (structural; takes N1 as hypotheses)
```
lemma label_product_le (BS …) (H B : Finset ℕ) (hdisj : Disjoint H B)
    (hcharge : ∀ s ∈ segStarts BS H B, s ≠ BS.k0 →
        ((labelFin BS c2 R s).card : ℝ) ≤
          (if s-1 ∈ H then Real.exp (eps*Rw c2 (s-1)) else Real.exp (eps*Pifloor BS e0 (s-1))))
    (hwnn : 0 ≤ all the exp factors) :
    (∏ s ∈ segStarts BS H B, ((labelFin BS c2 R s).card : ℝ))
      ≤ ((labelFin BS c2 R BS.k0).card : ℝ)
          * (∏ j ∈ H, Real.exp (eps*Rw c2 j)) * (∏ j ∈ B, Real.exp (eps*Pifloor BS e0 j))
```
**Proof:** split `segStarts = ({k0} ∩ segStarts) ∪ (segStarts \ {k0})`. The `k0`
factor `≤ |labelFin k0|` (factors `≥ 1`). For the rest, `s ↦ s-1` is injective
into `H ∪ B` (`segStarts` def: `s-1 ∈ H ∪ B` for `s ≠ k0`); apply `hcharge`, then
`Finset.prod_le_prod_of_subset_of_one_le'` to extend the product from the image
to all of `H ∪ B`, then `Finset.prod_union hdisj` to split. Use
`Finset.prod_image` for the `s ↦ s-1` reindex.

### N5. `hrhs` assembly → discharge `global_levelset_route`'s `hrhs`
Combine: `cover_card_le`/`hrhs_inner` (already done) give
`∑∑∑∑ fiber.card ≤ ∑_H ∑_B |admLabels(H,B)|·shellBound`; `admLabels_card` +
`label_product_le` bound `|admLabels(H,B)|`; `Finset.sum_mul_sum` factors the
`∑_H ∑_B` into `(∑_H ∏_H)(∑_B ∏_B)`; `sum_subset_charge_le ×2` bounds each by
`exp(2εR)exp(nB)`; the `(2L0+1)` initial factor becomes `1 + √R/σctrl` via
`sigmaCtrl_le_sigmaP_k0` (S3); collect constants into `exp(A·numBlocks)`;
ε-budget `3ε (shell) + 2ε + 2ε = 7ε ≤ 8ε`. Then feed the proved facts +
this `hrhs` into `global_levelset_route` to close `GlobalControl.global_levelset`.
(Obtain the master `c2,e0,X0` from `boundary_penalty_per_k` and `cold_isDominant`
— same underlying `theorem_B_nondominant_forcing (1/4)`; choose `k0min` = max of
all thresholds.)

## Detailed proofs (direct-translation level) for the hard pieces

### N1 detailed — the analytic core `pow_beats_poly_log`
First prove the clean asymptotic lemma (the only real analysis; everything else
is algebra):
```
lemma pow_beats_poly_log (C D : ℝ) (hD : 0 < D) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      C + (3 * s / 2) * Real.log 2 + Real.log (Real.log (2 ^ s))
        ≤ D * 2 ^ (s - 1) / (Real.log (2 ^ (s - 1))) ^ 3
```
Proof: `Real.log (2^s) = s·log 2`, so the LHS is `O(s)` and the RHS is
`D·2^{s-1}/((s-1)log2)^3`. Use `Filter.Tendsto`: the function
`(LHS)·((s-1)log2)^3 / 2^{s-1} → 0` (polynomial-times-log over `2^s`), via
`tendsto_pow_atTop_nhds_zero`-style facts already used in
`SBEEForcing.exists_X0_const_logbnd` / `hot_threshold` (copy that pattern: those
lemmas prove `poly·log^k / X → 0`).

Then `labelBound_charge_hot`: take `k0min := max 2 (N+1)` with `N` from
`pow_beats_poly_log (Real.log ((640/3)*Real.sqrt c2) ) (eps*c2)`. For `s ≥ k0min`:
* `labelBound c2 s ≤ (20/3)·√(c2·2^s)·(16·2^s·log(2^s)) + 1` by `Int.ceil_le`
  (`⌈x⌉ ≤ x + 1`), so `2·labelBound c2 s + 1 ≤ (640/3)·√(c2·2^s)·2^s·log(2^s) + 3`.
* `√(c2·2^s) = √c2·2^{s/2}` (`Real.sqrt_mul`, `Real.sqrt_eq_rpow` or
  `2^{s/2}=√(2^s)`), so the bound is `≤ (640/3)√c2·2^{3s/2}·log(2^s) + 3
  ≤ exp(log((640/3)√c2) + (3s/2)log2 + log log(2^s))` (for the `+3`, fold into
  the constant; use `x ≤ exp(log x)` and monotonicity).
* `exp(that) ≤ exp(ε·c2·2^{s-1}/log(2^{s-1})³) = exp(ε·Rw c2 (s-1))` by
  `pow_beats_poly_log` and `Real.exp_le_exp`.
Constants are lavish; widen freely. `labelBound_charge_boundary` is identical
with `Pifloor BS e0 (s-1)` in place of `Rw c2 (s-1)`, using the lower bound
`Pifloor BS e0 (s-1) ≥ c·2^{s-1}/(log)^? ` from block density (carry `BS`,`e0`,
and `N_k ≥ 2^k/(2 log 2^k)`).

### N4 detailed — `label_product_le`
Let `SS := segStarts BS H B`. Then:
```
∏_{s∈SS} |labelFin s|
  = (∏_{s∈SS ∩ {k0}} |labelFin s|) · (∏_{s∈SS \ {k0}} |labelFin s|)   -- Finset.prod_union (disjoint by sdiff)
```
* First factor `≤ |labelFin k0|`: if `k0 ∈ SS` it equals `|labelFin k0|`; else the
  product over `∅` is `1 ≤ |labelFin k0|` (window nonempty ⟹ card ≥ 1).
* Second factor: `SS \ {k0}` splits (disjointly, since `H ∩ B = ∅`) into
  `A_H := {s ∈ SS\{k0} : s-1 ∈ H}` and `A_B := {s ∈ SS\{k0} : s-1 ∈ B}` (every
  `s ∈ SS\{k0}` has `s-1 ∈ H ∪ B` by the `segStarts` filter). On `A_H`,
  `|labelFin s| ≤ exp(ε·Rw c2 (s-1))` (`hcharge`); the map `s ↦ s-1` is injective
  (`Nat.sub` injective on `≥1`; `SS` elements `≥ k0 ≥ 1`) with image `⊆ H`, so
  `∏_{s∈A_H} exp(ε·Rw c2 (s-1)) = ∏_{j∈(s↦s-1)''A_H} exp(ε·Rw c2 j)`
  (`Finset.prod_image`) `≤ ∏_{j∈H} exp(ε·Rw c2 j)`
  (`Finset.prod_le_prod_of_subset_of_one_le'`, factors `≥ 1` since `Rw ≥ 0`).
  Symmetrically for `A_B` with `Pifloor`.
Multiplying gives the claim. Key Mathlib lemmas: `Finset.prod_union`,
`Finset.prod_image` (injective `s↦s-1`), `Finset.prod_le_prod_of_subset_of_one_le'`,
`Finset.prod_filter_mul_prod_filter_not` (to split `SS\{k0}` by `s-1∈H`).

## After hrhs
G7 (`global_control_partition`) via note 38 §7 / 40 §6 (`partfun_series_bound` +
`gaussian_int_sum_le`, both ready). Phase C is being driven separately
(`CircleMethod.lean`); do not touch it.
