# G5 Endgame — Remaining Holes, Quartered

Back to [[00 README]]. Continues [[39 G5 Lean Skeleton - Twelve Named Holes]].
The skeleton is instantiated and most holes are CLOSED (1, 2, 4, 5, 7, 9, 11,
plus `hot_threshold`, `inv_sigmaP_bound`). This note quarters what remains —
the hole-8 glue, hole 3 (the repeated-timeout item), hole 6, hole 10, hole 12
— into sub-lemmas each ≤ 30–60 lines, **with complete proofs**. Close them in
the order listed; every one is independent unless marked.

Three structural notes discovered while re-deriving the assembly against the
instantiated skeleton (read before starting):

* **(N-a) No `log R` cap / trivial-regime split is needed in the assembly.**
  The fiber records per-block shells, so the hot count's polynomial factor is
  in `n_k` (handled inside `hot_factor`), never in `R`. `trivial_regime` is
  already proved — keep it, but hole 12 does not need the case split.
* **(N-b) The shell data must carry hot-consistency.** `hot_factor` needs
  `Rw c2 k ≤ n_k + 1`. True on the image of the encoder, but the factorized
  sum ranges over a product superset — so the consistency must be built into
  the shell-data Finset (the `.filter (∀ k ∈ H, Rw c2 k ≤ v k + 1)` in §3).
* **(N-c) The initial label uses the `√R`-range, non-initial labels use the
  `Rw`-range.** `labelRange c2 k` (the `X^{3/2}`-sized bound) is correct ONLY
  for non-initial segment starts; the start at `k0` must range over
  `Icc (−L₀) L₀` with `L₀ := ⌈7·√R / sigmaP (BS.P BS.k0)⌉` — that is where the
  single global factor `(1+√R/σctrl)` comes from (via S3). Using
  `labelRange` at `k0` would NOT give the σctrl factor.

Fix `ρ := 1/4`; `(c2, X0B)` from `cold_isDominant`; `e0` from
`cold_exception_bound`.

---

## §1. Hole 8 glue: `hot_factor` (its numeric core `hot_threshold` is proved)

*Proof of `hot_factor`.* Obtain `(C0, X1)` from `unified_levelset eps`. Obtain
`X0₈` from `hot_threshold eps c2 C0`. Take `X0 := max X1 X0₈ (+16)`. For a hot
shell `n+1 ≥ Rw c2 k`, `X = 2^k ≥ X0`:

1. `unified_levelset` at `R := n+1 ≥ 1` (window/density from `BS.hwindow`,
   `BS.hdensity` — same bridging as in `cold_factor`):
   `count ≤ C0·e^{ε(n+1)}·(1 + √(n+1)/σ_k)`.
2. `inv_sigmaP_bound`: `1/σ_k ≤ 16·2^k·log 2^k`, so
   `1 + √(n+1)/σ_k ≤ 17·2^k·log(2^k)·√(n+1)` (crudely, using `√(n+1) ≥ 1`,
   `2^k log 2^k ≥ 1`).
3. It remains: `C0·17·2^k·log(2^k)·√(n+1) ≤ e^{ε(n+1)}`. Take logs; with
   `t := n+1 ≥ Rw c2 k`:
   `log C0 + log 17 + log 2^k + log log 2^k + ½·log t ≤ ε·t`.
   * The `t`-free part: `hot_threshold`'s FIRST inequality at `X = 2^k` gives
     `2·(log C0 + log 34 + log X + log log X + 1) ≤ ε·Rw c2 k ≤ ε·t` — half of
     it covers the `t`-free terms.
   * The `½ log t` part: `hot_threshold`'s SECOND inequality gives
     `log(Rw) ≤ ε·Rw`; since `u ↦ ε·u − log u` is nondecreasing for
     `u ≥ 1/ε` (and `Rw c2 k ≥ 1/ε` for `X ≥ X0₈`, part of the threshold),
     `log t ≤ ε·t` for all `t ≥ Rw`. Halve it.
   Summing the two halves: `… ≤ (ε/2)t + (ε/2)t = ε·t`. ∎
   (Total target `e^{2ε(n+1)}` = step 1's `e^{ε(n+1)}` × step 3's `e^{ε(n+1)}`.)

---

## §2. Hole 3 quartered (the timeout item)

### 3a `sum_blockEnergy_le`
`Qctrl BS a ≤ R → ∑ k ∈ Icc BS.k0 BS.K, blockEnergy BS a k ≤ R`.
*Proof.* `energy_splits` gives `∑ blockEnergy + ∑ Xen ≤ Qctrl`; the bipartite
sum is a sum of squares `≥ 0`. ∎ (5 lines.)

### 3b `sum_shellVec_le`
`Qctrl BS a ≤ R → ∑ k ∈ Icc BS.k0 BS.K, (shellVec BS a k : ℝ) ≤ R`.
*Proof.* `Nat.floor_le (blockEnergy_nonneg)` per term + 3a. ∎
Also `shellVec_le_floorR : Qctrl ≤ R → ∀ k ∈ Icc, shellVec a k ≤ ⌊R⌋₊`
(`blockEnergy k ≤ ∑ ≤ R`, `Nat.floor_mono`). (Needed for the shell Finset.)

### 3c `sum_Rw_hot_le`
`Qctrl BS a ≤ R → ∑ k ∈ hotSet BS c2 a, Rw c2 k ≤ R`.
*Proof.* For `k ∈ hotSet`: `Rw c2 k ≤ blockEnergy a k` (defn `isHot`). Sum
over `hotSet ⊆ Icc` (`Finset.sum_le_sum_of_subset_of_nonneg`, energies `≥ 0`),
then 3a. ∎ (8 lines.)

### 3d `sum_Pi_boundary_le` — split into FOUR sub-lemmas

**3d-i `sum_bipartite_le`** (pure bookkeeping):
`Qctrl BS a ≤ R → ∑ k ∈ Finset.Ico BS.k0 BS.K, Xen k a ≤ R`
where `Xen k a := ∑ pq ∈ bipartitePairs BS k, (Hglob (toPlain BS a) pq.1 pq.2 / (pq.1*pq.2))²`.
*Proof.* `energy_splits` (drop the internal sum this time). ∎

**3d-ii `cold_exceptions_small`**: ∃ thresholds; for cold `k` (with
`X = 2^k ≥ X0`), the exception set
`E k := (BS.P k).filter (fun p => restrict BS a k ⟨p,…⟩ ≠ (coldLabel BS a k : ZMod p))`
satisfies `(E k).card ≤ ⌊e0⌋₊` and hence
`((BS.P k \ E k).card : ℝ) ≥ ((BS.P k).card : ℝ) − e0`.
*Proof.* `cold_isDominant` + `coldLabel_spec` give the dominant class;
`cold_label_size` gives `|m| ≤ N·X/16`; `cold_exception_bound` applies with
`R := blockEnergy a k ≤ Rw c2 k` — wait, use `R := max 1 (blockEnergy a k)`
and the cold bound `blockEnergy < Rw`; monotonicity in `R` of the hypothesis
`QP ≤ R` is harmless. Card arithmetic: `card (P \ E) = card P − card E`
(`E ⊆ P`). ∎

**3d-iii `boundary_penalty_per_k`** (the heart; ≤ 60 lines):
∃ thresholds (`k0min`); for `k ∈ boundarySet BS c2 a`, `2^{k} ≥ X0`:
`Pifloor BS e0 k ≤ Xen k a`.
*Proof.* Unfold `boundarySet`: `k, k+1` cold, labels `m := coldLabel a k ≠ m'
:= coldLabel a (k+1)`. Apply `mismatch_penalty_with_exceptions` with
`Ek := E k`, `Ek1 := E (k+1)` (3d-ii):
* `hlabel_k/hlabel_k1`: by definition of `E` (non-exception = label-conforming).
* `hNk : 12 ≤ (BS.P k \ Ek).card`: from 3d-ii (`N_k ≥ X_k/(2 log X_k)` density,
  `e0` absolute, `X_k ≥ X0(e0)` threshold).
* `hm : 32|m| ≤ 2^k·(BS.P k \ Ek).card`: `cold_label_size` gives
  `|m| ≤ N_k·X_k/16`; hmm — needed is `32|m| ≤ X_k·(N_k − e0)`; since
  `N_k − e0 ≥ N_k/2` (threshold), suffices `|m| ≤ N_k·X_k/64`: prove
  `cold_label_size` with `/64` — OR note its proof actually shows
  `|m| ≤ 168√c2·X^{3/2}/√log X` which is `≤ N_k X_k/64` for `X ≥ X0`:
  use the sharper intermediate form (see 6c below, `coldLabel_in_labelRange`,
  which is the better citation). Same for `hm'`.
* Conclusion `((P(k+1)\Ek1).card − 1)·((P k\Ek).card)³/(2^13 X_k²) ≥ Pifloor`:
  monotonicity in the two cards (3d-ii lower bounds), with
  `N_{k+1} − e0 − 1 ≥ 0` (threshold). ∎

**3d-iv `sum_Pi_boundary_le`** (assembly):
`∑_{k ∈ boundarySet} Pifloor BS e0 k ≤ ∑_{k ∈ boundarySet} Xen k a ≤ R`
by 3d-iii termwise (`boundarySet ⊆ Ico`), `Xen ≥ 0`, and 3d-i. ∎

---

## §3. Hole 6: data Finsets, encoder membership, label ranges

### Data Finsets (definitions; no obligations)

```lean
def admH (BS) (c2 R) : Finset (Finset ℕ) :=
  (Finset.Icc BS.k0 BS.K).powerset.filter (fun H => ∑ k ∈ H, Rw c2 k ≤ R)

def admB (BS) (e0 R) : Finset (Finset ℕ) :=
  (Finset.Ico BS.k0 BS.K).powerset.filter (fun B => ∑ k ∈ B, Pifloor BS e0 k ≤ R)

/-- Shell data: dependent pi over Icc, capped at ⌊R⌋₊, hot-consistent (N-b). -/
def admShells (BS) (c2 R) (H : Finset ℕ) : Finset ((k : ℕ) → k ∈ Finset.Icc BS.k0 BS.K → ℕ) :=
  ((Finset.Icc BS.k0 BS.K).pi (fun _ => Finset.range (⌊R⌋₊ + 1))).filter
    (fun v => (∑ k ∈ (Finset.Icc BS.k0 BS.K).attach, (v k.1 k.2 : ℝ)) ≤ R ∧
              ∀ k (h : k ∈ Finset.Icc BS.k0 BS.K), k ∈ H → Rw c2 k ≤ (v k h : ℝ) + 1)

/-- Label data: initial start ranges over the √R-window (N-c), others over labelRange. -/
def L0 (BS) (R : ℝ) : ℤ := ⌈(7:ℝ) * Real.sqrt R / sigmaP (BS.P BS.k0)⌉
def labelFin (BS) (c2 R) (k : ℕ) : Finset ℤ :=
  if k = BS.k0 then Finset.Icc (-(L0 BS R)) (L0 BS R)
  else Finset.Icc (-(labelRange c2 k)) (labelRange c2 k)
def admLabels (BS) (c2 R) (H B : Finset ℕ) : Finset ((k : ℕ) → k ∈ segStarts BS H B → ℤ) :=
  (segStarts BS H B).pi (fun k => labelFin BS c2 R k)
```

(Extend pi-elements to total functions when feeding `fiber`:
`extV v := fun k => if h : _ then v k h else 0`, same for labels.)

### 6c `coldLabel_in_labelRange` (two statements)
∃ thresholds; for cold `k` with `Qctrl a ≤ R`:
* if `k = BS.k0`: `coldLabel BS a BS.k0 ∈ Finset.Icc (−L0 BS R) (L0 BS R)`.
  *Proof.* `theoremA_label_range` at `R₀ := blockEnergy a k0 ≤ R` (3a-type),
  `5/(1−ρ) = 20/3 ≤ 7`. ∎
* if `k > BS.k0`: `coldLabel BS a k ∈ Icc (−labelRange c2 k) (labelRange c2 k)`.
  *Proof.* `theoremA_label_range` at `R_k < Rw c2 k` (cold) +
  `inv_sigmaP_bound`: `|m| ≤ 7·√(Rw c2 k)·16·2^k·log 2^k
  = 112·√c2·2^{3k/2}·√(log 2^k)·… ≤ 168·√c2·2^{3k/2}/√(log 2^k)`… —
  **chase the exact exponent of the log**: `√(Rw) = √c2·2^{k/2}/log^{3/2}`,
  times `16·2^k·log` gives `16√c2·2^{3k/2}/√log ≤ labelRange c2 k` ✓ (the
  `168` has slack ≥ 10×). ∎
  Also the size for 3d-iii / cold_factor: `labelRange c2 k† ≤ (BS.P k).card·2^k/64`
  for `k† ≤ k`, `2^{k†} ≥ X0` — monotone numeric (`2^{3k†/2} ≤ 2^{3k/2}` and
  `2^{3k/2}/√log ≤ (2^k/(2 log))·2^k/64` ⟺ `128·log^{1/2}·… ≤ 2^{k/2}`). ∎

### 6a `mem_fiber_encode`
∃ thresholds; `Qctrl a ≤ R` ⟹
`a ∈ fiber BS H B (extV (encV a)) (extL (encL a))` where `H := hotSet`,
`B := boundarySet`, `encV := shellVec` (restricted), `encL := coldLabel`
(restricted to `segStarts`).
*Proof.* Per `k ∈ Icc`: `blockEnergy ≤ shellVec k + 1` = `Nat.lt_floor_add_one`.
For cold `k`: the fiber wants the class for label `extL … (segStart H B k)`;
`segStart_mem` (hole 4) puts the start in `segStarts`, so `extL` evaluates to
`coldLabel a (segStart …)` which equals `coldLabel a k` by
`coldLabel_eq_segStart` (hole 5); the class bound is `coldLabel_spec` +
`cold_isDominant`. ∎

### 6b `encoder_data_admissible`
`Qctrl a ≤ R` ⟹ `hotSet ∈ admH` (3c), `boundarySet ∈ admB` (3d-iv),
restricted `shellVec ∈ admShells` (3b + `shellVec_le_floorR` + hot-consistency:
`k ∈ hotSet → Rw ≤ blockEnergy ≤ shellVec k + 1`), restricted labels
`∈ admLabels` (6c). ∎ (Bundling lemma.)

### 6d `cover_card_le`
```
(Set.ncard {a | Qctrl BS a ≤ R} : ℝ) ≤
  ∑ H ∈ admH, ∑ B ∈ admB, ∑ v ∈ admShells c2 R H, ∑ ℓ ∈ admLabels c2 R H B,
    ((fiber BS H B (extV v) (extL ℓ)).card : ℝ)
```
*Proof.* The levelset (as a Finset via `Set.ncard_coe_Finset` /
`Finset.filter`) is `⊆` the 4-level `Finset.biUnion` of fibers indexed by the
admissible data (6a membership + 6b admissibility), and `card_biUnion_le`
four times. ∎ (Bookkeeping only; no mathematics.)

---

## §4. Hole 10: the two label-product numerics

**10a `label_initial_card`**: `((labelFin BS c2 R BS.k0).card : ℝ)
≤ 15·csig·(BS.k0)·(1 + Real.sqrt R / sigmaCtrl BS)` (for `2 ≤ k0`).
*Proof.* `card (Icc (−L0) L0) = 2L0+1 ≤ 2(7√R/σ_{k0} + 1) + 1 ≤
15·(1 + √R/σ_{k0})`; then `1/σ_{k0} ≤ csig·k0/σctrl` (S3 rearranged). ∎

**10b `label_noninitial_card`**: ∃ `k0min`; for `k† ∈ segStarts H B`,
`k† ≠ BS.k0`, `k0 ≥ k0min`:
`((labelFin BS c2 R k†).card : ℝ) ≤ Real.exp (eps * w(k†−1))` where
`w(j) := if j ∈ H then Rw c2 j else Pifloor BS e0 j` (segStarts defn ⟹
`k†−1 ∈ H ∪ B`).
*Proof.* `card ≤ 2·labelRange c2 k† + 1 ≤ 2^{2k†}` (crude), so suffices
`2k†·log 2 ≤ ε·min(Rw c2 (k†−1), Pifloor BS e0 (k†−1))`; both floors are
`≥ c·2^{k†}/k†⁴` (density + `e0` absolute), a `theoremB_logthreshold`-style
chase. ∎

**10c `label_prod_le`** (the product over starts):
```
∏ k† ∈ segStarts H B, (labelFin … k†).card
  ≤ 15·csig·k0·(1+√R/σctrl) · ∏_{k∈H} e^{ε·Rw c2 k} · ∏_{k∈B} e^{ε·Pifloor e0 k}
```
*Proof.* Split the product at `k† = k0` (10a) vs rest (10b); the map
`k† ↦ k†−1` is injective from non-initial starts into `H ∪ B` (defn), and
each extra factor `e^{εw} ≥ 1`, so over-paying every member of `H ∪ B` only
increases the right side. (`H`, `B` disjoint? Not needed — `w` picks one.) ∎

---

## §5. Hole 12: the assembly (≤ 60 lines, every input named)

Choose `k0min` = max of all thresholds above; `A` collects all per-block
constants. Chain:

1. 6d: `N(R) ≤ ∑_{H,B,v,ℓ} fiber.card`.
2. `fiber_card_le` (hole 7) per tuple; per-block counts split hot/cold:
   `k ∈ H`: drop the cold conjunct (`Finset.card_le_card`, filter weakening) →
   `hot_factor` (hole 8; hypothesis `Rw ≤ v k + 1` from `admShells`'s filter) →
   `≤ e^{2ε(v_k+1)}`. `k ∉ H`: drop the energy-only weakening → `cold_factor`
   (hole 9; label size from the `labelFin` ranges + 6c's monotonicity) →
   `≤ e^{ε(v_k+1)} ≤ e^{2ε(v_k+1)}`.
3. The `ℓ`-sum is constant in the summand: `∑_ℓ 1 = ∏ labelFin.card`
   (`Finset.card_pi`) → 10c.
4. The `v`-sum: `∑_{v ∈ admShells} ∏_k e^{2ε(v_k+1)} ≤` `shell_sum_bound`
   (`α = 2ε, β = ε`; the admShells filter implies the SH filter; if SH's
   index form (`Fintype.piFinset`) differs from `Finset.pi`, add the
   10-line reindexing bridge) `≤ e^{3εR}·e^{A₂(ε)·nB}`.
5. The `H`-sum: `∑_{H ∈ admH} ∏_{k∈H} e^{εRw k} ≤` `weighted_subset_entropy`
   with `eps' := 4ε`, `w := Rw c2`, `cost k := e^{εRw k} = e^{(4ε)·w k/4}` —
   the hypothesis `hcb` holds with EQUALITY — `≤ e^{2εR}·e^{nB}`.
   Same for the `B`-sum with `w := Pifloor` → `≤ e^{2εR}·e^{nB}`.
6. Collect: `N(R) ≤ [15·csig·k0·(1+√R/σctrl)] · e^{(3+2+2)εR} · e^{(A₂+2)·nB}`
   and `k0 ≤ e^{nB}` (admissibility `2k0 ≤ K` ⟹ `nB ≥ k0+1`):
   `≤ e^{A·nB}·e^{7εR}·(1+√R/σctrl) ≤` target (`8ε`). ∎

(No trivial-regime split needed — N-a. `trivial_regime` stays as a proved
spare.)

## §6. After G5

G7 = note 38 §7 unchanged (`partfun_series_bound` at `ε = c/32`, sector I
floor `F0(BS) := min(Rw c2 k0, Pifloor e0 k0, E1(k0))` via the proved
budget/penalty lemmas, sector II via the proved `gaussian_int_sum_le`).
Then Phase C (notes 35 + 37 §6), then Phase W.
