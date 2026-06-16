# Note 43 — G6 localization dichotomy: translation-ready decomposition

**Target.** Close `GlobalControl.g6_localization` (in `GlobalControlG7.lean`):

```lean
theorem g6_localization :
    ∃ (k0loc : ℕ) (c2 e0 : ℝ), 0 < c2 ∧ 0 < e0 ∧
      ∀ (BS : BlockSystem), k0loc ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ a : GlobalAssignment BS, a ∉ mainArc BS C →
        globalControlFloor BS c2 e0 ≤ Qctrl BS a ∨ diagSector BS C a
```
where `globalControlFloor BS c2 e0 = min (Rw c2 BS.k0) (Pifloor BS e0 BS.k0)` and
`diagSector BS C a := ∃ m, (∀ p, a p = m mod p) ∧ C/σ < |m| ∧ Qctrl a = m²·σ²`,
`σ := sigmaCtrl BS`.

The `c2, e0` are exactly the cold-block constants produced by `cold_block_facts`
(same `c2,e0` that feed `boundary_penalty_per_k`); take `k0loc` large enough for
the two monotonicity thresholds in L1/L2 below (and `≥ 4`). This is note 34 §G6.

## Case structure

Fix `a` off the main arc. Three exhaustive cases on `(hotSet, boundarySet)`:

- **Case H (some hot block):** `∃ k ∈ [k0,K], isHot BS c2 a k`. → left disjunct.
- **Case B (no hot, some boundary mismatch):** `hotSet = ∅` and
  `∃ k ∈ [k0,K), ¬isHot k ∧ ¬isHot (k+1) ∧ coldLabel k ≠ coldLabel (k+1)`
  (i.e. `boundarySet ≠ ∅`). → left disjunct.
- **Case D (no hot, no boundary):** `hotSet = ∅` and `boundarySet = ∅`.
  → right disjunct (`diagSector`).

## L1 (Case H ⇒ floor disjunct)

`isHot k`: `Rw c2 k ≤ blockEnergy BS a k = QP (BS.P k) (restrict BS a k)`.
`energy_splits` gives `∑_{j∈[k0,K]} blockEnergy j + (bipartite) ≤ Qctrl a`, and each
summand is `≥ 0`, so `blockEnergy k ≤ Qctrl a`. Hence `Rw c2 k ≤ Qctrl a`.

**Need** `Rw c2 k0 ≤ Rw c2 k` for `k0 ≤ k` to conclude
`globalControlFloor ≤ Rw c2 k0 ≤ Rw c2 k ≤ Qctrl a`.

> **Sub-lemma `Rw_mono`** (REQUIRED): for `c2 > 0` and `4 ≤ k0 ≤ k`,
> `Rw c2 k0 ≤ Rw c2 k`. Proof: `Rw c2 k = (c2/(log2)³)·2^k/k³`; the map `k ↦ 2^k/k³`
> is nondecreasing for `k ≥ 4` because `2^{k+1}/(k+1)³ ≥ 2^k/k³ ⟺ 2k³ ≥ (k+1)³ ⟺
> (1+1/k)³ ≤ 2`, true for `k ≥ 4` (since `(5/4)³ = 125/64 < 2`). Formalize by
> `Nat`-induction on `k` from `k0`, each step the displayed inequality
> (`nlinarith` on `2k³ ≥ (k+1)³` for `k≥4`), plus `Real.log_pow` to expand
> `log (2^k) = k·log 2`. The `4 ≤ k0` requirement is folded into `k0loc`.

## L2 (Case B ⇒ floor disjunct)

`boundary_penalty_per_k` (already proved, with constants `c2,e0` from
`cold_block_facts`) states: for a mismatch-boundary block `k`,
`Pifloor BS e0 k ≤ Xen BS a k` where `Xen BS a k = ∑_{pq ∈ bipartitePairs k}
(Hglob/(pq))²` is the bipartite cross-energy at level `k`. (Check the exact name
of the bipartite-energy accessor in `GlobalControl.lean`; it is the `k`-th summand
of the second sum in `energy_splits`.) Then `Xen BS a k ≤ Qctrl a` (drop the
internal sum and the other bipartite summands, all `≥ 0`, via `energy_splits`).
Hence `Pifloor e0 k ≤ Qctrl a`.

**Need** `Pifloor e0 k0 ≤ Pifloor e0 k` for `k0 ≤ k`.

> **Sub-lemma `Pifloor_mono`** (REQUIRED): for the threshold `k0loc` (so that
> `|P j| - e0 ≥ ½|P j|`, available since density `|P j| ≥ 2^j/(2 log 2^j) → ∞`),
> `Pifloor BS e0 k0 ≤ Pifloor BS e0 k` for `k0 ≤ k ≤ K`. `Pifloor BS e0 k =
> (|P(k+1)|-e0-1)(|P k|-e0)³/(2¹³(2^k)²)`. Lower-bound numerator via density,
> upper-bound denominator; the ratio grows like `2^{2k}/log⁴ 2^k`. Cleanest: prove
> `Pifloor e0 k ≥ g(k)` with `g` explicitly increasing, OR (sufficient for the
> floor disjunct) prove directly `globalControlFloor ≤ Pifloor e0 k` by showing
> `min(Rw k0, Pifloor k0) ≤ Pifloor e0 k`. Since both `Rw k0` and `Pifloor k0`
> are `≤ Pifloor e0 k` for `k ≥ k0` once `k0loc` is past the density threshold,
> this is a monotone-comparison; the affine-vs-exponential gap is the same
> mechanism as `pow_beats_poly_log` (already proved in `GlobalControlG5Assembly`).

*(Implementation shortcut: L1 and L2 both only need
`globalControlFloor ≤ (the block bound)`. Since `globalControlFloor` is a `min`,
it suffices to show the relevant single floor (`Rw c2 k0` for H, `Pifloor e0 k0`
for B) is `≤` the per-block bound, then `min_le_left`/`min_le_right` +
monotonicity. So the two monotonicities are the only analytic inputs.)*

## L3 (Case D ⇒ globally diagonal with common label `m`)

`hotSet = ∅` ⇒ every block `k ∈ [k0,K]` is cold ⇒ by `cold_isDominant` each cold
block has a dominant label `coldLabel BS a k` with the `(1-ρ)`-majority property
(ρ = 1/4). `boundarySet = ∅` ⇒ for every consecutive cold pair,
`coldLabel k = coldLabel (k+1)`. Therefore `coldLabel` is **constant** on `[k0,K]`
(finite induction up the chain; or use `segment_label_constant` from
`GlobalPeierlsBookkeeping`, which states labels are constant along a non-boundary
run). Set `m := coldLabel BS a k0`.

**Each block is fully diagonal at `m`:** a cold block with dominant label `m` has
`(1-ρ)|P k|` primes `p` with `a p = m mod p`; the exceptions form `excSet`, with
`|excSet| ≤ e0` (`cold_exceptions_small`). To get `a p = m mod p` for **all**
`p ∈ blockSupport` (full diagonal, no exceptions) we need the exception set empty.
This is **not** automatic from cold-dominance alone.

> **Key step `cold_no_exceptions` (the substantive D-step):** in Case D (no hot,
> no boundary) every cold block has `excSet = ∅`, i.e. `a p = m mod p` for *every*
> `p`. Reason (note 34 §G6): an exceptional prime `p₀` in block `k` (with
> `a p₀ ≠ m mod p₀`) contributes, with its `(1-ρ)`-majority same-block partners,
> cross-energy `≥ E₁ = N³/(2¹⁵X²) ≈ Rw c2 k` (this is exactly the Theorem-A §3 (A3)
> per-exception energy via `lemmaD`), which would make the block **hot** —
> contradicting Case D. So no exceptions. Formalize by: if `excSet k ≠ ∅`, exhibit
> a prime giving `blockEnergy k ≥ Rw c2 k` (reuse the A3 energy estimate /
> `theorem_A_dominant_count` internals — `dispersion_energy_bound` over the
> in-block fingerprint), contradicting `¬ isHot k`. **This is the one genuinely
> new lemma**; everything else is assembly.

Given `cold_no_exceptions` for all `k`, and that every `p ∈ blockSupport` lies in
some block `k ∈ [k0,K]`, we get `∀ p, a p = (m : ZMod p)` — `a` is globally
diagonal with label `m`.

## L4 (off-main ⇒ large label)

`a ∉ mainArc BS C` and `a` globally diagonal with label `m`. `mainArc` =
`{a | ∃ m', |m'| ≤ C/σ ∧ ∀ p, a p = m' mod p}`. If `|m| ≤ C/σ`, then `m` itself
witnesses `a ∈ mainArc` — contradiction. Hence `C/σ < |m|`. (Direct from defs.)

## L5 (diagonal energy identity `Qctrl a = m²σ²`)

For globally diagonal `a` (`a p ≡ m mod p`): for any control pair `(p,q)`,
`Hglob (toPlain a) p q = crtRepr p q (a p) (a q)` = the centered representative in
`(-pq/2, pq/2]` of the residue `≡ m (mod pq)` (since `a p ≡ m mod p`,
`a q ≡ m mod q`, CRT). If `|m| < pq/2`, this centered rep equals `m`, so
`(Hglob/(pq))² = (m/(pq))²`.

**The bound `|m| < pq/2` holds for every control pair:** the smallest modulus
product is at block `k0`: every `p,q` in a `k0`-internal or `(k0,k0+1)`-bipartite
pair has `p,q ≥ 2^{k0}`, so `pq ≥ 2^{k0}·2^{k0} = 2^{2k0}` (strict for distinct
internal primes; bipartite `≥ 2^{2k0+1}`). The cold label obeys the per-block
bound `|m| = |coldLabel k0| ≤ (2^{k0})²/2 = 2^{2k0-1}` (from the `coldLabel`
definition's window `|m| ≤ (2^k)²/2`). Hence `|m| ≤ 2^{2k0-1} < 2^{2k0} ≤ pq`,
and in fact `|m| ≤ 2^{2k0-1} = ½·2^{2k0} ≤ pq/2`, with strictness from the strict
prime-product inequality. So the centered rep is `m` for **all** pairs.

> **Sub-lemma `crtRepr_eq_label_of_small`:** if `a p ≡ m mod p`, `a q ≡ m mod q`,
> and `|m| < pq/2`, then `crtRepr p q (a p) (a q) = m`. Proof: `crtRepr` is by
> definition the unique integer in `(-pq/2, pq/2]` congruent to the CRT-combined
> residue; `m` is congruent (CRT) and lies in the window, so by uniqueness equals
> it. (Use the centered-rep characterization already in `CRTLatticeCore` /
> `crtRepr_congr`; mirror note 30 §1's centered-rep handling — `|E| < q` style.)

Then
`Qctrl a = ∑_{pq ∈ ctrlPairs} (m/(pq))² = m² · ∑ 1/(pq)² = m² · σ²`
(`σ² = ∑ 1/(pq)²` by `sigmaCtrl` def; pull `m²` out via `Finset.mul_sum`,
`Real.sq_sqrt` for `σ² = (√…)²`).

## Assembly

```
rcases hotSet/boundary trichotomy
· Case H: left; exact le_trans (min_le_left _ _ ▸ Rw_mono …) (blockEnergy ≤ Qctrl)
· Case B: left; exact le_trans (min_le_right _ _ ▸ Pifloor_mono …) (Xen ≤ Qctrl)
· Case D: right
    refine ⟨m, ?diag, ?large, ?energy⟩
    · exact (cold_no_exceptions + label-constant) ⇒ ∀ p, a p = m mod p
    · exact L4
    · exact L5 (via crtRepr_eq_label_of_small + sigmaCtrl def)
```

## Required new lemmas (priority order)

1. `crtRepr_eq_label_of_small` — small; pure CRT centered-rep. (L5)
2. `Rw_mono` (k ≥ 4) — small analytic induction. (L1)
3. `Pifloor_mono` / `min(Rw k0,Pifloor k0) ≤ Pifloor e0 k` — density + pow-beats-poly. (L2)
4. `cold_no_exceptions` — **the substantive D-step**; reuse Theorem-A (A3)
   per-exception energy `≥ Rw` (via `dispersion_energy_bound`) to contradict
   `¬ isHot`. (L3)

Items 1–3 are mechanical/standard; item 4 is the real content (and is the same
energy mechanism already verified inside `theorem_A_dominant_count`). Everything
else is `energy_splits` bookkeeping + `min_le`/`le_trans` + the `mainArc`/`Qctrl`
definitions. `diagSector`'s exact-energy field is the only place the centered-rep
bound (L5) is load-bearing; the label window `|m| ≤ 2^{2k0-1} < pq/2` makes it
hold unconditionally on Case D.
