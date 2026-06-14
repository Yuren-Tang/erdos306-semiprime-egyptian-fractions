# R2 Final Assembly Ledger

Back to [[50 R2 Construction Resolved - Gadget Cancellation and the b≥3 Reduction]]
and [[53 R2 Assembly Skeleton Bookkeeping Completed]].

This note is the assembly ledger for the remaining `CircleMethod.exists_arcConstruction`.
It is written so that the Aristotle lane (`R2MinorEstimateInterface`) and the
local-Codex lane (`R2ConcreteData`) can return independently without colliding.

## The Target

For squarefree `b` with `3 ≤ b`, construct:

```lean
Nonempty (CircleMethod.ArcConstruction T b)
```

The consumer is already verified:

```lean
CircleMethod.exists_pos_weighted_of_construction
```

so the only remaining R2 job is to populate the fields of
`ArcConstruction`.

## Concrete Shape

Use a block system `BS` at large scale and define:

```lean
Q := block-aligned mass batch
R := prime divisors of b
S := block-support primes used for gadgets
E := r2Edges BS Q R S
L := primeSupportPeriod b (blockSupport BS)
```

Mathematically, `L = b * ∏ p ∈ blockSupport BS, p` because the support is chosen
above `b`, so the primes of `b` are disjoint from the block primes.

The edge set has three parts:

```lean
ctrlEdges BS
Q
gadgetEdges R S
```

The already verified wrappers are:

```lean
r2_edges_semiprime
r2_edges_avoid
r2_edges_dvd_period
ctrlEdges_subset_r2Edges
massBatch_subset_r2Edges
gadgetEdges_subset_r2Edges
```

## Field Ledger

### Structural Fields

These should be supplied by `R2ConcreteData.lean`:

```lean
hsemi
havoid
hne
hL
hbL
heL
he0
```

Expected inputs:

- `Q.Nonempty`, or at least `ctrlEdges BS` nonempty;
- `r2_edges_semiprime`;
- `r2_edges_avoid`;
- `r2_edges_dvd_period`;
- positivity of semiprimes.

### Weight Fields

Every edge in `E` must have weight in `[1/3,2/3]`, so control and gadget edges
cannot be given zero or negligible weights.  The clean construction is the
common-theta one:

```lean
loadE := ∑ e ∈ E, (1 : ℝ) / (e : ℝ)
theta e := (1 / (b : ℝ)) / loadE
```

provided the final edge set is chosen so that:

```text
3/(2b) ≤ loadE ≤ 3/b.
```

Then:

```text
1/3 ≤ theta e ≤ 2/3
∑ e ∈ E, theta e / e = theta * loadE = 1/b
```

Thus the mass batch `Q` must be chosen after accounting for the already-fixed
load contribution of `ctrlEdges BS ∪ gadgetEdges R S`.  Equivalently, choose `Q`
so the total load, not merely the `Q`-load, lands in the common-theta window.

This is a real correction to the naive use of:

```lean
exists_blockAligned_mass_batch
```

That lemma gives a `Q` whose own load lies in `[3/(2b), 3/b]`.  It is not
directly enough after adding control and gadget edges, because the total load
could exceed `3/b`.

What final assembly actually needs is the residual version.  Let:

```lean
baseLoad :=
  ∑ e ∈ ctrlEdges BS ∪ gadgetEdges R S, (1 : ℝ) / (e : ℝ)
```

Assume:

```text
0 ≤ baseLoad
baseLoad < 3/(2b)
```

Use the generic greedy lemma `exists_subset_recip_window` with:

```text
target = 3/(2b) - baseLoad
gap    = 3/(2b)
```

Then it returns `Q` with:

```text
3/(2b) - baseLoad ≤ loadQ ≤ 3/b - baseLoad
```

so:

```text
3/(2b) ≤ baseLoad + loadQ ≤ 3/b.
```

This residual batch lemma should be a separate small Lean target.  It can reuse
`blockPrimes_product_load_ge` and `exists_subset_recip_window`; the only new
large-scale input is `baseLoad < 3/(2b)`, supplied later by making control and
gadget edges sufficiently high-scale/light.

The formal target is:

```lean
hlb : ∀ e ∈ E, 1/3 ≤ theta e
hub : ∀ e ∈ E, theta e ≤ 2/3
hmass : (∑ e ∈ E, theta e / (e : ℝ)) = 1 / (b : ℝ)
```

This remains one of the genuine assembly obligations.

### Main-Arc Fields

Use:

```lean
exists_mainArc_bijection L N
fourierTerm_eq_term_label_of_modL
```

This supplies:

```lean
hpart
hdisj
hmaps
hinj
hsurj
hterm
```

provided:

```lean
0 ≤ N
2 * N + 1 ≤ (L : ℤ)
∀ e ∈ E, e ∣ L
b ∣ L
0 < L
∀ h ∈ SM, (L : ℤ) ∣ ((h : ℤ) - lbl h)
```

The bijection lemma already gives the last congruence.  Thus the remaining work
is choosing `N` large enough for `hN` but small enough for `2 * N + 1 ≤ L`.
Since `L` is enormous and `1 / σ_E` is only polynomial/exponential in the block
scale, this is a large-scale inequality.

### Main Smallness Fields

These are:

```lean
hN
htw
hsmall
```

They should be discharged by taking:

```lean
N ≈ ceil (C / Real.sqrt (sigmaE2 E theta))
```

with `C ≥ 1` fixed after the block-minor tail constant is known.

The proof obligations reduce to:

- `1 / sqrt(sigmaE2 E theta) ≤ N`;
- for all `|m| ≤ N` and all `e ∈ E`,
  `|(m : ℝ) / (e : ℝ)| ≤ 1/10`;
- the cubic Taylor error
  `∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3 ≤ 1/10`.

All are large-`k0` obligations.  They should not be mixed into the minor-arc
interface file.

### Minor-Arc Field

Split:

```lean
Sm = blockMinorPart Sm Sblock ∪ extraMinorPart Sm Sblock Sextra
```

The finite splitter is verified:

```lean
r2_minor_bound_split
```

The Aristotle lane should return wrappers producing:

```lean
hblock :
  ‖∑ h ∈ blockMinorPart Sm Sblock, fourierTerm E theta b L h‖ ≤ Bblock

hextra :
  ‖∑ h ∈ extraMinorPart Sm Sblock Sextra, fourierTerm E theta b L h‖ ≤ Bextra
```

or a sum/norm-compatible variant.  Then:

```lean
Bm := Bblock + Bextra
hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm
```

The block part uses:

```lean
minor_arc_bound_fiber_tail
```

with `K = b` or a constant depending only on `b` and the selected gadget
coordinates.

The extra part uses:

```lean
gadget_charFun_damp
```

repeated over `G` gadget primes per prime divisor of `b`.

## The `hbeat` Chase

Let:

```text
c3 = 0.8 * (Real.exp (-(Real.pi^2/2)) / 2)
```

The target is:

```lean
Bm < c3 / Real.sqrt (sigmaE2 E theta)
```

The intended quantitative form is:

```text
Bblock ≤ K * (η + Ctail * exp (-C^2 * 8/9)) / sigmaCtrl BS
Bextra ≤ c3 / (2 * sigmaCtrl BS)
sqrt(sigmaE2 E theta) ≤ sigmaCtrl BS
```

Then it is enough to choose:

```text
K * (η + Ctail * exp (-C^2 * 8/9)) < c3 / 2.
```

Parameter order:

1. Fix `eps = 1`.
2. Choose `K` from the fiber-tail/gadget setup.
3. Set `η = c3 / (4*K)`.
4. Apply `minor_arc_bound_fiber_tail` to get `k0min, Ctail`.
5. Choose `C` so that
   `K * Ctail * exp (-C^2 * 8/9) < c3 / 4`.
6. Choose `G` so that extra-minor damping gives
   `Bextra ≤ c3 / (2 * sigmaCtrl BS)`.
7. Choose `k0` large enough for:
   - `k0min ≤ BS.k0`;
   - mass batch existence;
   - gadget supply;
   - `2 * N + 1 ≤ L`;
   - `htw` and `hsmall`;
   - light-extra:
     `∑ e ∈ E \ ctrlEdges BS, 1 / (e : ℝ)^2 ≤ 3 * sigmaCtrl BS ^ 2`.

The last bullet feeds:

```lean
sigmaE_le_sigmaCtrl_of_extra_light
```

## Remaining Coupled Problems

After the two parallel lanes return, the still-coupled human/assembly tasks are:

1. exact mass with all nonzero weights in `[1/3,2/3]`;
2. large-`k0` inequalities for `hbound`, `hN`, `htw`, `hsmall`, and light-extra;
3. choosing `S` so there are `G` disjoint gadget primes per prime divisor of `b`;
4. proving that the block/extra minor partition covers `Sm`;
5. final `ArcConstruction` record construction.

The mathematical sign remains positive: the remaining work is genuinely coupled,
but it is not diffuse.  The critical analytic estimates are already banked or
assigned; the final obstruction is the exact construction/parameter ledger.
