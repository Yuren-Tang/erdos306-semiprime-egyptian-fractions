# SBEE V5 forcing-layer + assembly — verification report

Scope: TASK.md P1 (Lemma E), P2 (Theorem A), P3 (Theorem B), P4 (assembly).
All work is in `RequestProject/SBEEForcing.lean` and `RequestProject/SBEEAssembly.lean`,
on top of the already-verified `SBEEDispersion.lean` (Lemma D) and
`SBEEFingerprint.lean` (Theorem C, `fingerprint_count`).

## `lake build`

The whole package builds successfully (`Build completed successfully (8054 jobs)`).

**Packaging fix (was blocking the build).** As delivered, every `.lean` source sat
at the repository root, but `lakefile.toml` declares the library `RequestProject`
with glob `RequestProject.+` and every file uses `import RequestProject.…`. On a
case-sensitive Linux filesystem nothing resolved and `lake build` failed
immediately (`no such file or directory … RequestProject/SBEEForcing.lean`). Fix:
moved all sources into a `RequestProject/` subdirectory so the module names match
the library layout. No source content was changed by this move.

## Remaining `sorry`s (per theorem)

| Declaration | File | Status |
|---|---|---|
| `lemmaE_fiber` | SBEEForcing | **proved (new)** |
| `lemmaE_close_count` | SBEEForcing | **proved (new)** |
| `lemma_E_cross_label_energy` (Lemma E, P1) | SBEEForcing | **proved (new), sorry-free** |
| `theorem_A_dominant_count` (Theorem A, P2) | SBEEForcing | `sorry` (unchanged) |
| `theorem_B_nondominant_forcing` (Theorem B, P3) | SBEEForcing | `sorry` (unchanged) |
| `single_block_counting` (assembly, P4) | SBEEAssembly | `sorry` (unchanged) |

`#print axioms lemma_E_cross_label_energy` → `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`), and likewise for both helper lemmas.

## P1 — Lemma E: a statement bug, then a full proof

### Bug found (this is the most valuable finding for P1)

The V5 statement of `lemma_E_cross_label_energy` is **false as written**: it omits
the hypotheses that the elements of `C` and `C'` are primes in `[X, 2X]`.

`crtRepr p q · ·` is *defined to return `0` when `p, q` are not coprime*
(`BlockCRTEnergy.lean`). So if one takes `C, C'` to be, say, sets of even composite
numbers, every cross term `crtRepr p q …` is `0`, the left-hand sum is `0`, while
the right-hand side `c·|C|³|C'|/X²` is strictly positive — a direct counterexample.
The paper (`29 §5`) explicitly takes `C, C'` to be "disjoint sets of primes in
`[X,2X]`", and the reduction to Lemma D needs `q` prime with `X ≤ q`.

Fix: two added hypotheses
```
(∀ p ∈ C, Nat.Prime (p:ℕ) ∧ X ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*X)
(∀ q ∈ C', Nat.Prime (q:ℕ) ∧ X ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*X)
```
These are exactly the regime in which Theorem B uses Lemma E (it applies it to the
prime classes `C_n ⊆ P ⊆ [X,2X]`), so the fix is faithful and non-restrictive.

### Proof delivered

With the fix, Lemma E is proved in full, sorry-free, with absolute constant
`c = 1/8192`, decomposed exactly along `29 §5`:

* `lemmaE_fiber` — for a fixed prime `q ∈ [X,2X]` with `q ∤ (n'−n)`, the primes
  `p ∈ C` whose representative is `δ`-small inject into `SBEEDispersion.lemmaD_set`
  via `p ↦ (u, p)` with `H_{pq} − n = u·p` and `u·p ≡ n'−n (mod q)`. `lemmaD` then
  bounds the fiber by `2(2(2δX + B/X)+1)`. (The `U < X` side-condition of `lemmaD`
  holds because `2δX + B/X ≤ 3X/4 < X`.)
* `lemmaE_close_count` — sums the fibers over `q ∈ C'`. The `≤ 2` primes `q` that
  divide `d = n'−n` are discarded with `SBEEDispersion.card_prime_factors_dyadic_le_two`
  (valid since `0 < |d| ≤ 2B ≤ X²/2 < X³`), contributing `≤ |C|` pairs each.
* The main lemma chooses `δ = |C|/(64X)` (so `δ ≤ 1/4` from `|C| ≤ X+1`), shows the
  close pairs number `≤ |C||C'|/2` (using `|C| ≥ 32(B/X+1)` and `|C'| ≥ 8`), hence
  at least `|C||C'|/2` cross pairs carry `(H/pq)² > δ²`, giving energy
  `≥ (|C||C'|/2)·δ² = |C|³|C'|/(8192 X²)`.

I re-derived the constant chase independently; the `δ = min(¼, |C|/(64X))` recipe
of the note works (in fact `|C|/(64X) ≤ 1/32 ≤ ¼` always, so the `min` is moot),
and the three accounting inequalities close as claimed.

## P2 — Theorem A (dominant count): still `sorry`

`theorem_A_dominant_count` remains a `sorry`. The proof in `29 §3` is correct as an
argument, but its Lean formalization needs infrastructure that is not present:

* (A1) label uniqueness — a "product of `≥ N/2` distinct primes `≥ X` divides
  `m−m'`" lower bound, then `|m−m'| ≤ X²` forces `m = m'`.
* (A2) label range — a comparison `σ_{C_m}² ≥ (1−ρ)²/24 · σ_P²` of restricted pair
  sums, giving `|m| ≤ (5/(1−ρ))√R/σ_P`.
* (A3) per-exception energy `≥ N³/2¹⁵X²` — this is the one step that is genuinely a
  Lemma-D application (the same engine as Lemma E, with `w = a_q − m`); it is the
  most tractable A-ingredient and could reuse `lemmaE_fiber`/the close-count idea.
* (A4) the **exception-set entropy bookkeeping** — `#{dominant a : QP ≤ R}` is
  bounded by (label choices) × (Σ_e binom(N,e)(2X)^e), with `e ≤ 2¹⁵RX²/N³` from
  (A3) and `3e log X ≤ εR` for `X ≥ X₀(ε)`. This binomial/entropy counting against
  the concrete `BlockAssignment` product space is the bulk of the missing work and
  was not formalized.

No error was found in the §3 argument; the gap is purely the amount of unbuilt
counting infrastructure (A4) and the restricted-σ comparison (A2).

## P3 — Theorem B (non-dominant forcing): still `sorry`

`theorem_B_nondominant_forcing` remains a `sorry`. It is the natural consumer of
the now-proved Lemma E, but its `29 §4`+`§6` proof needs the **covering
construction**, none of which is yet formalized:

* base-point selection by averaging: `∑_{p₀} #{q : |H_{p₀q}| > B} = 2·#{pairs |H|>B}
  ≤ 32RX⁴/B²`, so some `p₀` has `≤ 32N/A²` far vertices;
* the short list `L` and the residue classes `C_n = {q : H_{p₀q} = n}` (disjoint,
  each with constant residue `n`, covering all but `≤ 32N/A²+1` vertices);
* the mass accounting `M₂ ≥ ρN/2` for the substantial mass outside the largest
  class (the "soft spot" flagged in the task), including the case split
  (one big secondary class vs. spread), then Lemma E to get
  `R ≥ c(M₂/2)⁴/(|L|²X²) ⇒ R ≥ c'X/log³X`.

A reusable bridge that will be needed here (and is straightforward) is
`∑_{p∈C}∑_{q∈C'}(H/pq)² ≤ QP P a` for disjoint prime classes `C, C' ⊆ P`
(each unordered cross pair appears once and all `QP` terms are nonneg; it needs the
symmetry `crtRepr p q = crtRepr q p` of the centered representative). This was not
added because it is only useful once the covering construction above is in place.

I checked the §6 constants (`A² ≥ 128/ρ`, `s₀ = 32(B/X+1)+8`, the `M₂ ≥ ρN/2`
accounting): they are internally consistent. No mathematical error was found; the
gap is the (large) covering/mass-accounting formalization.

## P4 — assembly `single_block_counting`: still `sorry`

`single_block_counting` (target `SBEEPartitionBound c`) remains a `sorry`. Beyond
depending on A and B, it requires:

* the `R`-trichotomy wiring (`R < R_w` → A via B; `R_w ≤ R ≤ R_triv` → Theorem C
  `fingerprint_count`, which **is** proved; `R > R_triv` trivial), and the mesh
  `R_C ≤ R_w`, which note 30 itself only claims asymptotically (crossover near
  `X ≈ 10³⁵` with the crude constants) — so in Lean this must be carried as an
  `X ≥ X₁` hypothesis or an explicit large constant, as TASK.md anticipates;
* the **Laplace transform** from the level-set bound `N(R) ≤ …` to the
  partition-function bound `∑_a e^{−cQ} ≤ C/σ_P` (`∑_a e^{−cQ} = ∫ N(R)·c e^{−cR} dR`
  with `c > 2ε`). This is the genuinely analytic missing piece and was not built.

## Audit notes / flags

* **Lemma E hypotheses (fixed).** The missing prime/window hypotheses are a real
  correctness bug, not cosmetic; see the counterexample above.
* `SBEEDispersion.dispersion_energy_bound`'s docstring still says
  "**Status**: `sorry`", but the declaration is in fact fully proved (the comment
  is stale). Not changed, since it is outside this task's files.
* The §3/§6 paper arguments check out where I verified them (constants, the `δ`
  recipe, the divisor discard, the mass accounting bookkeeping). The remaining gaps
  are formalization volume (covering construction, entropy counting, Laplace), not
  mathematical errors.
