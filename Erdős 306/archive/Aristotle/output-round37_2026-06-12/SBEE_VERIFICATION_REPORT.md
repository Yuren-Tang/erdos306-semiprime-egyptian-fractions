# SBEE single-block counting — verification report

This report records, per theorem, what verifies and what remains a `sorry`, with a
one-line reason for each gap. The build stays **green** (`lake build` succeeds;
only `sorry`/linter warnings remain).

## Repository note

The delivered snapshot had all `.lean` files flattened to the project root, while
they `import RequestProject.X` and the lakefile globs `RequestProject.+`. The
files were moved into `RequestProject/` (their intended location, per
`REGENERATE.sh`) so the project builds. No source content was changed by the move.

New files added:

- `RequestProject/SBEEDispersion.lean` — P1 (Lemma D, dispersion corollary, Thm C)
- `RequestProject/SBEEForcing.lean` — P2 (Theorem A, Lemma E, Theorem B)
- `RequestProject/SBEEAssembly.lean` — P3 (`SBEEPartitionBound`, assembly)

## P1 — Lemma D and Theorem C

### Lemma D (`29 §2`) — **FULLY PROVED, no sorry** ✅
`SBEEDispersion.lemmaD` (and helper `lemmaD_fiber`).
`#print axioms` = `[propext, Classical.choice, Quot.sound]` only.

- `lemmaD_fiber`: for fixed `u`, at most `2` primes `p∈[X,2X]` with `u·p≡w (mod q)`.
- `lemmaD`: `#{(u,p): |u|≤U, p∈[X,2X] prime, u·p≡w (mod q)} ≤ 2(2U+1)`.

**Verification finding (a real simplification).** The paper's hypothesis `U < X`
(used to make `u` invertible mod `q` via `|u| < q`) is **not needed**: `q ∤ u`
follows directly from `q ∤ w` (if `q ∣ u` then `q ∣ u·p`, hence `q ∣ w`). The
`U < X` hypothesis is kept on `lemmaD` only to match the paper's literal statement
(marked `_hUX`, unused); the fiber bound holds for every integer `u`. So Lemma D
is true and slightly more general than stated.

### Dispersion corollary (`30 §1`)

- `dispersion_energy_bound` — **PROVED conditionally on `dispersion_residue_count`** ✅
  The reduction `∑_{p∈F} ‖E·q̄/p‖² ≥ |F|³/(2¹¹X²)` is proved cleanly from the
  residue count (half the primes have phase `> δ=|F|/32X`, each `> δ²`); its own
  body has **no** `sorry` (it transitively depends only on the residue-count
  `sorry`). The constant chase `(|F|/2)·δ² = |F|³/(2¹¹X²)` checks out
  (`2·32² = 2·1024 = 2¹¹`).
- `dispersion_residue_count` — **`sorry`.** Reason: needs the
  `‖E·q̄/p‖ ≤ δ ⟹ p ∣ E−u·q (|u|≤2δX)` reduction and the "a nonzero integer
  `< X³` has `≤ 2` prime factors in `[X,2X]`" step, feeding `lemmaD`. Requires the
  fractional-norm / modular-inverse layer (the `phase` function is defined
  faithfully as distance-to-nearest-integer of `E·(q : ZMod p)⁻¹.val / p`).

### Theorem C (`30 §1`) — **`sorry`** (`fingerprint_count`)
Reason: bundles (i) the phase-identity slack `|H| ≥ pq‖·‖ − q`, (ii) cold rigidity
(uniqueness of the cold residue, using the *un-recentered* centered integer
representative — the subtlety flagged in the "Verification note" of `30 §1`), and
(iii) the entropy bookkeeping `3h log X ≤ εR/2 ⟺ R ≥ R_C`. Stated faithfully
against `QP`; the analytic estimates are isolated as this single `sorry`.

## P2 — Theorem A, Lemma E, Theorem B (`SBEEForcing.lean`)

All stated faithfully against the concrete CRT energy (`QP`, `sigmaP`,
`BlockAssignment`, `crtRepr`); each is an isolated `sorry`:

- `theorem_A_dominant_count` (Theorem A, `29 §3`) — `sorry`: the per-exception
  energy accounting (A3, via Lemma D over `QP`) and exception entropy (A4).
- `lemma_E_cross_label_energy` (Lemma E, `29 §5`) — `sorry`: choice of `δ`, the
  discard of the `≤2` prime divisors of `n'−n`, and the energy accounting.
- `theorem_B_nondominant_forcing` (Theorem B, `29 §6`) — `sorry`: the covering
  construction (`29 §4`) + Lemma E + the tiny-mass / `M₂ ≥ ρN/2` accounting (the
  soft spot flagged in the task).
- `corollary_SBEE_below_window` (`29 §7`) — `sorry`: direct A+B combination.

## P3 — assembly (`SBEEAssembly.lean`)

- `IrvingGood` — defined faithfully (no free labeling) as the dyadic-window +
  density regime `P ⊆ [X,2X]` prime with `|P| ≥ X/(2 log X)`. This is the
  hypothesis the unconditional `29`/`30` proof actually uses; it is genuinely
  restrictive (sparse / non-dyadic blocks fail it), so the target is not vacuous.
- `SBEEPartitionBound` — defined exactly per note 28 §3 (uniform `C` outside
  `∀P`, `IrvingGood` hypothesis, `2 ≤ P.card`, no labeling).
- `single_block_counting : SBEEPartitionBound c` — `sorry`: the A+B+C trichotomy
  on `R` (mesh `R_C < R_w`, asymptotic) plus the Laplace transform from the
  level-set bound to the partition function. Rests on the P1/P2 sorries.

## Summary table

| Statement | File | Status |
|---|---|---|
| Lemma D (`lemmaD`, `lemmaD_fiber`) | SBEEDispersion | **Proved (no sorry)** |
| Dispersion energy bound | SBEEDispersion | Proved ⟸ residue count |
| Dispersion residue count | SBEEDispersion | `sorry` |
| Theorem C (`fingerprint_count`) | SBEEDispersion | `sorry` |
| Theorem A (`theorem_A_dominant_count`) | SBEEForcing | `sorry` |
| Lemma E (`lemma_E_cross_label_energy`) | SBEEForcing | `sorry` |
| Theorem B (`theorem_B_nondominant_forcing`) | SBEEForcing | `sorry` |
| Corollary below window | SBEEForcing | `sorry` |
| `single_block_counting` (= SBEE) | SBEEAssembly | `sorry` |

## Soft spots examined (per the task's "Notes for the verifier")

- **Lemma D invertibility / `U<X`**: the `U<X` hypothesis is unnecessary — `q∤u`
  comes from `q∤w` alone. (Confirmed by the formal proof.)
- **`G_F` constant chase**: `(|F|/2)·(|F|/32X)² = |F|³/(2¹¹X²)` — verified in the
  proved `dispersion_energy_bound`.
- **Centered-representative discipline (`30 §1`)**: encoded in the docstring of
  `fingerprint_count`; the *un-recentered* integer difference is what the cold
  rigidity argument must use. Not yet machine-checked (inside the `sorry`).
- **Phase-identity slack, Theorem B covering bookkeeping, mesh `R_C ≪ R_w`**:
  isolated inside `fingerprint_count` / `theorem_B_nondominant_forcing` /
  `single_block_counting` respectively. Not yet machine-checked.

No counterexample to any stated step was found; the only correction surfaced is
that Lemma D's `U < X` hypothesis is superfluous.
