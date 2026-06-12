# Aristotle delivery — Erdős 306 package cleanup

**Upload this whole folder.** It is a self-contained Lean 4 package
(`leanprover/lean4:v4.28.0` + Mathlib, see `lean-toolchain` / `lakefile.toml`).
Build with `lake build`. The package currently builds with **one intended
`sorry`**: `fourier_positivity_unconditional` in
`RequestProject/FourierPositivity.lean`. Do **not** attempt to prove that one —
it is an open analytic theorem, out of scope here.

## Success criterion

After your changes the package must still build with **no new errors** and **no
new `sorry`/`admit`** beyond that single `fourier_positivity_unconditional`.
Preserve every public lemma/def name that other files import (add aliases if you
rename). Report the final `lake build` output.

## Background (what is real vs assumed)

`erdos_306` (the main theorem) reduces, with no hidden dependencies, to the one
`sorry`. A second file `SBEE.lean` states a *parallel, unfinished* route via an
**assumed** `ConditionSBEE` structure; several of its "theorems" currently just
return their own hypotheses (`:= hbound`), and `IrvingKloostermanBound'`
concludes `True`. A large block of files (`*CRT*`, `Anchored*`, `*Cluster*`,
`SplitStarCorrelation`, …) is real, sorry-free algebra/combinatorics but is
**disconnected** from the main theorem. The tasks below make the package honest
and de-duplicated without touching the open problem.

## Tasks (in priority order)

### C1 — De-vacuize `SBEE.lean`
- The four theorems `cross_block_label_mismatch`, `peierls_collapse`,
  `ordinary_diagonal_counting`, `global_control_partition` are proved `:= hbound`/
  `:= hlb` (they return their own hypothesis). Either **delete** them (grep
  confirms nothing imports them) or **restate** them with their genuine
  conclusions proved by `sorry` (clearly marked). Do not leave hypothesis-returns.
- Restate `IrvingKloostermanBound'.bound` with its real conclusion instead of
  `True`: a nontrivial bound on `S_q(a;x) = ∑_{p∼x,(p,q)=1} e(a·p⁻¹/q)`, e.g.
  `|S_q(a;x)| ≤ C·(x^(15/16) + q^(1/4)·x^(2/3))·q^ε` for `x^(3/4) ≤ q ≤ x^(4/3)`
  (Irving, *Average Bounds for Kloosterman Sums Over Primes*, Acta Arith. 150
  (2011)). Keep it as an external **axiom/structure** — do **not** prove it.
- `irving_good_pruning` is currently vacuous (`P_star := P.primes` gives `2|P|≥|P|`).
  Restate honestly (its real content is phase dispersion) with `sorry`, or remove
  if unused downstream.

### C2 — Factor duplicated CRT-lattice machinery
`ValidCRTLattice`, `AnchoredCRTLattice`, `ReciprocalCRTProduct` repeat the same
constructions (`base_diff`, `local_residue`, `_smul`, `dvd_of_*Hit`,
`xi_eq_div`). Extract a shared generic core file and have the three instantiate
it, **preserving all exported names** so dependents
(`ResidualPrimeShellCRT`, `SplitStarCorrelation`, `AnchoredDeterminantRank`,
`AnchoredSelectionPipeline`) compile unchanged.

### C3 — Honestly label the disconnected component
Add a module-level comment to each of the rational-collision files
(`*CRT*`, `Anchored*`, `*Cluster*`, `SplitStarCorrelation`,
`PrimitiveProjectiveNormalization`, `ResidualPrimeShellCRT`) stating they are
**route-exploration not on the critical path of `erdos_306`**, and that the top
result `ResidualPrimeShellCRT.residualPrimeShellBound_of_intervalBound` *assumes*
the shell bound as a hypothesis.

(Do C1 and C3 first — they are small and high-value. C2 is a larger refactor.)
