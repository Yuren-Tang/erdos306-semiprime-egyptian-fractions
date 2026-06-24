# Refactor roadmap: analytic inputs, toolchain, lint, and module structure

This project now has a small analytic audit boundary, but the rest of the codebase
is still a flat, historical development tree.  The next cleanup should be done in
coordinated stages rather than as one unreviewable mega-patch.

## Why not one all-at-once rewrite?

The requested items are mathematically related, but they have different failure
modes:

1. **Analytic-input migration** changes the formal trust boundary and must keep
   the `#print axioms erdos_306` audit exact.
2. **Lean/Mathlib upgrade** changes elaboration, tactic behavior, and library API.
3. **Warning/linter cleanup** is mostly mechanical but touches many proofs.
4. **Directory/module reorganization** changes import paths and risks accidental
   import cycles or hidden dependency expansion.
5. **Deleting obsolete material** is safest only after the new import graph is
   stable.

Doing all five at once would make it hard to tell whether a failure is
mathematical, tactical, or merely organizational.  The recommended workflow is a
short branch stack: each branch builds, audits, and leaves exactly the same two
non-standard analytic axioms.

## Stage A — analytic boundary hardening

Goal: make the new PNT/Mertens boundary semantically clean before moving files.

- Keep exactly two non-standard axioms:
  - `GlobalControl.pnt_dyadic_prime_density`;
  - `GlobalControl.mertens_dyadic_window_mass`.
- Keep stable downstream wrappers:
  - `GlobalControl.dyadic_prime_density`;
  - `GlobalControl.dyadic_mertens_cumulative`.
- Add a later bridge layer if we decide to axiomatize more primitive asymptotic
  statements (`Filter.Tendsto` / `IsEquivalent`) and prove the dyadic corollaries
  inside Lean.

Deliverable: `RequestProject.AnalyticInputs` remains the only analytic axiom leaf,
and `RequestProject.Audit` prints only the two audited axiom names.

## Stage B — Lean/Mathlib v4.31 port

Goal: port without changing theorem statements or module layout.

Observed blockers from the mechanical bump: `GlobalPeierlsBookkeeping.lean`
first fails around a geometric-sum normalization proof; after a local repair, the
next failures occur in `BernoulliFourier.lean` and `SBEEDispersion.lean`, mainly
around fragile `convert`, `ring`, and `grind` proof scripts.  Start with these
files, then continue module-by-module.  This stage should avoid broad renames so
any failure is clearly a toolchain/tactic migration issue.

Expected edits:

- replace deprecated names;
- simplify fragile `ring`/`ring_nf` endings;
- remove tactic calls that became no-ops;
- prefer newer Mathlib lemmas where they reduce proof scripts.

Deliverable: `lake build RequestProject.Erdos306FormalConjectures` passes on
Lean/Mathlib `v4.31.0` and the audit still lists only the two analytic axioms.

## Stage C — warning/linter cleanup

Goal: make normal builds quiet enough that real regressions are visible.

Prioritize warnings that are deterministic and local:

1. deprecated declarations;
2. unused variables by renaming to `_` or deleting binders;
3. unused `simp` arguments;
4. `simpa` -> `simp` suggestions;
5. no-op tactics;
6. repeated `ring` suggestions where a stable `ring_nf` proof is possible.

Do not blindly apply every informational note.  Some `ring` suggestions are not
warnings and can make proofs more brittle; use them only when the replacement is
stable on the target toolchain.

Deliverable: build output has no warnings for project files on the target
Lean/Mathlib version, or the remaining warnings are documented with a reason.

## Stage D — module and directory reorganization

Goal: move from one flat `RequestProject` directory to a mathematical layout.

Proposed structure:

```text
RequestProject/
  Analytic/        # PNT/Mertens boundary and dyadic prime supply
  Core/            # basic definitions, dyadic blocks, arithmetic support
  GlobalControl/   # global bookkeeping and Peierls/control lemmas
  CircleMethod/    # arcs, main/minor arc decomposition, Fourier positivity
  SBEE/            # SBEE dispersion/forcing/assembly material
  R2/              # R2 certificates, components, mass batch, final assembly
  Audit.lean       # final audit entry point
  Erdos306FormalConjectures.lean
```

Recommended migration rule: add compatibility shims first, move imports in small
batches, then delete shims only after the import graph is stable.

Deliverable: a shallower import graph with clear public interface files for each
layer.

## Stage E — deletion pass

The former `RequestProject.RSPrimeSums` compatibility shim has now been removed after the active import graph was moved to `RequestProject.AnalyticInputs`.  Continue deleting obsolete historical files only after stages B--D make their replacements explicit.
Use the import graph and `rg` checks to prove that a file or declaration is truly
unreferenced.

Deliverable: no dead compatibility layers, no stale Rosser--Schoenfeld naming in
active code unless it appears only in historical documentation or source-citation prose.
