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

Completed port nodes include `BernoulliFourier`, `GlobalPeierlsBookkeeping`,
`SBEEDispersion`, `SBEEFingerprint`, `SBEEForcing`, `SBEEAssembly`, and
`GlobalControl`.  `GlobalControl` now builds cleanly without warnings or tactic
diagnostics.  Its former monolith has been decomposed into `Basic`,
`CrossBlockEnergy`, `BlockEncoding`, `BlockEntropy`, and `ColdBlockBounds`, with
the independent Gaussian estimate in `GlobalControl.GaussianIntegerSum`.  Every extracted
node and the compatibility aggregate build on v4.31.  The downstream
The downstream nodes now live under mathematical paths:
`GlobalControl.LevelSetData`, `GlobalControl.LevelSetAssembly`,
`GlobalControl.Localization`, `GlobalControl.LaplaceAboveFloor`, and
`GlobalControl.Partition`.  They build without diagnostics; their historical
G-numbered paths remain temporary compatibility imports.  The next task is to
audit the final public import chain and then continue the same mathematical
decomposition in the next historical monolith.

The original strictly sequential rule (finish the complete port before moving
modules) is too expensive for large historical files.  Use a node-based hybrid:

1. repair a coherent mathematical node under the broad environment until its
   statement and proof are green;
2. narrow its imports, and place an olean boundary around it only when the node
   is also a genuine mathematical unit;
3. continue the port from that boundary;
4. postpone broad public renames until the containing route is green.

For a red monolithic file, a green prefix may be extracted before the rest of
the file is ported only when it has an independently meaningful mathematical
contract.  Compilation speed alone does not justify turning bookkeeping into a
module; remote CI may absorb that cost while the mathematical architecture
stays faithful to the paper.

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
Use [`docs/architecture.md`](architecture.md) as the naming and public-interface
contract for this migration.

Proposed structure:

```text
RequestProject/
  Core/                  # basic definitions, reductions, dyadic blocks
  Analytic/              # PNT/Mertens boundary and dyadic prime supply
  Spectral/              # finite spectral selection principles
  CircleMethod/          # arcs, main/minor arc decomposition
  LocalEnergy/           # single-block energy and forcing package
  GlobalControl/         # global bookkeeping and Peierls/control lemmas
  ResonantConstruction/  # dyadic semiprime construction and final arc witness
  Public/                # stable public theorem facades
  Audit.lean       # final audit entry point
  Erdos306FormalConjectures.lean
```

Recommended migration rule: add compatibility shims first, move imports in small
batches, then delete shims only after the import graph is stable.
Historical working names such as `R2`, `cannon`, `gadget`, `endgame`, `lane`,
`supply`, and `certificate` should be kept out of new public names unless they
are part of an explicitly temporary shim.

Deliverable: a shallower import graph with clear public interface files for each
layer.

Current progress:

- stable public facade: `RequestProject.Public.Erdos306`;
- stable spectral facades: `Spectral.Selection` and
  `Spectral.CircleMethodBridge`;
- `SpectralCannon` and `GlobalPeierlsBookkeeping` have narrowed Mathlib imports;
- the local-energy route is being separated at the phase/dispersion,
  fingerprint-rigidity, entropy, dominant-forcing, and nondominant-forcing
  nodes;
- the obsolete dependency `BlockCRTEnergy -> SBEE` has been removed: the
  concrete CRT energy layer does not depend on the deprecated conditional SBEE
  placeholder chain.
- the local-energy route through `BlockCRTEnergy`, `SBEEDispersion`,
  `SBEEFingerprint`, `SBEEForcing`, and `SBEEAssembly` now builds cleanly on
  v4.31 with narrowed imports; the dependency closure fell from roughly 8.5k
  to 3.1k jobs;
- the historical `GlobalControl.lean` monolith has been replaced by the
  mathematical module chain documented in `docs/architecture.md`; the old
  G5/G6/G7 paths are now compatibility imports only;
- the level-set, localization, above-floor Laplace, and partition assemblies
  build through their mathematical paths, and `CircleMethodArcs` consumes the
  canonical `global_control_partition` theorem directly;
- keep `Spectral.CircleMethodBridge` as the stable handoff contract now, but
  postpone its internal declaration renames and final implementation split
  until both finite spectral selection and the circle-method/global-control
  side build cleanly against their own facades.

### Lessons from the global-control route

1. **Repair before moving.** Port a coherent theorem node under the broad
   environment, make its output quiet, and only then move it behind a module
   boundary. This separates mathematical errors from import-path errors.
2. **Split by handoff theorem.** The useful boundaries were not equal-sized
   source chunks: they were the block/sigma interface, cross-block mismatch
   penalty, assignment encoding, entropy absorption, cold-block boundary bound,
   localization dichotomy, and final partition theorem.
3. **Use direct imports.** Moving the route exposed accidental reliance on
   transitive imports (`GlobalPeierlsBookkeeping` in particular). Every module
   should state the mathematical dependencies it actually uses.
4. **Treat `convert` as a diagnostic smell.** Most v4.31 failures came from
   `convert` generating equality goals between typeclass projections. Stable
   replacements were `calc`, `simpa` after a named definition, or an explicit
   pointwise equality.
5. **Keep bookkeeping compressed after diagnosis.** Expanded ring/field
   calculations were useful to expose the invariant, but mature proofs were
   folded back to the smallest stable normalization step.
6. **Separate canonical names from compatibility.** Historical route numbers
   remain useful in comments and paper cross-references; module and theorem
   names should state the mathematics. Thin compatibility imports/aliases make
   that migration reversible until full CI is green.
7. **Validate at confluences.** Local module builds caught port errors cheaply;
   `CircleMethodArcs` then verified the first external consumer. The clean
   checkout build and axiom gate remain CI responsibilities.

### Remaining order

1. Push this checkpoint and require the clean CI build, source lint, workflow
   lint, and exact two-axiom audit to pass.
2. After CI, remove G-numbered compatibility imports only when `rg` and the
   public import closure show no external use; keep theorem aliases for one
   additional migration interval if useful.
3. Audit the circle-method layer as the next confluence, but avoid reopening the
   now-green global-control or local-energy sources without a mathematical
   reason.
4. Decompose the `R2*` resonant-construction tree by mathematical ownership:
   reciprocal-mass reservoir, frequency selection, damping edges, support and
   budget estimates, and terminal semiprime assembly. Introduce canonical
   `ResonantConstruction/` paths before deleting historical files.
5. Finish by making `Public.Erdos306` and `Audit` the only supported external
   entry points and deleting compatibility layers proved dead by the import
   graph.

## Stage E — deletion pass

The former `RequestProject.RSPrimeSums` compatibility shim has now been removed after the active import graph was moved to `RequestProject.AnalyticInputs`.  Continue deleting obsolete historical files only after stages B--D make their replacements explicit.
Use the import graph and `rg` checks to prove that a file or declaration is truly
unreferenced.

Deliverable: no dead compatibility layers, no stale Rosser--Schoenfeld naming in
active code unless it appears only in historical documentation or source-citation prose.
