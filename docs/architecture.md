# Architecture and naming plan

This document fixes the intended mathematical architecture before the module
tree is reorganized. Public names and module boundaries should state their
mathematical role; historical working names are removed when their mathematical
replacement is verified at its first consumers.

## Public spine

The final project should expose a short public spine:

```text
Core definitions
  -> structural analytic inputs
  -> finite spectral selection
  -> circle-method arc construction
  -> resonant dyadic semiprime construction
  -> Erdős 306 theorem
  -> audit entry point
```

The public theorem surface should be:

- `Erdos306.erdos_306`, matching the Formal Conjectures statement.
- A project-native theorem for semiprime Egyptian representations, kept as a
  stable bridge for the formal-conjectures theorem.
- An audit file that imports only the public theorem and prints the theorem,
  its axioms, and the two structural analytic inputs.

Everything else should be treated as internal proof infrastructure unless it is
explicitly documented as a module output.

## Module layers

The target directory tree is:

```text
RequestProject/
  Core/                  # semiprimes, representations, reductions, dyadic blocks
  Analytic/              # PNT/Mertens structural input boundary
  Spectral/              # finite spectral selection principles
  CircleMethod/          # Fourier arcs and arc-construction interface
  LocalEnergy/           # single-block energy and forcing package
  GlobalControl/         # block-system control and minor-arc partition bounds
  ResonantConstruction/  # dyadic semiprime construction and final arc witness
  Public/                # stable public theorem facades
  Audit.lean
```

Each layer should eventually have a public import file.  Downstream modules
should import public files rather than reaching into internal construction
files.

The current Core source chain is:

```text
Core.Asymptotics  (shared growth thresholds)
Core.LevelSetLaplace  (abstract level-set-to-partition conversion)
Core.SmallBallEnergy  (small-ball counts imply quadratic-energy bounds)
Core.ShortIntervalCongruence  (short intervals contain at most one residue representative)
Core.UnitCircleResidue  (unit-circle norms via `ZMod.valMinAbs`)

Core.Semiprime
  -> Core.EgyptianRepresentation
     -> Core.UnitNumeratorReduction
     -> Core.SquarefreeNecessity  (independent paper-side corollary)
```

The former `Defs` aggregate and conditional `MainTheorem -> SBEE` chain have
been removed from the active project graph.

### Local-energy handoff

Global control consumes the single-block theory through three mathematical
contracts:

```text
LocalEnergy.CRTModel
  -> LocalEnergy.ReciprocalDispersion
     -> LocalEnergy.FingerprintCounting
     -> LocalEnergy.CrossLabelEnergy
        -> LocalEnergy.DominantLabel.Basic
           -> LocalEnergy.DominantLabel.Counting
           -> LocalEnergy.DominantLabel.Forcing
              -> LocalEnergy.DominantLabel.ColdBounds
        -> LocalEnergy.LevelSet

Core.SmallBallEnergy
Core.ShortIntervalCongruence
Core.UnitCircleResidue
LocalEnergy.CRTModel
  -> LocalEnergy.AdjacentScaleEnergy
     -> GlobalControl.CrossBlockEnergy

Core.LevelSetLaplace
  -> LocalEnergy.LevelSet
```

- `CRTModel`: finite residue assignments, Mathlib-centered CRT representatives,
  quadratic block energy, and the block deviation scale;
- `ReciprocalDispersion`: linear-congruence fiber counts and reciprocal-phase
  small-ball/energy bounds on `UnitAddCircle`;
- `FingerprintCounting`: CRT-to-phase comparison, uniqueness below the
  dispersion threshold, fingerprint decoding, and entropy counting;
- `CrossLabelEnergy`: close-pair congruence counts and the energy forced between
  two distinct residue classes;
- `DominantLabel.Basic`: the dominant-label predicate;
- `DominantLabel.Counting`: label recovery, exception energy, and entropy
  counting for dominant assignments;
- `DominantLabel.Forcing`: covering and class-mass arguments forcing energy in
  the absence of a dominant label;
- `DominantLabel.ColdBounds`: the low-energy merger of the counting and forcing
  branches, including label and exception bounds;
- `LevelSet`: the uniform single-block level-set and partition-function bounds.

The public names describe the mathematics (`HasDominantLabel`,
`nondominant_energy_lower_bound`, `block_level_set_bound`, and
`RequestProject.partition_function_bound_of_level_sets`) rather than historical
proof-note labels. General growth thresholds live in `Core.Asymptotics`, while
the abstract Laplace conversion lives in `Core.LevelSetLaplace`; neither is
owned by the local-energy theory.

Global-control modules import these mathematical contracts rather than
historical implementation paths. Physical migration and canonical namespace
renaming proceed one mathematical node at a time.

### Global-control proof graph

The first mathematical decomposition of the former monolithic
`GlobalControl.lean` is now:

```text
GlobalControl.BlockSystem
  -> GlobalControl.Basic
  -> GlobalControl.CrossBlockEnergy
     -> GlobalControl.BlockEncoding
        -> GlobalControl.BlockEntropy
           -> GlobalControl.ColdBlockBounds
              -> GlobalControl.LevelSetData
              -> GlobalControl.Localization

GlobalControl.Basic
  -> GlobalControl.MainArc
     -> GlobalControl.Localization

GlobalControl.Basic
LocalEnergy dominant-forcing bounds
  -> GlobalControl.ScaleComparison
     -> GlobalControl.LevelSetAssembly

GlobalControl.LevelSetData
  -> GlobalControl.LevelSetAssembly

GlobalControl.Localization
  -> GlobalControl.LaplaceAboveFloor

GlobalControl.LevelSetAssembly
GlobalControl.Localization
GlobalControl.LaplaceAboveFloor
GlobalControl.GaussianIntegerSum
  -> GlobalControl.Partition

GlobalControl.Partition
  -> GlobalControl (public aggregate only)
```

The module contracts are:

- `BlockSystem`: prime-block data, finite support and assignments, and the
  admissible scale range, without any local-energy theorem dependency;
- `Basic`: control energy, the single-block bridge, restriction, and comparison
  of the elementary global scales;
- `LocalEnergy.AdjacentScaleEnergy`: reciprocal-phase dispersion between
  adjacent dyadic scales and the resulting fixed-outer-prime CRT energy bound,
  independent of any block system;
- `ScaleComparison`: the handoff from the global control scale to the
  first-block deviation, isolated because it uses the deeper local-energy
  forcing package;
- `MainArc`: the globally diagonal small-label set, separated from both the
  basic data and its later localization theorem;
- `CrossBlockEnergy`: specialization of adjacent-scale CRT energy to the
  mismatch penalty for consecutive blocks, with and without exception sets;
- `BlockEncoding`: hot/cold data, segment labels, and finite assignment fibers;
- `BlockEntropy`: cardinality and asymptotic absorption of encoding data;
- `ColdBlockBounds`: exception sets, cold-label estimates, energy budgets, and
  the boundary-penalty handoff;
- `GaussianIntegerSum`: the independent one-dimensional analytic estimate used
  in the final Laplace sector.

These are mathematical ownership boundaries.  Further splitting requires a
new independently meaningful contract, not merely a shorter compile time.
No internal or downstream module may import the aggregate `GlobalControl` file;
that file is an outward-facing re-export only.

## Naming policy

Current names such as `R2`, `cannon`, `gadget`, `endgame`, `ready`, `lane`,
`supply`, and `certificate` were useful while the proof was being found, but
they should not be the long-term public language.

Preferred replacements:

| Working name | Public mathematical name |
| --- | --- |
| `R2` | resonant dyadic semiprime construction |
| `SpectralCannon` / `CannonBridge` | finite spectral selection / spectral bridge |
| `gadget` | prime-reservoir damping edge(s) |
| `mass batch` | reciprocal-mass reservoir |
| `endgame` | terminal assembly |
| `lane` | frequency class or frequency estimate |
| `supply` | witness data, hypothesis package, or construction input |
| `certificate` | witness package, construction stage, or assembly record |

Rules:

- Public theorem names should describe the mathematical statement, not the route
  by which it was discovered.
- Internal records may keep transitional names during the port, but every new
  public facade should use the formal vocabulary above.
- Compatibility shims should have short comments saying which formal name
  replaces them and when they can be deleted.

## Deletion policy

Do not delete Lean files merely because their names are historical.  The current
audit import closure reaches every Lean file in `RequestProject`, so file-level
deletion must wait until a replacement public import graph exists.

Safe deletion candidates are:

1. declarations outside the audit dependency closure;
2. declarations used only by compatibility shims after downstream imports have
   been migrated;
3. comments describing old false routes, once a preserved note or issue records
   the mathematical lesson;
4. public wrappers whose replacement theorem is already imported by the audit
   entry point and whose old name has no downstream users.

Every deletion pass should be justified by:

- an import-closure check from `RequestProject.Audit`;
- an `rg` check for declaration references;
- a successful build or CI run of the public audit target.

## Refactor order

1. Finish the Lean/Mathlib v4.31 port without broad renames. (Completed through
   the global-control core.)
2. Add public facade files with formal mathematical names while keeping old
   imports as shims.
3. Move the spectral selection layer first; it is the cleanest abstraction and
   sets the style for later extractions.
4. Move the analytic boundary and core definitions.
5. Split global control into public final theorems and internal historical
   translation files.
6. Rename and move the resonant dyadic construction in small batches.
7. Remove compatibility shims and stale prose only after the audit target imports
   the new public path.

The invariant throughout is that the audit theorem has exactly the standard
Lean axioms plus the two structural analytic inputs.

## Proof-graph discipline

The mathematical development is a directed graph of motivation and
specialization, not merely a sequence of files.  A typical proof segment has
two distinguished nodes:

1. a **principle node**, stating the smallest mathematically natural mechanism;
2. a **handoff node**, applying that mechanism to the concrete objects expected
   by the next layer.

Intermediate declarations should be retained when they express a genuinely
nontrivial reusable idea, give a useful independent corollary, or make an
important mathematical transition visible.  Pure tactic scaffolding should
remain private or be eliminated.

“Smallest” here means the smallest sufficient abstraction that preserves the
mathematical motivation, not the statement with the greatest possible formal
generality.  A proposed abstraction should pass three tests:

- **explanation:** its mechanism can be stated clearly in one sentence;
- **specialization:** the project-specific handoff is a natural instantiation;
- **payoff:** it clarifies the paper or materially simplifies downstream Lean.

Generalization into category theory, abstract algebra, or another foundational
language is appropriate when it passes these tests.  Otherwise Mathlib is the
upstream boundary and the project should use the least elaborate interface that
exposes the idea.

Each mature module should document a compact node contract:

- the motivating question inherited from upstream;
- the mathematical input declarations;
- the principle theorem(s);
- the concrete handoff theorem(s);
- the downstream modules allowed to depend on that handoff.

Before introducing a new principle theorem, search the pinned Mathlib source
and use `#check`/`#find_home` for the underlying mathematical mechanism.  Prefer
standard Mathlib structures even when a hand-written project lemma is already
working.  The local CRT model, for example, uses `Nat.coprime_primes`,
`ZMod.chineseRemainder`, and `ZMod.valMinAbs`; project code should state only the
energy-specific structure built on top of those APIs.

Module boundaries follow mathematical structure, not compiler timing.  A useful
build boundary is not by itself a reason to create a file or theorem: an
extracted unit must still have a natural mathematical name, mechanism, and
handoff.  Pure bookkeeping should normally be discharged by the smallest
stable automation that expresses the intended calculation.  Expanded
normalization steps are acceptable while diagnosing a port, but should not
remain in the mature proof unless they expose a genuine mathematical point.

The paper should linearize this same graph.  Lean declaration names therefore
need to be mathematically searchable from the paper: names should describe the
statement, module docstrings should explain the node contract, and theorem
docstrings should record mathematical role rather than proof history.

## Refactoring frontier

Mathematical development continues from sources toward the final theorem.  The
engineering work should stay at the earliest non-clean confluence on that route:

- do not reopen an earlier green source without a mathematical reason;
- do not skip over a red confluence to polish a downstream bridge;
- inspect all incoming branches at the confluence, then extract only its
  mathematically coherent upstream nodes and continue downstream from their
  stable interfaces.

Thus a justified physical file extraction may look locally "upstream-facing",
but it does not reverse the proof direction.  A green prefix that is merely a
convenient compilation slice remains in its mathematical module.
