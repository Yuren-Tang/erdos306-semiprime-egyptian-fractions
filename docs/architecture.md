# Architecture and naming plan

This document fixes the intended mathematical architecture before the module
tree is reorganized.  It is deliberately conservative: public names should be
mathematical, while historical working names may remain temporarily as internal
compatibility shims until the v4.31 port and CI audit are green.

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
Core.Semiprime
  -> Core.EgyptianRepresentation
     -> Core.UnitNumeratorReduction
     -> Core.SquarefreeNecessity  (independent paper-side corollary)
```

The former `Defs` aggregate and conditional `MainTheorem -> SBEE` chain have
been removed from the active project graph.

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

GlobalControl.NearestInteger
  -> GlobalControl.CrossBlockEnergy
  -> CircleMethodArcs

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
- `NearestInteger`: the reusable distance-to-the-nearest-integer primitive used
  by both cross-block dispersion and the circle method;
- `ScaleComparison`: the handoff from the global control scale to the
  first-block deviation, isolated because it uses the deeper local-energy
  forcing package;
- `MainArc`: the globally diagonal small-label set, separated from both the
  basic data and its later localization theorem;
- `CrossBlockEnergy`: reciprocal-phase dispersion and the energy penalty caused
  by different labels on consecutive blocks;
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
