# Lean environment notes

This project is a Lake/Mathlib project.  The authoritative project pins are:

- `lean/lean-toolchain` — Lean toolchain used by `elan` and Lake;
- `lean/lakefile.toml` — Mathlib dependency revision;
- `lean/lake-manifest.json` — resolved transitive dependency graph.

## Local setup

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
. "$HOME/.elan/env"
cd lean
lake exe cache get
lake build RequestProject.Erdos306FormalConjectures
lake env lean RequestProject/Audit.lean
```

The checked-in project currently pins Lean/Mathlib `v4.31.0`.  The dependency
lockfile has been refreshed on this release line; the proof port and full CI
verification are tracked as the Stage B migration in
[`docs/refactor-roadmap.md`](refactor-roadmap.md).

## Latest-release upgrade status

As of 2026-06-26, GitHub lists Lean `v4.31.0` and Mathlib `v4.31.0` as the latest
stable release tags.  The project pins have been mechanically bumped:

```text
lean/lean-toolchain: leanprover/lean4:v4.31.0
lean/lakefile.toml:  mathlib rev = "v4.31.0"
```

`lake update` refreshed `lean/lake-manifest.json` and installed the local Lean
`v4.31.0` toolchain.  The Mathlib cache download was interrupted by local disk
space exhaustion (`No space left on device`), so the next engineering step is to
finish the cache/build verification in CI or after freeing local space.

Earlier mechanical port testing found proof-script blockers in
`RequestProject/GlobalPeierlsBookkeeping.lean`, then
`RequestProject/BernoulliFourier.lean` and the former `SBEEDispersion.lean`.
Those blockers are closed; reciprocal dispersion now lives at
`RequestProject/LocalEnergy/ReciprocalDispersion.lean`.


## Refactor sequencing

See [`docs/refactor-roadmap.md`](refactor-roadmap.md) for the recommended branch
stack for the v4.31 port, warning cleanup, module reorganization, and deletion
pass.  The important invariant for every stage is that `RequestProject.Audit`
continues to report exactly the three standard Lean axioms plus the two analytic
axioms.
