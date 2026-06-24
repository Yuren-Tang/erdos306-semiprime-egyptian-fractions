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

The checked-in project currently pins Lean/Mathlib `v4.28.0`, matching the build
that verifies the headline theorem in this workspace.

## Latest-release upgrade note

As of 2026-06-24, GitHub lists Lean `v4.31.0` and Mathlib `v4.31.0` as the latest
stable release tags.  I tested the mechanical bump:

```text
lean/lean-toolchain: leanprover/lean4:v4.31.0
lean/lakefile.toml:  mathlib rev = "v4.31.0"
```

`lake update mathlib` completed, but the proof does not build unchanged on
`v4.31.0`.  The first blocker was `RequestProject/GlobalPeierlsBookkeeping.lean`
around the geometric-sum normalization step; after repairing that locally, the
next blockers appeared in `RequestProject/BernoulliFourier.lean` and then
`RequestProject/SBEEDispersion.lean`, where older fragile `convert`/`grind` proof
scripts no longer elaborate cleanly.  Therefore this branch keeps the proven
`v4.28.0` pins and records the `v4.31.0` upgrade as a dedicated porting stage
rather than mixing a toolchain migration into the analytic-axiom refactor.


## Refactor sequencing

See [`docs/refactor-roadmap.md`](refactor-roadmap.md) for the recommended branch
stack for the v4.31 port, warning cleanup, module reorganization, and deletion
pass.  The important invariant for every stage is that `RequestProject.Audit`
continues to report exactly the three standard Lean axioms plus the two analytic
axioms.
