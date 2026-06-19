This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Erdős 306 Aristotle Delivery

This folder is the upload/build root.  Do not move the Lean files out of
`RequestProject/`; the Lake package is already arranged in the expected shape.

## Quick Start

1. Work from this folder as the project root.
2. Keep `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and
   `RequestProject/` together.
3. First try to fetch Mathlib's binary cache:

```sh
lake exe cache get
```

4. A project cache is already expanded at
   `.lake/build/lib/lean/RequestProject/`.  If it is missing after upload,
   restore it from `prebuilt-oleans.tar.gz` before rebuilding:

```sh
mkdir -p .lake/build/lib/lean
tar xzf prebuilt-oleans.tar.gz -C .lake/build/lib/lean/
lake build
```

The included cache/archive contains the compiled `RequestProject` oleans for
this source state.  It does not vendor the whole Mathlib cache; use
`lake exe cache get` for Mathlib.  If Lake considers any file stale, it will
rebuild that file normally.

## Active Task

Read `TASK.md` first, then `ACTIVE_PROMPT.md`.  The current active mathematical
instruction is note `52 R2 Assembly Skeleton Next Task.md`, with notes 50 and 51
as the surrounding proof map.  The former note-47, note-49, and R2-mass tasks
have already been completed locally and are included here only as context.  The
latest machine-generated status is recorded in `ARISTOTLE_SUMMARY.md`.
