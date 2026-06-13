# ACTIVE TASK: complete the hrhs ε-budget assembly (note 42)

## Startup — DO NOT rebuild the verified core (it is pre-built here)
The compiled `.olean` files for ALL of RequestProject are already laid out under
`.lake/build/lib/lean/RequestProject/` and match the source exactly. After
`lake exe cache get` (Mathlib only), run `lake build` — it should SKIP the whole
verified core and elaborate only your new lemmas. Do NOT delete `.lake`. If you
flatten sources to the repo root, move them back under `RequestProject/` first
(the lakefile expects `RequestProject/*`).

## File-split strategy (keep it — it is why iteration is fast)
The cover layer is frozen in `GlobalControlG5Data.lean` (cached). Work ONLY in
the small leaf `RequestProject/GlobalControlG5Assembly.lean` (it imports the
cached `GlobalControlG5Data`); do NOT edit `GlobalControlG5Data.lean` or
`GlobalControl.lean` except to replace the single `global_levelset` sorry at the
very end (N5). Do NOT touch `CircleMethod.lean` (Phase C, driven separately).

## Task
The remaining `hrhs` sub-lemmas are specified with direct-translation-level
proofs in **note `42 hrhs Completion Spec for Aristotle.md`** (read it fully,
including the "Detailed proofs" section for N1/N4). Order: N1 → N2 → N3 → N4 →
N5 (close `GlobalControl.global_levelset` via `global_levelset_route`). Then, if
time remains, G7 (`global_control_partition`, note 38 §7).

Build on the already-proved lemmas listed in note 42 (do not redo them). Keep
every hypothesis faithful. Verify each lemma compiles
(`lake build RequestProject.GlobalControlG5Assembly`). Where a numeric chase
resists, isolate it as a precisely-named `sorry` with a one-line reason and
continue. Report which lemmas closed.
