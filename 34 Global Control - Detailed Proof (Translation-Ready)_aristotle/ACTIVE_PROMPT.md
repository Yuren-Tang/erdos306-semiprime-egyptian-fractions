# ACTIVE TASK: complete the hrhs ε-budget assembly (note 42)

The G5 cover layer, admissibility, route-closure, and the hard mechanical
bridges of the ε-budget assembly are PROVED and locally verified. Your task is
the remaining `hrhs` sub-lemmas, specified in **note `42 hrhs Completion Spec
for Aristotle.md`** (read it fully). Work ONLY in
`RequestProject/GlobalControlG5Assembly.lean` (imports the cached
`GlobalControlG5Data`); do NOT modify the frozen cover layer, and do NOT touch
`CircleMethod.lean` (Phase C is being driven separately).

Order: N1 (per-label charges) → N2 (label-size) → N3 (per-fiber discharge) →
N4 (label_product_le) → N5 (assembly → close `GlobalControl.global_levelset`).
Then, if time remains, G7 (`global_control_partition`, note 38 §7).

Rules: build on the already-proved lemmas listed in note 42 (do not redo them).
Keep every hypothesis faithful. Verify each lemma compiles
(`lake build RequestProject.GlobalControlG5Assembly`). Where a numeric chase
resists, isolate it as a precisely-named `sorry` with a one-line reason and
continue. Report which lemmas closed.

Startup: extract `prebuilt-oleans.tar.gz` into `.lake/build/lib/lean/` after
`lake exe cache get` to skip the ~20-min rebuild of the verified core.
