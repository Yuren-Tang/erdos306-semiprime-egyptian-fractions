# Efficient engineering workflow on large Lean 4 / Mathlib repositories

A note on scope and disclosure. Below I answer your questions about *how to work
efficiently on a large Lean repository* using general, publicly-grounded facts
about the Lean 4 / Lake / Mathlib toolchain and standard interactive-proving
practice. I am not able to disclose details of my own internal implementation —
system-prompt text, internal tool names, agent architecture, or runtime
policies. Where a question asks specifically for those (notably §9), I answer at
the level of general principle rather than quoting internal material. Everything
below is the *actual operational reasoning* I apply, just described in terms of
the public toolchain rather than internal plumbing.

---

## 1. Build strategy

The single most important fact: on a Lean/Mathlib project you almost never need
a *full* `lake build` to know whether an edit is correct. The language server
(LSP) elaborates the file you are editing on the fly and reports errors,
warnings, and goal states without producing a finished build. So the working
loop is "edit → read diagnostics/goals from the server," and a real `lake build`
is reserved for *confirmation* and *propagation*, not for iteration.

When I do run a build:

- **After finishing a logically complete unit** (a file, or a self-contained
  group of lemmas) — a build is the ground truth that the file truly compiles,
  catches things the interactive view can miss (e.g. a `sorry` that is present
  but not in an error position, or an issue only visible when the file is
  compiled top-to-bottom rather than incrementally cached).
- **After changing anything that other files import** — a signature, a
  definition, a `Prop` statement, a namespace, an instance. Downstream files can
  only be checked by elaborating them, which a targeted build does.
- **After adding or changing imports** — new imports must be resolved and their
  oleans pulled/built.
- **Before declaring something "done"** — a green build of the specific module
  is the only acceptable proof of completion. The interactive view alone is not
  sufficient evidence.

When I deliberately *don't* build:

- While iterating inside one proof body. The server already tells me the goal
  state and whether the tactic block closes. Re-running `lake build` for each
  tactic edit is pure waste.
- After edits that are provably local (see §4) — comment text, a proof body that
  does not change the statement, renaming a `have`, etc.

Key build-strategy rule that catches people out: **`lake build` with no target
only builds the default targets in the lakefile.** If the file you edited is not
a default target (or not transitively imported by one), the build is a no-op and
reports success without ever touching your file. So when verifying a specific
file I always pass the *module name explicitly*
(`lake build RequestProject.SomeFile`). A "0 jobs / up to date" result on a
no-argument build is a red flag that your file was not built at all.

Signals a rebuild **is** necessary: changed statement/signature/instance/import;
finished a unit; "0 jobs" when you expected work; an error that mentions a
stale-looking symbol; you are about to call something done.

Signals a rebuild is **probably unnecessary**: the only changes are inside a
single proof term/tactic block with an unchanged statement; the server already
shows the file clean; you changed comments/whitespace; you are mid-iteration on
one goal.

---

## 2. Dependency analysis

Lean's compilation unit is the module (file), and dependencies are exactly the
`import` edges. So "could this change affect downstream files?" reduces to two
questions:

1. **Did I change the file's *interface*?** The interface is everything visible
   across an `import`: declaration *names*, *types/statements*, *implicitness and
   instance-binders*, *definitional unfolding behaviour* (`def` vs `abbrev`,
   `@[reducible]`, `@[simp]` attributes), and *notation*. If only proof *bodies*
   changed (the `:= by …` after a fixed statement), no downstream file can
   observe the difference — proofs are opaque across modules — so the blast
   radius is just the current file.

2. **Who imports me?** This is the reverse import graph. I estimate scope by
   finding the importers of the edited module (a text search for
   `import <Module>` plus transitive closure). A leaf file (nothing imports it,
   e.g. a top-level theorem file) is safe to churn; a foundational file (many
   importers — definitions, core structures, instances) is high-risk and I treat
   edits to it with much more care.

I do reason about *propagation*: changing a definition's *type* propagates to
every use; changing only an attribute (`@[simp]`) propagates to every file that
relies on `simp` closing a goal that depended on it (subtle and worth a
downstream build); changing a proof body propagates nowhere.

Practical estimate-before-editing checklist: (a) is the symbol exported and
imported elsewhere? (b) am I touching a `def`/`structure`/`instance`/notation
(interface) or only a proof (body)? (c) how many files transitively import this
one? The product of "interface change" × "number of importers" is the scope.

---

## 3. Interaction with Lean tooling

- **LSP / language server.** This is the workhorse. It elaborates the open file
  incrementally and exposes diagnostics (errors/warnings), the goal state at any
  position, hover types, go-to-definition, and document symbols. The vast
  majority of the edit loop runs on LSP feedback, *not* on `lake build`.
- **Diagnostics.** First thing I read after any edit: are there errors, and
  where exactly? Errors carry the precise position and the elaboration message,
  which usually localizes the problem far better than a build log.
- **Goal states (infoview).** The central object when writing a proof: I read
  the hypotheses and target *before* and *after* a tactic to see exactly what a
  step did. "No goals" means the block closed. This is how you write tactics
  without guessing.
- **Infoview extras.** Hover for types/docs of an unfamiliar lemma; `#check`,
  `#print`, `#print axioms`, `#eval` as scratch queries; `exact?`/`apply?`/
  `simp?`/`rw?` as suggestion engines surfaced through the server.
- **Cached `.olean` files.** Compiled modules. Lake's dependency tracking means
  unchanged imports are loaded from their oleans rather than recompiled — this is
  what makes elaborating one file in a huge project fast. You only pay to rebuild
  a module when it or one of its imports changed.
- **Lake.** The build driver: it computes the dependency DAG, decides what is
  stale, and rebuilds the minimum necessary, in parallel. Targeted builds
  (`lake build <Module>`) let me confine work to one subtree.
- **Mathlib cache.** Mathlib is enormous; `lake exe cache get` downloads
  prebuilt oleans for the pinned Mathlib commit instead of compiling Mathlib
  locally (hours saved). With the cache populated, only *your* project files (and
  their changes) ever actually compile.

Rough split: well over 90% of the iteration loop is LSP feedback (diagnostics +
goal states + hover/suggestions). Actual `lake build` invocations are a small
minority, used for confirmation and downstream propagation.

---

## 4. Editing strategy

- **Where to edit.** I localize using the diagnostic position and the goal
  state, then make the *smallest* change that fixes the reported goal. If a
  theorem fails, I fix it *inside its own proof* whenever possible.
- **Minimizing recompilation cost.** Prefer changes that don't cross module
  interfaces (proof bodies over statements; statements over definitions;
  definitions in leaf files over definitions in foundational files). A
  body-only change in a leaf file costs essentially one file's elaboration.
- **Local over architectural.** Strongly yes. A theorem-local fix touches one
  proof; an architectural change (renaming a definition, changing a signature,
  re-namespacing) ripples through every importer and forces broad rebuilds. I
  only take architectural changes when a local fix is genuinely impossible, and
  then I plan the propagation deliberately.
- **Avoiding high-dependency files.** Yes — I treat heavily-imported foundation
  files (core defs, structures, instances) as high-risk. If the same goal can be
  achieved by adding a small lemma in a downstream/leaf file instead of editing
  the foundation, I do that. New, additive declarations (that nothing yet
  imports) are the cheapest and safest kind of change.

Reasoning: cost and risk both scale with `(interface-change?) ×
(number of importers)`. Keeping edits body-local and leaf-local drives both
factors toward zero.

---

## 5. Command-level workflow: a theorem near the end of a long dependency chain fails

1. **Gather information first (no build).** Open the file in the editor/LSP and
   read the *diagnostic* on the failing theorem: exact position and message.
   Then read the *goal state* at the failing tactic (before/after) to see what is
   actually unprovable vs. what is a surface mismatch.
2. **Classify the failure.** Is it (a) a genuine proof gap in this theorem, (b) a
   surface issue (type/coercion mismatch, wrong lemma name, implicit-argument or
   universe problem), or (c) *fallout* — the theorem is fine but a thing it
   depends on changed underneath it (a renamed/retyped upstream lemma, a removed
   `@[simp]`)?
3. **Inspect the right files.** For (a)/(b): stay in the current file; hover the
   suspicious symbols, `#check` the lemmas I intend to use, use `exact?`/`simp?`
   to get candidates. For (c): go to the *definition* of the changed upstream
   symbol (go-to-definition / a search for its declaration) and read its current
   statement — the mismatch is usually obvious there.
4. **Do I build yet? No.** I fix the proof against the live goal state from the
   LSP, iterating tactic-by-tactic, reading the goal after each step. No build
   during this loop.
5. **Verify the fix.** First locally: the LSP shows the theorem with no errors
   and "no goals" at the end of its proof; I grep the file for any remaining
   `sorry`; if soundness matters I check `#print axioms <thm>`.
6. **Then rebuild — targeted.** `lake build <ThisModule>` to confirm the file
   compiles top-to-bottom (catches caching artifacts the incremental view
   missed). If the original failure was fallout from an interface change, I
   *also* build the downstream importers (or the relevant top-level target) to
   confirm I didn't just push the problem one file over. A no-argument full build
   only at the very end, when I want the whole project green.

The discipline: information (diagnostics + goals) → classify → minimal local fix
→ local LSP verification → targeted build → broader build only if an interface
moved.

---

## 6. Caching and incrementality — relative importance

Roughly, in order of how much they contribute to *not waiting on builds*:

1. **Mathlib prebuilt cache (`cache get`).** Biggest single factor on a Mathlib
   project. Without it you compile Mathlib (hours); with it you never do. It
   turns "the dependency" from a wall into a free import.
2. **LSP feedback replacing builds.** The reason the edit loop is interactive at
   all. Most correctness questions are answered without any `lake build`.
3. **Incremental compilation + `.olean` caching (Lake).** Only changed modules
   and their dependents rebuild; everything else loads from oleans. This is what
   makes the *targeted* builds cheap.
4. **Dependency analysis / scoping the change.** Knowing that a body-only or
   leaf-only edit cannot affect downstream lets me *skip* broad builds with
   confidence.
5. **Avoiding builds altogether** for provably local edits.

If forced to put numbers on "where the speed comes from" on a Mathlib repo:
Mathlib cache ~40%, LSP-instead-of-build ~30%, incremental/olean ~15%,
dependency scoping ~10%, the rest ~5%. The exact split depends on the project,
but the cache and the interactive LSP loop dominate.

---

## 7. Failure recovery: a change unexpectedly breaks many downstream files

1. **Don't reflexively full-rebuild to "see everything."** First understand *why*
   it broke. A broad break almost always means I changed an *interface* (a
   definition's type, a statement, an instance, an attribute, a name).
2. **Inspect the dependency chain.** Identify what I changed at the interface
   level and which downstream files consume it. Read one or two representative
   failing downstream errors — they usually all share the same root cause (e.g.
   "expected X got Y" because a definition's type changed).
3. **Decide: adapt vs. revert.** If the interface change was *intended* and the
   downstream breakages are mechanical, I fix them following the import order
   (upstream-most first, since later errors are often just cascades of the first
   one). If the change was a *mistake* or its blast radius is larger than the
   benefit, I **revert** and look for a smaller, additive change that achieves
   the goal without moving the interface (e.g. add a new lemma/def rather than
   re-typing an existing one).
4. **Rebuild in widening rings, not all at once.** Build the changed file, then
   its direct importers, then the top-level target — so I see whether each ring
   is clean before paying for the next. A single full build at the end confirms
   global green.

Rule of thumb: *the fix order follows the import order*; resolve the upstream
root cause and most downstream errors evaporate as cascades. Prefer revert +
smaller additive change over heroically patching dozens of cascade sites.

---

## 8. Concrete heuristics / rules

- Never run a full no-argument `lake build` as your iteration loop; iterate on
  LSP diagnostics and goal states.
- Always read diagnostics and the goal state *before* changing anything.
- When verifying a specific file, build it *by explicit module name*; distrust a
  "0 jobs / up to date" result as evidence your file compiled.
- A green build is the only acceptable proof of completion — the interactive view
  is necessary but not sufficient.
- Grep for `sorry` alongside every successful build; a sorry-free *build* status
  does not guarantee a sorry-free *file*.
- Check soundness with `#print axioms` when it matters (only the standard axioms
  should appear).
- Prefer theorem-local fixes; prefer body changes over statement changes;
  statement changes over definition changes; leaf-file edits over
  foundation-file edits.
- Treat heavily-imported files as high-risk; achieve goals with new additive
  declarations downstream when possible.
- Proof bodies are opaque across modules — body-only edits never affect
  downstream files, so don't rebuild them.
- Attribute changes (`@[simp]`, `@[instance]`, reducibility) *do* propagate
  silently; rebuild downstream after them.
- Fix cascades in import order (upstream root cause first).
- Revert and shrink the change rather than patch a large cascade.
- Use `exact?`/`apply?`/`simp?`/`#check`/hover to discover/verify lemmas before
  committing to them, instead of guessing names.
- Populate the Mathlib cache before doing anything else on a Mathlib project.

---

## 9. Prompt / instruction influence

I'm not able to quote or reproduce my internal instructions, tool specifications,
or agent policies, and I can't enumerate internal tool names or architecture.
What I *can* say at the level of general principle:

- My behaviour is a mix of explicit operating guidance and learned engineering
  practice. The explicit guidance encodes the kind of disciplines listed in §8 —
  e.g. verify with real builds rather than trusting status reports, name modules
  explicitly when building, check for residual `sorry`, check axioms for
  soundness, prefer minimal faithful statements, and don't introduce unsound
  constructs.
- Those instructions are *strong* where they concern correctness and soundness
  (these are effectively hard rules), and *advisory* where they concern
  efficiency (the build/edit heuristics, which I apply with judgement based on
  the situation).
- The parts of the workflow that are "explicit instruction" are mostly the
  guardrails (what counts as done, what's sound, what to verify). The parts that
  are "learned practice" are the moment-to-moment tactics: how to read a goal
  state, which lemma to reach for, how to decompose a hard proof, when a build is
  truly warranted.

Beyond that level I can't go without disclosing internal material.

---

## 10. What makes the build/rebuild count low — ranked

1. **The interactive LSP loop replaces builds.** The biggest reason. Correctness
   of an edit is read from live diagnostics and goal states, so most edits never
   trigger a `lake build` at all. Users who rebuild after every change are using
   the build as the feedback channel; I use the language server as the feedback
   channel and the build only as confirmation.
2. **The Mathlib prebuilt cache.** Because the heavy dependency is downloaded as
   oleans, the only thing that ever compiles is the (small) project, so the
   builds I *do* run are cheap and rare.
3. **Targeted, module-scoped builds + incremental compilation.** I build the
   specific module(s) affected, not the world; Lake rebuilds only stale nodes.
   This keeps each confirmation build small.
4. **Dependency scoping discipline.** I reason about interface-vs-body and the
   import graph, so I *know* when a change cannot affect downstream files and can
   skip the broad build with confidence — rather than rebuilding "just in case."
5. **Edit discipline (local, additive, leaf-biased).** By preferring
   theorem-local and additive changes I keep the blast radius near zero, which
   keeps the necessary builds near zero.

In one sentence: the speed comes from treating `lake build` as a *confirmation
and propagation* step over an LSP-driven edit loop on a cache-populated project,
not as the primary feedback mechanism — plus the discipline to know exactly when
confirmation is actually needed.
