# Summary of changes for run c7636123-7fe9-4513-9bb8-960ddf0ae597
## Outcome

I must be upfront about a central fact: **Erdős Problem 306 is an open mathematical problem.** I verified this directly against the authoritative source (erdosproblems.com/306, accessed 2026-06-16), which states: *"This is open, and cannot be resolved with a finite computation."* No proof is known in the literature. (The "Lichtman 2024" reference that appeared in an earlier draft of the code is unsubstantiated; the only published progress, [BEG15], handles a different, weaker statement — products of *three* distinct primes, with b=1.)

Because the problem is open, it cannot be "finished," and I am constrained from papering over it with an `axiom`. Instead I produced the most honest, clean, publishable packet possible: everything that *is* provable is fully machine-verified, and the single open input is isolated behind one clearly-cited `sorry`.

## What is now verified (sorry-free)

- **Faithful statement** of Problem 306: `erdos_306` (`RequestProject/Erdos306.lean`).
- **Necessity** of the squarefree hypothesis on `b`: `necessity_squarefree_denom` (`RequestProject/Defs.lean`).
- **Reduction** of the general numerator case `a/b` to the unit case `1/b` (denominator-avoiding form): `reduction_to_unit_numerator_avoiding` (`RequestProject/MainTheorem.lean`).
- **Concrete instances** via the triple-prime identity: `1/2, 1/3, 1/5, 1/6, 1/7, 1/11` (`RequestProject/Erdos306.lean`), with the identity `triple_prime_sum`.

I confirmed each of these is genuinely sorry-free by tracing its axioms (only `propext, Classical.choice, Quot.sound`).

## The single isolated open input (with citation)

The lone gap is the unit case `1/b` for general squarefree `b`, which *is* the open content of Problem 306. It is isolated as one lemma, `erdos_306_unit_case_open`, recorded as an ordinary `theorem ... := by sorry` (not an `axiom`, so it stays visible to `#print axioms`), and cited to **[ErGr80]** P. Erdős and R. Graham, *Old and new problems and results in combinatorial number theory* (1980), MR 0592420; recorded as Problem 306. The related three-prime result **[BEG15]** is cited as the nearest published progress. There are **no `axiom` declarations and no `@[implemented_by]`** anywhere in the built library. I also ran an automated proof attempt on this lemma to honor the request to "try finishing"; as expected for an open problem, no proof was found.

`#print axioms erdos_306` reports `[propext, sorryAx, Classical.choice, Quot.sound]` — the `sorryAx` corresponds to, and only to, this single cited open input.

## Cleanup

- The built library now consists of exactly three clean files: `Defs.lean`, `MainTheorem.lean`, `Erdos306.lean` (entry point), importing only Mathlib and each other.
- The previous large, **incomplete** circle-method attempt (82 files, 60+ scattered `sorry`s, which after much scaffolding bottomed out at the same open problem and relied on results recorded as axioms) was moved out of the build into `notes/abandoned-circle-method-route/`, with a README explaining its non-authoritative status. It is preserved, not deleted.
- Rewrote `README.md` to state the honest open status, the verified content, the single cited gap, and the build/verify instructions.
- Removed stale object files for the deleted modules, rebuilt the clean spine, and regenerated `prebuilt-oleans.tar.gz` so the shipped `.olean` files exactly match the three live sources. The full project builds successfully.

## Honest bottom line

This repository is a faithful formalization of Erdős 306 together with its verified necessity direction, its verified reduction to the unit case, and verified concrete instances; the unit case for general squarefree `b` remains genuinely open and is isolated as a single cited `sorry`. It should **not** be cited as a complete proof of Erdős 306, because no such proof exists.


# Summary of changes for run 4a44471c-44b2-480b-914a-8a525f6c0f27
## What I did

I cleaned, analyzed, reorganized, and honestly documented the Erdős 306 packet, and isolated the proof's gaps and cited inputs. **Important honesty note:** I could *not* turn this into a complete machine-checked proof — after full dependency analysis, the work reduces to a single genuinely-open, research-level construction lemma that the prior development never grounded in a concrete object, and I am constrained from introducing new axioms to paper over it. Everything that *can* be verified is verified, and the one remaining gap is now crisply isolated and documented.

### Repository hygiene (the "paperwork")
- Removed the junk duplicate `Erdos306Unconditional.lean.lean`. (The mentioned `aristotle_delifery`/`aristotle-delivery` folder was already absent from the packet.)
- Moved all working notes, plans, logs and task files into `notes/` (79 files, preserved for reference) with a `notes/README.md` explaining they are non-authoritative/archival.
- Wrote a clean, accurate top-level `README.md` (statement, build/verify instructions, a verification-status table, the cited-axiom list, project layout, and an explicit completeness caveat).
- Laid the sources out under `RequestProject/` (matching `lakefile.toml`), and regenerated `prebuilt-oleans.tar.gz` so the shipped `.olean` files exactly match the final sources (84 modules). The `.lake` build tree is kept so you can verify after download.

### Reorganization driven by the dependency graph
- Computed the full import graph. The whole project builds (`lake build`, 8110 jobs).
- Removed 16 fully-disconnected exploratory files (the superseded SBEE/rational-collision "anchored lattice / cluster" route) that nothing on the live spine or the construction-reduction path imports.
- Decoupled the obsolete SBEE-conditional route from the unconditional spine (`MainTheorem.lean` no longer depends on `SBEE`; it now contains only the reusable, fully-verified numerator reduction `a/b ⇝ 1/b`).
- Rewrote `RequestProject/Erdos306Unconditional.lean` into a pristine entry point: faithful statement of `erdos_306`, the proof architecture, a precise verification-status section, the cited classical inputs, and a trailing `#print axioms erdos_306` so verifiers see the dependency trace immediately.

### Isolation of the goal, the gap, and the "quoted" lemmas (with citations)
- **Final goal** `erdos_306` is isolated and cited (erdosproblems.com/306), with the squarefree-necessity direction proved (`necessity_squarefree_denom`).
- **The single reachable gap** is `CircleMethod.exists_arcConstruction` (the block-aligned circle-method construction). I confirmed by kernel axiom-tracing that the surrounding analytic core `exists_pos_weighted_of_construction` (construction ⇒ positivity ⇒ representation) is **sorry-free**, so this lemma is the unique source of `sorryAx` reachable from `erdos_306` (every case, including b=1,2, routes through it). It carries a clear "REMAINING GAP" docstring. I kept it as a documented `sorry` rather than an axiom, since adding axioms is disallowed in this packet.
- **The "directly quoted" lemmas** are the three pre-existing classical inputs feeding the construction's reduction — Rosser–Schoenfeld (1962) and Mertens, in `dyadic_prime_density`, `dyadic_mertens_cumulative`, `dyadic_control_recipLoad_eventually_small`. They already carried citations; I documented and centrally listed them (in the entry header and `README.md`) so a verifier recognizes them as cited results, not failures.

### Verified (sorry-free), confirmed by axiom-tracing
- The reduction `a/b ⇝ 1/b`; the circle-method analytic core; the b=1/b=2 reductions; the concrete instances (1/b for b = 2,3,5,7,11) and the triple-prime identity.

### What remains open
- `exists_arcConstruction` (1 reachable gap) plus 12 named `sorry`s in the unfinished Phase-G / SBEE minor-arc analysis (`GlobalControl`, `BlockCRTEnergy`, `GlobalControlG5Assembly`, `SBEE`) that are not reachable from `erdos_306` but are the analytic content a full construction would need. These are documented as the genuine remaining mathematical work. Consequently `#print axioms erdos_306` reports `[propext, sorryAx, Classical.choice, Quot.sound]`, and the repository should be cited as a formalization of the squarefree case **modulo the explicit block-aligned construction lemma**, not as a complete proof.
