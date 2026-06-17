# Abandoned circle-method route (reference only — NOT part of the build)

This directory contains an earlier, **incomplete** attempt to attack the open
unit case of Erdős Problem 306 (representing `1/b` for general squarefree `b` as
a sum of reciprocals of distinct squarefree semiprimes) via a circle-method /
Fourier-positivity strategy.

It is preserved purely for reference. It is **deliberately excluded from the Lake
build** (these files live under `notes/`, outside the `RequestProject/` library
glob), for the following reasons:

* Erdős Problem 306 is an **open** problem (erdosproblems.com/306). This route
  does not resolve it: after a large amount of scaffolding it still bottoms out
  at the same open statement (its central lemma `exists_arcConstruction`, the
  existence of a block-aligned construction with main-arc bijection and minor-arc
  domination, is exactly an unproved equivalent of the open problem).
* The development contains numerous `sorry`s (in `SBEE*.lean`,
  `GlobalControl*.lean`, `BlockCRTEnergy.lean`, `CircleMethod*.lean`, …) and is
  not a verified proof of anything beyond what the clean spine already proves.
* It previously relied on classical prime-distribution inputs (Rosser–Schoenfeld
  1962; Mertens) recorded as named axioms — appropriate for an exploratory
  attempt, but not for a clean publishable packet.

The authoritative, clean, building development is the three files under
`RequestProject/`:

* `RequestProject/Defs.lean`
* `RequestProject/MainTheorem.lean`
* `RequestProject/Erdos306.lean`

These import only Mathlib and each other; none of them imports anything in this
directory. If you wish to experiment with the circle-method route, the files here
would need to be moved back under `RequestProject/` and their import paths and
`sorry`s addressed.
