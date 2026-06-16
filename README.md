# Erdős Problem 306 — A Semiprime Egyptian-Fraction Program

**Author:** Yuren Tang
**Status:** preliminary research release (`v0.0.1-prerelease`) — work in progress, *not* a completed proof.

---

## The problem

**Erdős Problem 306** (a form of the Butler–Erdős–Graham question on unit fractions
with restricted denominators):

> Every positive rational $a/b$ with squarefree denominator $b$ is a finite sum of
> reciprocals of **distinct squarefree semiprimes** (products of two distinct primes):
> $$\frac{a}{b} = \sum_{i} \frac{1}{n_i}, \qquad n_i = p_i q_i \ \text{distinct squarefree semiprimes}.$$

The difficulty grows as the number of prime factors $\omega$ of the allowed
denominators *decreases*; the semiprime case $\omega = 2$ is the hard one.

## What this repository is — and is not

This is a **research log and an in-progress Lean 4 formalisation** of an *independent*
attack on the problem via a route that is, to our knowledge, methodologically distinct
from the existing literature:

- a **circle-method / weighted-positivity** reduction (`fourier_positivity`), and
- a **deterministic-dispersion** treatment of the single-block counting condition
  ("SBEE") that, at the block level, replaces Kloosterman/Irving input with an
  elementary dispersion lemma.

**It is not a finished proof.** The current Lean development contains **76 `sorry`
placeholders across 30 files** and **3 explicitly declared classical axioms**
(dyadic prime density / a cumulative Mertens bound). Several self-contained
components *are* machine-verified sorry-free (e.g. the SBEE dispersion and
"fingerprint" counting core, the abstract Peierls bookkeeping layer, and concrete
small-denominator instances), but the headline statement is **not yet machine-checked**.
The honest remaining targets are the R2 arc construction (`exists_arcConstruction`),
the G5/G7 global-control endgame, and Phase C of the circle method. See
[`proof-notes/00 README.md`](proof-notes/00%20README.md) and
[`proof-notes/04 Failure and Risk Ledger.md`](proof-notes/04%20Failure%20and%20Risk%20Ledger.md)
for the candid status, and [`proof-notes/20 Lean Core Audit and Dependency Map.md`](proof-notes/20%20Lean%20Core%20Audit%20and%20Dependency%20Map.md)
for the real-vs-assumed map of the Lean code.

## Relation to concurrent work

While this release was being prepared, **Shisheng Li**, *"Every natural number is a
sum of distinct semiprime unit fractions"* (arXiv:2606.15159, 13 June 2026), gave a
**complete** proof of the integer $\omega = 2$ case and of the rational case above an
explicit threshold, by a **different** method (Olson's addition theorem and Chebyshev
bounds), with accompanying Lean 4 and Python material.

This repository documents an **independent line of work**, developed 7–16 June 2026
(see [`TIMELINE.md`](TIMELINE.md)), pursuing a different proof strategy. It is released
as a dated, citable record of that approach; it makes **no claim of priority over**
Li's result. Where the two overlap, Li's paper is the complete reference for the theorem.

## Repository layout

```
proof-notes/   Numbered research notes (00–57). Start at "00 README.md".
               The mathematical core is in notes 29–35 (SBEE / circle method),
               34 (block-to-global), 38/40 (G5/G7), 46/50 (R2 construction).
lean/          Lean 4 formalisation (Lean v4.28.0 + Mathlib v4.28.0).
               lean/RequestProject/*.lean — sources. Build: `lake build RequestProject`.
TIMELINE.md    Development chronology (digest of the private working repository).
```

The Lean development is large and slow to build; it depends on a pinned Mathlib
(`lake-manifest.json`). Build artifacts and third-party reference papers are
intentionally excluded from this snapshot.

## Citing

If you reference this work, please cite it as a dated software/preprint record
(see [`CITATION.cff`](CITATION.cff)); a DOI will be attached to this release via Zenodo.

## License

- Prose and mathematical notes: **CC BY 4.0**.
- Lean source code: **Apache-2.0** (matching the Mathlib ecosystem).

See [`LICENSE`](LICENSE).
