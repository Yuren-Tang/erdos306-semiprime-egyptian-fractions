# A formally verified proof of Erdős Problem 306 in Lean 4

[![verify-erdos-306](https://github.com/Yuren-Tang/erdos-306/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Yuren-Tang/erdos-306/actions/workflows/ci.yml)

Yuren Tang — [ORCID 0009-0006-0847-3330](https://orcid.org/0009-0006-0847-3330)

This repository contains a **complete, machine-checked proof of Erdős Problem
306**, formalized in Lean 4 with Mathlib. The proof is `sorry`-free; it is
complete modulo **two named structural analytic-number-theory inputs**: a
PNT-type dyadic prime-density input and a Mertens-type reciprocal-prime window
input.

## The statement

Erdős Problem 306 ([erdosproblems.com/306](https://www.erdosproblems.com/306)):

> Let $a/b \in \mathbb{Q}_{>0}$ with $b$ squarefree. Are there integers
> $1 < n_1 < \cdots < n_k$, each the product of two distinct primes, such that
> $$\frac{a}{b} = \frac{1}{n_1} + \cdots + \frac{1}{n_k}\,?$$

This repository proves the answer is **yes**, as the theorem `erdos_306` (in
[`lean/RequestProject/Erdos306FormalConjectures.lean`](lean/RequestProject/Erdos306FormalConjectures.lean)),
whose formal statement is taken verbatim from the Formal Conjectures project
(cited below), where it is left open with `sorry`:

```lean
theorem erdos_306 :
    ∀ (q : ℚ), 0 < q → Squarefree q.den →
      ∃ k : ℕ, ∃ (n : Fin (k + 1) → ℕ), n 0 = 1 ∧ StrictMono n ∧
        (∀ i ∈ Finset.Icc 1 (Fin.last k), ω (n i) = 2 ∧ Ω (n i) = 2) ∧
        q = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i)
```

Reading the Lean against the problem: `q` is the rational $a/b$ (with `q.den` its
reduced denominator); `ω`, `Ω` are Mathlib's counts of distinct and total prime
factors, so `ω (n i) = Ω (n i) = 2` says each denominator is a product of two
distinct primes; `n 0 = 1` is a dummy initial entry and `StrictMono n` makes the
denominators distinct and increasing. Comparing the two boxes is all it takes to
confirm the formalization expresses the problem.

## What the machine guarantees — and the one thing you check by hand

The Lean kernel guarantees the proof: `erdos_306` compiles with no `sorry`, and
`#print axioms erdos_306` shows it rests on **only** Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) plus two named analytic inputs —
nothing else. CI re-checks this from a clean build on every push and prints the
full statements in its run summary.

The formal audit boundary is now structural rather than tied to one set of
explicit numerical Rosser--Schoenfeld estimates.  The two non-standard axioms are
stated in [`lean/RequestProject/AnalyticInputs.lean`](lean/RequestProject/AnalyticInputs.lean):

- **`GlobalControl.pnt_dyadic_prime_density`** — a PNT-type dyadic prime-density
  axiom, exported downstream through `GlobalControl.dyadic_prime_density`:

  ```lean
  axiom pnt_dyadic_prime_density (k : ℕ) (hk : 5 ≤ k) :
      (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ ((dyadicBlock k).card : ℝ)
  ```

  Conceptually, this is a coarse eventual dyadic consequence of the prime number
  theorem `π(x) ~ x / log x`, namely that `[2^k, 2^(k+1))` contains enough primes
  for all sufficiently large construction scales.

- **`GlobalControl.mertens_dyadic_window_mass`** — a Mertens-type reciprocal-prime
  window axiom, exported downstream through `GlobalControl.dyadic_mertens_cumulative`:

  ```lean
  axiom mertens_dyadic_window_mass :
      ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
        (21 : ℝ) / 20 ≤
          ∑ p ∈ (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock, (1 : ℝ) / (p : ℝ)
  ```

  Conceptually, this follows from Mertens' reciprocal-prime theorem
  `∑_{p≤x} 1/p = log log x + B + o(1)`: for every fixed `A > 1`, the window
  `∑_{X≤p<X^A} 1/p` tends to `log A`; the construction uses the case whose mass
  is bounded below by `21/20`.

Recommended references for the conceptual analytic inputs are Montgomery--Vaughan
or Apostol for the prime number theorem, and Mertens/Landau/Tenenbaum for the
reciprocal-prime theorem.  Rosser--Schoenfeld's explicit estimates remain a
possible way to instantiate these structural inputs, but are no longer the Lean
axiom names or the hard-wired dependency chain.

So the entire trust boundary — the problem statement, the Lean theorem, and the
two structural analytic inputs — is visible on this page. Each CI run re-prints
the same audit, so it can also be checked from a run without opening any file.

## Scope of this release (v0.0.3)

The headline theorem and its two boundary axioms are final and audited. The
internal development is fully machine-checked — that is what makes the theorem
valid — but its comments, naming, and file organization are still being cleaned
up and should be read as provisional; in-code prose carries no logical weight. A
written mathematical account is in preparation.

## Build and verify it yourself

```bash
cd lean
lake exe cache get                                   # prebuilt Mathlib oleans
lake build RequestProject.Erdos306FormalConjectures  # builds and checks the proof
lake env lean RequestProject/Audit.lean              # prints the theorem, axioms, and audit
```

Toolchain `leanprover/lean4:v4.31.0`, Mathlib `v4.31.0`.  See
[`docs/environment.md`](docs/environment.md) for local setup notes and the
current upgrade status, and
[`docs/refactor-roadmap.md`](docs/refactor-roadmap.md) for the staged cleanup plan.
The intended public module architecture and formal naming policy are recorded in
[`docs/architecture.md`](docs/architecture.md).

## Continuous integration

Lean projects are checked by GitHub Actions. The workflow
[`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs on every push and
pull request: it builds the project **from a clean checkout** and then **fails
the run** if any `sorry` is reachable from `erdos_306` or if any axiom outside the
allowed set enters its dependencies. On success it prints the verification
summary (theorem and both axiom statements).

On pushes, the same workflow also runs two follow-up checks after verification
succeeds: Lean's linter over the Lake workspace, and `actionlint` over the
GitHub Actions workflows. These are deliberately sequenced after the proof
verification, so a broken verification run does not spend time on cleanup-only
checks. The separate [`lean-graph`](.github/workflows/lean-graph.yml) workflow is
manual (`workflow_dispatch`) because dependency-graph extraction can be useful
for review and refactoring, but is heavier and noisier than the push gate.

Each run appears under the repository's **Actions** tab as its own page; a run is
tied to the branch (or pull request) that triggered it. The badge above tracks
`main`.

## Citation

Cite this software via [`CITATION.cff`](CITATION.cff) (GitHub's "Cite this
repository"). For the problem itself:

- P. Erdős and R. Graham, *Old and new problems and results in combinatorial
  number theory*, L'Enseignement Mathématique (1980).
- T. F. Bloom, Erdős Problem #306, <https://www.erdosproblems.com/306> (accessed 2026-06-19).

The formal statement this proof is aligned with is due to the Formal Conjectures
project:

- The Formal Conjectures Authors, *The Formal Conjectures Repository* (2025),
  <https://github.com/google-deepmind/formal-conjectures>.
- M. Firsching, P. Lezeau, S. Mercuri, M. Z. Horváth, Y. Dillies, C. Sönne,
  E. Wieser, F. Zhang, T. Hubert, B. Agüera y Arcas, P. Kohli, *Formal
  Conjectures: An Open and Evolving Benchmark for Verified Discovery in
  Mathematics* (2026), [arXiv:2605.13171](https://arxiv.org/abs/2605.13171).

## License

[Apache License 2.0](LICENSE).

The formalization was developed with AI assistance; responsibility for the work
rests with the author, and — for the headline theorem — with the Lean kernel.
