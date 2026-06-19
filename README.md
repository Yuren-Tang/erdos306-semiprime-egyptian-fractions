# A formally verified proof of Erdős Problem 306 in Lean 4

[![verify-erdos-306](https://github.com/Yuren-Tang/erdos-306/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/Yuren-Tang/erdos-306/actions/workflows/ci.yml)

Yuren Tang — [ORCID 0009-0006-0847-3330](https://orcid.org/0009-0006-0847-3330)

This repository contains a **complete, machine-checked proof of Erdős Problem
306**, formalized in Lean 4 with Mathlib. The proof is `sorry`-free; it is
complete modulo **two named classical inputs**, each a verbatim transcription of
a theorem of Rosser–Schoenfeld (1962), cited to its primary source.

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

So a reviewer need not read the internal proof. Beyond the statement above, the
sole hand-check is that those **two axioms** transcribe their primary source
faithfully. With $\pi$ the prime-counting function and $B$ the Mertens constant
(RS eq. (2.10), p. 65, $B = 0.26149721284764\ldots$):

- **`rosser_schoenfeld_cor3`** — RS **Corollary 3, eq. (3.8), p. 69**:

  $$\frac{3x}{5\log x} \;<\; \pi(2x) - \pi(x), \qquad 20\tfrac{1}{2} \le x.$$

  ```lean
  axiom rosser_schoenfeld_cor3 (x : ℝ) (hx : (41 : ℝ) / 2 ≤ x) :
      3 * x / (5 * Real.log x) <
        (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)
  ```

- **`rosser_schoenfeld_thm5`** — RS **Theorem 5, p. 70**, the bounds (3.17) and
  (3.18), each under its own range:

  $$\log\log x + B - \frac{1}{2\log^2 x} \;<\; \sum_{p \le x} \frac{1}{p} \qquad (1 < x),$$

  $$\sum_{p \le x} \frac{1}{p} \;<\; \log\log x + B + \frac{1}{2\log^2 x} \qquad (286 \le x).$$

  ```lean
  -- `primeRecipSum x` is `∑ 1/p` over primes p ≤ x.
  axiom rosser_schoenfeld_thm5 :
      ∃ B : ℝ, ∀ x : ℝ,
        (1 < x →
            Real.log (Real.log x) + B - 1 / (2 * (Real.log x) ^ 2) < primeRecipSum x) ∧
        (286 ≤ x →
            primeRecipSum x < Real.log (Real.log x) + B + 1 / (2 * (Real.log x) ^ 2))
  ```

  (`B` is stated *existentially*, exactly as Theorem 5 provides, rather than pinning
  a rounded decimal.)

J. B. Rosser and L. Schoenfeld, "Approximate formulas for some functions of prime
numbers," *Illinois Journal of Mathematics* **6**(1) (1962), 64–94.
[DOI: 10.1215/ijm/1255631807](https://doi.org/10.1215/ijm/1255631807).

So the entire trust boundary — the problem statement, the Lean theorem, and the two
axioms with their sources — is visible on this page. Each CI run re-prints the same
audit, so it can also be checked from a run without opening any file.

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

Toolchain `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`.

## Continuous integration

Lean projects are checked by GitHub Actions. The workflow
[`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs on every push and
pull request: it builds the project **from a clean checkout** and then **fails
the run** if any `sorry` is reachable from `erdos_306` or if any axiom outside the
allowed set enters its dependencies. On success it prints the verification
summary (theorem, both axiom statements, citations).

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
