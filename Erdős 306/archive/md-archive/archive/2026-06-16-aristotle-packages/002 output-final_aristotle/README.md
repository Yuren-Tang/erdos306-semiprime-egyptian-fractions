This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Erdős Problem 306 — Lean 4 formalization

A clean Lean 4 / Mathlib formalization of **Erdős Problem 306**
(<https://www.erdosproblems.com/306>):

> **Problem 306 ([ErGr80]).** Let `a/b ∈ ℚ_{>0}` with `b` squarefree. Are there
> integers `1 < n₁ < ⋯ < n_k`, each the product of two distinct primes, such
> that `a/b = 1/n₁ + ⋯ + 1/n_k`?

> ⚠️ **This is an OPEN mathematical problem.** As recorded on
> erdosproblems.com/306 (status accessed 2026-06-16): *"This is open, and cannot
> be resolved with a finite computation."* No proof is known. **This repository
> does not contain — and does not claim — a complete proof.** It provides a
> faithful Lean statement together with everything that *is* provable, and
> isolates the single open input behind one clearly-cited `sorry`. See
> [Verification status](#verification-status).

## What this repository actually establishes

Everything below is machine-verified and **sorry-free**, except for the single
isolated open input:

1. **Faithful statement** of the problem: `erdos_306`
   (`RequestProject/Erdos306.lean`).
2. **Necessity** of the squarefree hypothesis on `b`:
   `necessity_squarefree_denom` (`RequestProject/Defs.lean`). A finite sum of
   reciprocals of squarefree integers always has a squarefree reduced
   denominator, so the squarefree condition on `b` is genuinely required.
3. **Reduction** of the general numerator case `a/b` to the unit case `1/b`
   (denominator-avoiding form): `reduction_to_unit_numerator_avoiding`
   (`RequestProject/MainTheorem.lean`).
4. **Concrete instances**, fully verified via the triple-prime identity:
   `1/2, 1/3, 1/5, 1/6, 1/7, 1/11` (`RequestProject/Erdos306.lean`).

The only gap is the unit case `1/b` for general squarefree `b`, which **is** the
open content of Problem 306. It is isolated as the single `sorry`-bearing lemma
`erdos_306_unit_case_open`, documented and cited to [ErGr80].

## The single open input ("isolated citation")

There is exactly **one** unproved statement in the whole built library, and it is
the open problem itself:

```lean
/-- OPEN INPUT — Erdős Problem 306, unit case (avoiding form). -/
theorem erdos_306_unit_case_open
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b) := by
  sorry
```

* **Citation.** [ErGr80] P. Erdős and R. Graham, *Old and new problems and
  results in combinatorial number theory*, Monographies de L'Enseignement
  Mathématique (1980), MR 0592420; recorded as Problem 306 at
  erdosproblems.com/306.
* **Status.** Open. No proof is known. It is recorded as an ordinary
  `theorem ... := by sorry`, **not** as an `axiom`, so that it remains fully
  visible to `#print axioms`.
* The closest published progress is the *three*-prime, `b = 1` analogue proved by
  [BEG15] S. Butler, P. Erdős and R. Graham, *Egyptian fractions with each
  denominator having three distinct prime divisors*, Integers **15** (2015),
  Paper No. A51, MR 3437526. This is a different, weaker statement and does not
  settle Problem 306.

There are **no `axiom` declarations and no `@[implemented_by]` attributes**
anywhere in the built library; the lone gap is the `sorry` above.

## Entry point

Open **`RequestProject/Erdos306.lean`**. Its module header is the authoritative,
self-contained description of the statement, the honest status, the verified
content, and the cited open input. The file ends with `#print axioms erdos_306`
so the dependency trace is visible on build.

## Building / verifying

* Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (see `lean-toolchain`,
  `lakefile.toml`, `lake-manifest.json`).
* Prebuilt object files for this package are shipped in
  `prebuilt-oleans.tar.gz` (extract at the repository root to restore
  `.lake/build/lib/lean/RequestProject/…`). Mathlib itself is fetched/built by
  `lake`.

```sh
tar xzf prebuilt-oleans.tar.gz      # optional: restore this package's .olean files
lake build                          # builds RequestProject (Mathlib from cache)
```

A successful build prints
`'erdos_306' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`.
The `sorryAx` entry corresponds to, and only to, the cited open input
`erdos_306_unit_case_open`.

## Verification status

| Component | Where | Status |
|---|---|---|
| Statement `erdos_306` (faithful) | `Erdos306.lean` | ✓ stated |
| Necessity of squarefree `b` | `Defs.lean` (`necessity_squarefree_denom`) | ✓ verified |
| Reduction `a/b ⇝ 1/b` (denominator-avoiding) | `MainTheorem.lean` | ✓ verified |
| Triple-prime identity | `Erdos306.lean` (`triple_prime_sum`) | ✓ verified |
| Concrete instances `1/2,1/3,1/5,1/6,1/7,1/11` | `Erdos306.lean` | ✓ verified |
| Unit case `1/b`, general squarefree `b` | `Erdos306.lean` (`erdos_306_unit_case_open`) | ✗ **OPEN** (the single cited `sorry`) |

## Project layout

* `RequestProject/Erdos306.lean` — **entry point**: statement, honest status,
  cited open input, concrete instances, and `erdos_306`.
* `RequestProject/Defs.lean` — basic definitions (semiprimes, Egyptian
  representations) and the necessity of the squarefree denominator.
* `RequestProject/MainTheorem.lean` — the numerator reduction `a/b ⇝ 1/b`.
* `notes/` — archived development notes, plans, and logs (reference only).
* `notes/abandoned-circle-method-route/` — a large, **incomplete** exploratory
  attempt to attack the open unit case via the circle method. It is preserved for
  reference only, is **not** part of the build, and bottoms out (after much
  scaffolding) at the same open problem. It contains numerous `sorry`s and should
  not be cited as verified content.

## Caveat on completeness

Erdős Problem 306 is open. This repository is a faithful formalization of the
problem statement together with its verified necessity direction, its verified
reduction to the unit case, and verified concrete instances. The unit case for
general squarefree `b` remains an open problem and is isolated as a single cited
`sorry`. The repository must **not** be cited as a complete proof of Erdős 306.
