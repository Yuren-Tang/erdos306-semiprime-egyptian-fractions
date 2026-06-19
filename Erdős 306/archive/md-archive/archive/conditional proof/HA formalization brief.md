# Harmonic Aristotle formalization brief

Back to [[CP 00 Navigation]].

This brief is for formalizing the already-organized conditional proof package. The main line should **not** try to prove SBEE. Treat SBEE as a named hypothesis and formalize everything conditional on it.

Use standard Obsidian math delimiters in any new notes:

- inline math: `$...$`
- display math: `$$...$$`

---

# Objective

Formalize the existing conditional proof of:

**Conditional theorem.** Assuming [[CP 02 The single remaining condition|SBEE]], every rational `$a/b$` with squarefree `$b$` is a finite sum of reciprocals of distinct squarefree semiprimes.

The source files are:

- [[CP 01 Conditional theorem]]
- [[CP 02 The single remaining condition]]
- [[CP 03 Lemma bank]]
- [[CP 00 Navigation]]

The formalization output should make the proof suitable for a publication-level draft, still conditional on SBEE.

---

# Scope

Do formalize:

1. notation for prime sets, edge sets, CRT representatives, energies, and Fourier coefficients;
2. the deduction from Irving's theorem to the Irving-good pruning lemma, as a cited external-input lemma;
3. the cross-label divisor-energy lemma and its proof;
4. the conditional single-block counting theorem as a consequence of SBEE;
5. the cross-block label mismatch lemma;
6. the block-label Peierls collapse, at least to the level of a formally stated proposition with a detailed proof skeleton;
7. ordinary diagonal counting;
8. global control partition theorem;
9. edge construction, mass tuning, variance compatibility;
10. lattice-span gadget;
11. Fourier inversion, main arc, minor arc, positivity, and the reduction from `$1/b$` to `$a/b$`.

Do not prove:

- SBEE itself;
- the dyadic energy-entropy inequality inside SBEE;
- any new strengthening of Irving's theorem.

---

# Required precision

The final formalized package should explicitly separate:

- theorem assumptions;
- external cited inputs;
- internal proved lemmas;
- conditional inputs;
- construction parameters and their order of choice.

In particular, clarify the order:

1. fix squarefree `$b$`;
2. choose `$k_0$` large;
3. choose high scales `$K_1,K$`;
4. choose pruned prime blocks;
5. add internal, skeleton, mass, and gadget edges;
6. choose bounded-away Bernoulli parameters;
7. verify mass, variance, lattice span;
8. run Fourier positivity.

Make sure the final theorem never states the false unrestricted-denominator version.

---

# Expected deliverable

Create a new note:

`Erdős 306/conditional proof/HA formalized conditional proof.md`

It should be self-contained enough that a reader can follow the conditional proof without opening the old scattered drafts, while still using Obsidian links back to the source notes.

If you find a gap outside SBEE, do not patch it silently. Create a section:

`# Potential non-SBEE gaps`

and list the issue with the exact lemma where it occurs.

If there are no additional gaps, say explicitly:

`No non-SBEE mathematical gaps found at this formalization level.`

