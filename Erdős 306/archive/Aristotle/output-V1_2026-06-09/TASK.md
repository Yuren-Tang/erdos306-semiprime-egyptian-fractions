# Aristotle delivery — VERIFY the SBEE single-block counting proof

**Upload this whole folder.** It is a self-contained Lean 4 package
(`leanprover/lean4:v4.28.0` + Mathlib; build with `lake build`). It currently
builds with these intended sorries only: `fourier_positivity_unconditional`
(out of scope), the 5 SBEE chain lemmas in `SBEE.lean`, and the single-block
sorries in `BlockCRTEnergy.lean`/`SingleBlockCounting.lean`.

**This task is different from the earlier exploratory ones: it is VERIFICATION.**
There is now a complete written paper proof of the SBEE single-block counting
theorem, in the two markdown files included here:

- `29 SBEE Master - …md` — setup; **Lemma D** (deterministic dispersion),
  **Theorem A** (dominant case), **Lemma E** (cross-label energy), **Theorem B**
  (non-dominant forcing); SBEE for $R\le c'X/\log^3X$.
- `30 Theorem C - …md` — **Theorem C** (fingerprint count for $R\ge R_C$) and the
  assembly A+B+C ⇒ full single-block counting = SBEE.
- `28 Faithful SBEE Statement …md` — the faithful target encoding
  (`SBEEPartitionBound`, no free labeling; the `QP`/`sigmaP` definitions already
  exist in `BlockCRTEnergy.lean`).

Your job is to **formalize these proofs and report exactly which steps verify and
which do not** — naming every unclosed step as a precise `sorry`. Do **not**
invent weaker statements, do **not** assume conclusions, do **not** launder. If a
step in the paper is wrong or unprovable as written, that is the single most
valuable thing you can find — say so explicitly.

## Success criterion

Build stays green. Report, per theorem, whether it is fully proved or which
sub-lemmas remain `sorry`, with a one-line reason for each `sorry`. The pattern of
sorries is the deliverable.

## Priority order (do P1 fully before P2; partial progress is fine and useful)

### P1 — the crux: Lemma D + Theorem C  (the novel, most-scrutinized part)
Work in a new file `RequestProject/SBEEDispersion.lean` (import `BlockCRTEnergy`).
1. **Lemma D** (`29 §2`): for prime $q\in[X,2X]$, integer $w$ with $q\nmid w$, and
   $U\ge1$, $U<X$: `#{(u,p) : p∈[X,2X] prime, |u|≤U, u*p ≡ w (mod q)} ≤ 2*(2*U+1)`.
   This is purely elementary (residue class meets interval in ≤2; $u$ invertible).
   **Prove it (no sorry).**
2. **The dispersion corollary** used by Theorem C (`30 §1`, "Dispersion (Lemma D
   form)"): for $q\notin F$, integer $E$ with $q\nmid E$, $0<|E|<q$, $\delta=|F|/(32X)$:
   `#{p∈F : ‖E·q̄/p‖ ≤ δ} ≤ 2*(4δX+1) ≤ |F|/2`, hence
   `∑_{p∈F} ‖E·q̄/p‖² ≥ |F|³/(2^11 X²) =: G_F`. (Uses: $p\mid E-uq$, $E-uq\not\equiv0\ (q)$,
   $|E-uq|<X^3$ has ≤2 prime factors in $[X,2X]$.) **Prove it.**
3. **Theorem C** (`30 §1`): the fingerprint count. Encode the cold-rigidity
   (unique consistent residue per cold vertex — note the **representative
   discipline** in `30 §1`: use centered integer reps, do NOT recenter the
   difference mod q) and the entropy bookkeeping. The bound is asymptotic in $X$
   ($X\ge X_0(\varepsilon)$). **Prove what you can; isolate the entropy/counting
   bookkeeping or any analytic estimate as named sorries** (e.g.
   `theorem fingerprint_count … := sorry` with a docstring on the gap).

### P2 — Theorem A, Lemma E, Theorem B
Formalize (`29 §3, §5, §6`) into `RequestProject/SBEEForcing.lean`. Theorem A
(dominant): label uniqueness (A1), label range (A2), per-exception energy via
Lemma D (A3), the count (A4). Lemma E (cross-label energy). Theorem B (forcing
$R\gg X/\log^3X$). Name sorries for the parts you cannot close.

### P3 — assembly
`single_block_counting : SBEEPartitionBound c` (note 28's faithful predicate),
assembling A (R<R_w) + C (R≥R_w) + trivial, with the mesh $R_C<R_w$ as an explicit
hypothesis or lemma. No laundering; the assembly may rest on the P1/P2 sorries.

## Notes for the verifier (soft spots the author flagged)

- The **phase identity** slack `|H| ≥ pq·‖·‖ − q` at both window ends (`30 §1`).
- The **constant chase** in `G_F`, `T = G_F/7`, and the `6T+1 ≤ G_F` step.
- **Theorem B**'s covering bookkeeping (`29 §6`) and the tiny-mass accounting.
- The **mesh** `R_C ≪ R_w` is only asymptotic (crossover $X_0$ large but explicit).
- Whether centered-representative handling of residues mod `q` is done correctly
  (the author corrected one such slip — see the "Verification note" in `30 §1`).

These are exactly where a real error, if any, would hide. Surface them.
