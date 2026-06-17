# Aristotle delivery — V4: close Theorem C; advance the forcing layer

**Upload this whole folder** (`lake build`). State: the deterministic dispersion
engine (`SBEEDispersion.lean`) AND the full Theorem-C decomposition
(`SBEEFingerprint.lean`: `phaseP1`, `coldRigidity`, `cold_decoding_unique`,
`hot_count_bound`, `entropy_inequality` — all sorry-free) are machine-verified.
Paper proofs: included notes `29`, `30`, `32`. Plan below; **use your judgment,
and if you find any statement/step that is wrong or can't close as written, say so
explicitly in your report — that is the most valuable outcome** (a flat build
hides nothing, but flag suspicions early).

## P1 — close `fingerprint_count` (Theorem C), the final assembly

In `SBEEDispersion.lean`, `fingerprint_count` is the last open sorry of Theorem C.
Everything it needs is proved in `SBEEFingerprint.lean`. Assemble:

1. Choose the **fingerprint** `F` ⊆ `P` = the `⌈εR/(2 log 2X)⌉` smallest primes of
   `P` (so `|F|` meets `entropy_inequality`'s `Fc` bounds; and `|F| ≥ 208` and
   `8 ≤ |F|` hold for `X ≥ X0` since `|F| ≳ X^{2/3}`).
2. **Energy relation** (the one new sub-lemma): `∑_{q ∈ P∖F} tEnergy F a q (a q) ≤ QP P a`.
   Proof: `tEnergy F a q w = ∑_{p∈F}(crtRepr p q (a p) w/(pq))²`; the pairs
   `{(p,q): p∈F, q∈P∖F}` are distinct unordered pairs of `P`, hence a sub-family
   of the pairs summed in `QP`; all terms ≥ 0. So the sum is ≤ `QP P a`.
3. **Hot set & injection**: `Hot(a) := {q∈P∖F : tEnergy F a q (a q) ≥ G_F/7}`;
   `|Hot(a)| ≤ R/(G_F/7) = 7R/G_F` from step 2 (`hot_count_bound`). The level set
   injects (via `cold_decoding_unique`) into
   `{a|_F} × {(S, residues) : S ⊆ P∖F, |S| ≤ 7R/G_F}`, whose cardinality is
   `≤ (2X)^{|F|} · ∑_{h ≤ 7R/G_F} C(|P|,h)(2X)^h ≤ (2X)^{|F|} · (⌊7R/G_F⌋+1) · C(|P|,h_max)(2X)^{h_max}`.
   Bound by `entropy_inequality` (absorb the `(⌊·⌋+1)` polynomial factor into the
   `e^{εR}` by rescaling `ε`).
4. Conclude `N(R) ≤ |P| · e^{εR}` for `R ≥ R_C`. Close the sorry (or, if the
   cardinality-of-image step needs a Mathlib `Finset.card_le_card`/`Fintype`
   lemma you cannot find, isolate exactly that as a named sorry).

## P2 — the forcing layer (parallel): Theorems A, B in `SBEEForcing.lean`

These are elementary and use the **same** verified `lemmaD`/dispersion. Per notes
`29 §3` (Theorem A, dominant case: label uniqueness, label range, per-exception
energy `≥ N³/2¹⁵X²` via Lemma D, the count) and `29 §5–6` (Lemma E cross-label
energy; Theorem B forcing `R ≳ X/log³X`). Prove as much as cleanly closes; name
precise sorries for the rest. Theorem B is what lets the assembly cover `R < R_w`.

## P3 — if both above close: the assembly `single_block_counting`
Combine: `R < R_w` (Theorem B ⇒ dominant ⇒ Theorem A) + `R ≥ R_w` (Theorem C, with
mesh `R_C ≤ R_w`) + trivial, into `SBEEPartitionBound` (note 28 / `SBEEAssembly.lean`),
then Laplace-transform to the partition-function form. No laundering.

Report `lake build` + remaining sorries per theorem, and flag anything suspect.
