# Aristotle delivery — V3: formalize Theorem C via its decomposition

**Upload this whole folder.** Self-contained Lean 4 package (`lake build`). State:
the **deterministic dispersion engine is fully machine-verified** in
`SBEEDispersion.lean` (`lemmaD`, `card_prime_factors_dyadic_le_two`,
`phase_dvd_witness`, `dispersion_residue_count`, `dispersion_energy_bound`,
`phase_sub_le` — all sorry-free). The single remaining sorry there is
`fingerprint_count` (Theorem C). A monolithic attempt failed; **note `32` (included)
decomposes Theorem C into 5 reachable lemmas and proves the two new ones in full.**
Formalize them in order. No laundering/weakening; name any unclosed step as a
precise `sorry` with a one-line reason.

Work in `RequestProject/SBEEFingerprint.lean` (import `BlockCRTEnergy`,
`SBEEDispersion`). Definitions to add: `tEnergy q w := ∑_{p∈F} (crtRepr p q (a p) w / (p*q))^2`
(the per-vertex fingerprint energy; `F`, `a` as parameters), matching note 32.

## P1 (HEART — do first, fully): Lemma P1 then Lemma P2

1. **Lemma P1 (phase identity)** — note `32` Sub-lemma 1, full proof there:
   `phase (ã_p − w̃) q p ≤ |crtRepr p q a_p w| / (p*q) + 1/X`. Use `crtRepr`'s
   congruences (`crtRepr_congr_left/right` in `BlockCRTEnergy.lean`): write
   `H = w̃ + v*q`, `v ≡ (ã_p − w̃)·q̄ (mod p)`, then
   `‖v/p‖ = ‖(ã_p−w̃)q̄/p‖ = phase(…)` and `‖v/p‖ ≤ |H|/(pq) + 1/(2p)`. Prove it.

2. **Lemma P2 (cold rigidity)** — note `32` Sub-lemma 2, full proof there: for
   `q ∉ F`, at most one residue `w` has `tEnergy q w < G_F/7`. Uses ONLY the
   verified `dispersion_energy_bound`, `phase_sub_le`, and Lemma P1. Centered
   integer reps; `E = w̃' − w̃`, `0<|E|<q`, `q∤E`; the `(α+β+γ)²≤3(α²+β²+γ²)` step.
   **This is the novel core — getting it machine-checked is the key deliverable.**

## P2 (counting): Lemma P3/P3' + Lemma P4 → `fingerprint_count`

3. **Lemma P3 (decoding injection)** + **P3' (hot bound `≤7R/G_F`)** — note `32`
   Sub-lemma 3: the map `a ↦ (a|_F, Hot(a), residues on Hot)` is injective on the
   level set (cold vertices decoded uniquely via P2); `|Hot(a)| ≤ R/T` from
   `∑_q tEnergy q (a q) ≤ Q_P(a) ≤ R`.
4. **Lemma P4 (entropy inequality)** — note `32` Sub-lemma 4: the real-analysis
   bound `(2X)^|F| · C(|P|,h) (2X)^h ≤ |P| e^{εR}` for `R ≥ R_C`. Fiddly logs;
   isolate as a named sorry if needed.
5. **Assemble `fingerprint_count`** from P3+P4 (card of level set ≤ card of image
   set ≤ product bound). Remove its sorry if all parts close; else leave the
   precise residual sorry.

## P3 (parallel, optional this round): forcing layer
Theorems A, B (`SBEEForcing.lean`, notes 29 §3,§6) use the same Lemma D and are
elementary. Formalize if time permits.

Report `lake build` and the exact remaining sorries per lemma.
