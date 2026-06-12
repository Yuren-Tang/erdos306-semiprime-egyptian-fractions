# Aristotle delivery — V6: Theorem A, Theorem B, and the assembly

**Upload this whole folder** (`lake build`). State: machine-verified, sorry-free —
the dispersion engine (`SBEEDispersion.lean`), all of **Theorem C**
(`SBEEFingerprint.lean`, `fingerprint_count`), and **Lemma E**
(`lemma_E_cross_label_energy` in `SBEEForcing.lean`, with helpers `lemmaE_fiber`,
`lemmaE_close_count`). Remaining SBEE sorries: `theorem_A_dominant_count`,
`theorem_B_nondominant_forcing` (`SBEEForcing.lean`), `single_block_counting`
(`SBEEAssembly.lean`). Paper proofs: included notes `29`, `30`. **Use judgment;
flag any wrong/unprovable step. Include ALL hypotheses faithfully (e.g. prime-in-
[X,2X], P.card lower bounds) — earlier statements were buggy for omitting them.**

## P1 — Theorem A (`theorem_A_dominant_count`), `SBEEForcing.lean`
Note `29 §3`. For an `m`-dominant assignment: (A1) label uniqueness; (A2) label
range `|m| ≤ 5√R/((1−ρ)σ_P)` (restricted-σ comparison `σ_{C_m}² ≥ ((1−ρ)²/24)σ_P²`);
(A3) **each exception vertex carries energy `≥ N³/2¹⁵X²`** — a direct application of
the verified `lemmaD` (mirror Theorem C's dispersion use / `lemmaE_fiber`);
(A4) the count `≤ e^{εR}(1+C_ρ√R/σ_P)` — exception entropy bookkeeping
(`exceptions ≤ R/E₁`, `binom × residues`), **reuse the Theorem-C encoding/entropy
infrastructure** in `SBEEFingerprint.lean` (`decoding_card_bound`,
`entropy_inequality` are templates). Include the faithful hypotheses
(`1 ≤ P.card` / `N ≥ X/(2 log X)`, primes in `[X,2X]`, `|m| ≤ X²/2`).

## P2 — Theorem B (`theorem_B_nondominant_forcing`), `SBEEForcing.lean`
Note `29 §6`, now with **Lemma E available**. Steps: the base-point averaging
(`29 §4`: `∃ p₀` with `#{q:|H_{p₀q}|>B} ≤ 32N/A²`, `B=A√R X²/N`); the short list
`𝓛` and classes `C_n`; the **mass accounting** `M₂ ≥ ρN/2` (the flagged soft spot —
chain: covered mass `≥ N−32N/A²−1`, no class `>(1−ρ)N`, tiny mass `≤ ρN/8`); then
`lemma_E_cross_label_energy` on the substantial classes ⇒ `R ≥ c·N²/(X log X) ≳ X/log³X`.
Consider extracting the covering and mass-accounting as named sub-lemmas (as note 32
did for Theorem C) if the monolith resists. Include the reusable bridge
`∑_{p∈C}∑_{q∈C'}(H/pq)² ≤ Q_P` (noted in the V5 report).

## P3 — assembly (`single_block_counting`), `SBEEAssembly.lean`
Combine `R < R_w` (Theorem B ⇒ dominant ⇒ Theorem A) + `R ≥ R_w` (Theorem C; mesh
`R_C ≤ R_w` — asymptotic, take as hypothesis `X ≥ X₁`) + trivial, into
`SBEEPartitionBound` (note 28); then Laplace-transform the level-set bound to the
partition-function form (`∑_a e^{-cQ} = ∫₀^∞ N(R)·c·e^{-cR} dR`, `c>2ε`). No laundering.

Report `lake build` + remaining sorries per theorem, and flag anything suspect.
