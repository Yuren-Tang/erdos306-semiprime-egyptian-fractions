# Aristotle delivery — V5: the forcing layer (Theorems A, E, B) and assembly

**Upload this whole folder** (`lake build`). State: the dispersion engine
(`SBEEDispersion.lean`) and **all of Theorem C** (`SBEEFingerprint.lean`,
`fingerprint_count`) are machine-verified, sorry-free. The remaining SBEE sorries
are the forcing layer and the assembly. Paper proofs: included note `29` (§3, §5,
§6) and note `30`. **Use your judgment; flag any step that is wrong or won't close
as written — that's the most valuable report.**

These are elementary energy/counting estimates that reuse the **verified**
`lemmaD` (and you may reuse Theorem C's encoding/injection technique from
`SBEEFingerprint.lean`).

## P1 — Lemma E (`lemma_E_cross_label_energy`), `SBEEForcing.lean`
Note `29 §5`: for prime sets `C, C'` (labels `n ≠ n'`, `|n|,|n'| ≤ B ≤ X²/4`),
`|C| ≥ 32(B/X+1)`, `|C'| ≥ 8`, disjoint:
`∑_{p∈C, q∈C'} (H_pq/pq)² ≥ c·|C|³|C'|/X²`. Direct divisor argument via `lemmaD`
(`u·p ≡ d (mod q)` for the cross pairs; ≤2 primes divide `d`; choose `δ=min(¼,|C|/64X)`).

## P2 — Theorem A (`theorem_A_dominant_count`), `SBEEForcing.lean`
Note `29 §3`. For an `m`-dominant assignment (some label `m`, `|m|≤X²/2`, class
`≥(1−ρ)N`): (A1) label uniqueness; (A2) label range `|m| ≤ 5√R/((1−ρ)σ_P)`;
(A3) **each exception vertex carries energy `≥ N³/2¹⁵X²` via `lemmaD`** (the key
step — analogous to Theorem C's dispersion use); (A4) count `≤ e^{εR}(1+C_ρ√R/σ_P)`
(entropy bookkeeping: label choices × exception set/residues, exceptions
`≤ R/E₁` — reuse the Theorem-C counting style). Add `1 ≤ P.card` (or the
`N ≥ X/(2log X)` hypothesis) as Theorem C needed.

## P3 — Theorem B (`theorem_B_nondominant_forcing`), `SBEEForcing.lean`
Note `29 §6`: non-dominant ⇒ `R ≥ c·N²/(X log X) ≳ X/log³X`. Uses the base-point/
short-list covering (§4), Lemma E (P1), and tiny-mass accounting. (`corollary_SBEE_below_window`
is already proved on top of A+B.)

## P4 — assembly (`single_block_counting`), `SBEEAssembly.lean`
Combine `R < R_w` (Theorem B ⇒ dominant ⇒ Theorem A) + `R ≥ R_w` (Theorem C, with
the mesh `R_C ≤ R_w` — provable asymptotically, may be a hypothesis `X ≥ X₁`) +
trivial `R > R_triv`, into `SBEEPartitionBound` (note 28). The partition-function
form follows from the level-set bound by Laplace transform (`∑_a e^{-cQ} = ∫ N(R) c e^{-cR} dR`,
`c > 2ε`). No laundering.

Report `lake build` + remaining sorries per theorem, and flag anything suspect.
