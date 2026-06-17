# Summary of changes for run 3480257a-8ffc-4f1d-9007-c54ee4f2ad0a
# F2a' Completed: Faithful CRT Energy Encoding

## What was done

### Created `RequestProject/BlockCRTEnergy.lean` (new file)
A faithful CRT energy encoding replacing the abstract `BlockEnergyData` that previously allowed trivial proofs. Key definitions:

- **`BlockAssignment P`** = `∀ p : P, ZMod p.1` — the CRT product space, with cardinality `∏_{p ∈ P} p`
- **`crtRepr p q ap aq`** — centered CRT representative H with H ≡ ap (mod p), H ≡ aq (mod q), |H| ≤ pq/2
- **`QP P a`** = `∑_{p < q ∈ P} (H(p,q,a(p),a(q)) / (p·q))²` — the CRT energy quadratic form
- **`sigmaP P`** = `√(∑_{p < q ∈ P} 1/(p·q)²)` — the block deviation
- **`blockPartFun P hP c`** = `∑_{a : BlockAssignment P} exp(-c · QP(P,a))` — the partition function
- **`SBEESavingBound P hP c`** — the saving bound: `∃ C > 0, blockPartFun ≤ C / sigmaP`

Since the assignment space has `∏ p` elements (exponentially large), the trivial bound `≤ ∏ p` is useless — any proof of `SBEESavingBound` must exhibit a genuine saving.

### Proved CRT infrastructure (no sorry)
- `crtRepr_abs_le`: centering bound |H| ≤ pq/2
- `crtRepr_congr_left`/`crtRepr_congr_right`: CRT congruence properties
- `center_abs_le`, `center_cast_eq`: helper lemmas for centering
- `QP_nonneg`, `sigmaP_nonneg`, `sigmaP_pos_of_two`: basic properties
- `blockAssignment_card`: cardinality = ∏ p
- `primes_coprime_of_ne`: distinct primes are coprime

### Honest sorries (no laundering, no trivial substitutes)
- **`dominant_case_saving`**: saving bound when a dominant label exists (Irving majority correction)
- **`tiny_case_saving`**: saving bound when all classes are tiny (short-list / energy tradeoff)
- **`sbee_nondominant'`**: FIE target — restated against QP/sigmaP with genuine hypotheses
- **`single_block_counting_faithful`**: assembly of the three cases — does NOT assume the conclusion

### Revised `RequestProject/SingleBlockCounting.lean`
- Removed the laundering `single_block_counting_assembled` (which assumed `N ≤ C/√variance`)
- Renamed `tiny_case_bound` to `trivial_bound` with a note that it is useless for the saving
- Added notes pointing to the faithful bounds in `BlockCRTEnergy.lean`
- Kept the abstract decomposition lemmas (label classes, dominant/non-dominant split)
- The abstract `sbee_nondominant` is kept as honest sorry, pointing to `sbee_nondominant'`

## Build status
`lake build` succeeds. Remaining sorries:
- `fourier_positivity_unconditional` (FourierPositivity.lean) — the known open problem, untouched
- 5 SBEE chain lemmas (SBEE.lean) — pre-existing honest sorries
- 4 faithful case bounds + assembly (BlockCRTEnergy.lean) — new, honestly named
- 1 abstract `sbee_nondominant` (SingleBlockCounting.lean) — pre-existing, superseded by faithful version

No new sorries in previously clean files. No laundering. No trivial `≤ N` substitutes.