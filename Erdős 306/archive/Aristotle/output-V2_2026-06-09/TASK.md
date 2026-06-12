# Aristotle delivery — V2: discharge the foundational sorries of the SBEE proof

**Upload this whole folder.** Self-contained Lean 4 package (`leanprover/lean4:v4.28.0`
+ Mathlib; `lake build`). V1 already formalized the SBEE proof statements
faithfully and **proved Lemma D** (`SBEEDispersion.lean`); the full per-theorem
status is in `SBEE_VERIFICATION_REPORT.md`, and the paper proofs are in the
included notes `29`, `30` (`31` has the new residue-count proof). This task
discharges the next sorries, bottom-up. **No laundering, no weakening; name any
step you cannot close as a precise `sorry` with a one-line reason.**

## P1 — complete the dispersion engine (elementary; full proof provided)

In `SBEEDispersion.lean`:

1. **Factor out** from `lemmaD_fiber`'s proof the lemma
   `card_prime_factors_dyadic_le_two`: for `n : ℤ`, `n ≠ 0`, `|n| < X^3`, the set
   `{p ∈ [X,2X] : p.Prime ∧ (p:ℤ) ∣ n}` has card `≤ 2`. (Three distinct primes
   `≥ X` dividing `n` give `|n| ≥ X^3`.)

2. **Prove `dispersion_residue_count`** (currently `sorry`) following note `31 §4`:
   for `p ∈ F` with `phase E q p ≤ δ` (`δ = |F|/(32X)`), there is an integer `s`,
   `|s| ≤ 2δX`, with `(p:ℤ) ∣ E − s*q` (set `s = E·q̄ − r·p` where `r` is the
   nearest integer to `E·q̄/p`; then `E ≡ s*q (mod p)` via `q*q̄ ≡ 1 (mod p)`);
   `E − s*q ≠ 0` (else `q ∣ E`) and `|E − s*q| < X^3`. Bound the set by the
   `s`-fibres (`≤ 4δX+1` values of `s`, each `≤ 2` primes via step 1):
   `≤ 2(4δX+1) = |F|/4 + 2 ≤ |F|/2`.

3. **Complete `dispersion_energy_bound`** from step 2 by the constant chase
   `δ²·(|F|/2) = |F|³/(2^11 X²)` (its body reportedly already reduces to the
   residue count). After P1 the **dispersion engine is fully machine-verified.**

## P2 — Theorem C (`fingerprint_count`), the crux

Following note `30 §1`. Use the now-proved `dispersion_energy_bound`. Key steps:
the phase identity `‖(a_p−w̃)q̄/p‖ ≤ √(t^{(p)}_q(w)) + 1/X` (centered integer reps
`w̃ ∈ (−q/2,q/2]`); **cold rigidity** (a cold vertex `q`, `t_q < G_F/7`, has a
unique consistent residue — see the representative discipline / "Verification
note" in `30 §1`, which corrected an earlier slip: do NOT recenter the difference
mod q); the encoding (fingerprint `a|_F`, entropy `≤ εR/2`; hot set `≤ 7R/G_F`,
entropy `≤ εR/2` for `R ≥ R_C`; cold vertices decoded uniquely = zero entropy).
Prove as much as possible; isolate the entropy/counting bookkeeping as named
sorries if needed. **This is the most important verification target** — if it
holds, the novel core of SBEE is machine-confirmed.

## Notes
- `IrvingGood` is correctly just a dyadic-window + density predicate (the
  deterministic Lemma D removes any need for Irving phase-dispersion pruning); it
  is faithful — consider renaming to `DyadicPrimeBlock` for clarity (optional).
- Report `lake build` and the exact remaining sorries per theorem.
