# V4 progress report — Theorem C closed; forcing layer advanced

## Build / packaging

* **Packaging fix.** The delivered `.lean` files were at the repository root, but
  every `import RequestProject.X` and the lakefile glob `RequestProject.+` require
  them under `RequestProject/`.  As shipped, `lake build` would resolve no targets.
  All sources were moved into `RequestProject/`; the whole project now builds with
  `lake build` (8054 jobs, success).

## P1 — Theorem C (`fingerprint_count`): **CLOSED, sorry-free**

`fingerprint_count` was moved out of `SBEEDispersion.lean` (which cannot see the
cold-rigidity/entropy layer it imports *from*) into `SBEEFingerprint.lean`, where
all of `coldRigidity`, `cold_decoding_unique`, `hot_count_bound`,
`entropy_inequality` are available, and there fully proved.

`#print axioms SBEEFingerprint.fingerprint_count` →
`[propext, Classical.choice, Quot.sound]` (standard only).

New sorry-free supporting results added in `RequestProject/SBEEFingerprint.lean`:

* `extendAssign` / `extendAssign_injective` — bridge from `BlockAssignment P`
  to total residue functions used by the fingerprint energy.
* `exists_lower_subset` — fingerprint selection (`F` = the `k` smallest primes).
* `energy_relation` — `∑_{q∈P∖F} t_q(a_q) ≤ Q_P(a)` (the new sub-lemma of the plan).
* `decoding_card_bound` — the decoding **injection + sub-set/residue counting**
  (the cardinality-of-image heart): level-set card
  `≤ (2X)^{|F|}·(h_max+1)·C(|P|,h_max)·(2X)^{h_max}`, via `cold_decoding_unique`
  and `hot_count_bound`.
* `levelset_card_le_pow` — the trivial bound `≤ (2X)^{|P|}`.
* `entropy_inequality2` — `entropy_inequality` with the `(h+1)` hot-size factor
  absorbed (doubled exponent), used to close the assembly.
* helper estimates `block_card_le_two_mul`, `exp_card_trick`, `cube_rpow_ge`,
  `Fc_ge_helper`, `hmax_bound_helper`.

`SBEEDispersion.lean` and `SBEEFingerprint.lean` are now both **entirely
sorry-free** (this includes `dispersion_residue_count` / `dispersion_energy_bound`,
which the old header listed as `sorry` but were in fact already proved).

### Verification finding (flagged, as requested)

The statement of Theorem C as written in note 30 / V1 is **false for an empty
block**: for `P = ∅` the block has exactly one (empty) assignment with `Q_P = 0`,
so the level-set count is `1`, while the right-hand side `N·e^{εR} = 0·e^{εR} = 0`.
(This was confirmed by an automated disproof of the original statement.)  The fix
is the minimal, faithful hypothesis `1 ≤ P.card` (the paper tacitly works with
substantial blocks, `N ≥ X/(2 log X) ≥ 2`); it is documented on the theorem.

## P2 — forcing layer (`SBEEForcing.lean`)

* `corollary_SBEE_below_window` — **proved** as the clean Theorem A + Theorem B
  combination (every low-energy assignment with `R ≤ c'·X/log³X` is dominant, then
  Theorem A counts it).  It currently rests on the two analytic sorries below.
* `theorem_A_dominant_count`, `lemma_E_cross_label_energy`,
  `theorem_B_nondominant_forcing` — remain as named `sorry`s (the genuinely
  analytic estimates: per-exception/cross-label energy via Lemma D and the
  covering/mass bookkeeping).  These are the next targets.

## P3 — assembly (`SBEEAssembly.lean`)

* `single_block_counting` — remains `sorry` (needs the `R_C ≤ R_w` mesh and the
  Laplace transform from the level-set bound to the partition function, on top of
  the P2 sorries).

## Remaining `sorry` inventory

* `SBEEForcing.lean`: `theorem_A_dominant_count`, `lemma_E_cross_label_energy`,
  `theorem_B_nondominant_forcing` (P2).
* `SBEEAssembly.lean`: `single_block_counting` (P3).
* Pre-existing, outside the V4 scope: `BlockCRTEnergy.lean` (the four
  `*_uniform` predicates), `SBEE.lean` (5 high-level theorems),
  `SingleBlockCounting.lean`, `FourierPositivity.lean`.
