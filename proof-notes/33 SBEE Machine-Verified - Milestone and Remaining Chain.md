# SBEE Machine-Verified: Milestone and Remaining Chain

Back to [[00 README]]. **Milestone (2026-06-09): the SBEE single-block counting
condition — CP 02's "the single remaining condition" of the conditional proof —
is fully machine-verified in Lean, sorry-free, against a faithful statement.**

## 1. What is verified

`single_block_counting : SBEEPartitionBound c` (`SBEEAssembly.lean`), sorry-free,
axioms = `propext, Classical.choice, Quot.sound` only (no `sorryAx`). The whole
chain it rests on is sorry-free:

* **Faithful statement** (unchanged from [[28 Faithful SBEE Statement - Design (4th iteration)]]):
  `SBEEPartitionBound c = ∃C>0, ∀ prime block P, IrvingGood P → 2≤|P| → blockPartFun P c ≤ C/sigmaP P`
  (uniform `C`; `IrvingGood` = dyadic window + density; CRT energy `QP`/`sigmaP`/
  `blockPartFun` per CP 02 §1; no free labeling). Verified faithful.
* **Dispersion engine** (`SBEEDispersion.lean`): Lemma D + the residue/energy
  corollaries.
* **Theorem C** (`SBEEFingerprint.lean`): the fingerprint count — cold rigidity,
  decoding injection, entropy bound.
* **Theorem A** (dominant), **Lemma E** (cross-label energy), **Theorem B**
  (non-dominant forcing) (`SBEEForcing.lean`); the assembly `unified_levelset`
  (A+B below the window, C above) + `mesh_lemma` + `partfun_series_bound`
  (Laplace transform) (`SBEEAssembly.lean`).

## 2. Why this matters / how it was simplified

This was the named open condition of the entire conditional proof. The verified
proof is **elementary**: the only dispersion input is the **deterministic** Lemma D
(an interval of length ≤ modulus meets a residue class in ≤2 points + a nonzero
integer <X³ has ≤2 prime factors in [X,2X]). **No Irving/Kloosterman/Fourier/
polymer at the block level** — a genuine simplification of the original route
(which routed block-level dispersion through Irving-good pruning). `IrvingGood` is
now misnamed (it is just window+density); no pruning is needed.

## 3. Honest scope — what this does NOT yet give

`SBEEPartitionBound` is the **new, faithful** condition (in `SBEEAssembly.lean`). It
is **not yet wired** to the old `ConditionSBEE.partition_bound` (`SBEE.lean`) or to
`erdos_306`. The full Erdős 306 proof still needs:

1. **Block-to-global chain** (CP 03 §§5–8): cross-block label mismatch → Peierls
   collapse → ordinary diagonal counting → **global control partition** (Prop 8.1).
   These take the single-block bound to the global minor-arc bound. (In the old
   `SBEE.lean` these were the *laundered* theorems; they are markdown, unformalized.)
2. **Circle method** (CP 01): edge construction (audited ✓, note 24) + Fourier
   inversion on `ZMod L` + Gaussian main arc + minor arc (from Prop 8.1) →
   `ℙ(Y=L/b)>0` → `fourier_positivity_unconditional`.
3. **Connection**: `SBEEPartitionBound` ⇒ (1) ⇒ (2) ⇒ `fourier_positivity_unconditional`
   ⇒ `erdos_306` (`reduction_to_unit_numerator_avoiding`, already proved).

So: a major, hard, previously-open piece is done and machine-checked; the
remaining work is the block-to-global chain + circle method + wiring — more
standard, with markdown proofs in CP 01 / CP 03 to follow.

## 4. Process update (per the user's feedback)

Aristotle is strong (it built Theorem B bottom-up over ~13h). But it is **faster
when translating a detailed proof than when rediscovering one**: Theorem C, which
I decomposed into explicit sub-lemmas with full proofs ([[32 Theorem C Decomposition - Phase Identity and Cold Rigidity]]),
went smoothly; Theorem B, given less detail, took far longer. **Adopted policy for
the remaining chain: I write the proofs in Lean-friendly detail (explicit lemma
statements + proof steps + ALL hypotheses) so Aristotle translates, not proves.**

## 5. Next

Scope and then **write detailed proofs** for the block-to-global chain (CP 03
§§5–8) — start with the cross-block label mismatch and the global control
partition (Prop 8.1), the inputs to the minor arc. Then the circle-method layer
(CP 01, edge construction audited). Each handed to Aristotle as a translation
task, not a discovery task.
