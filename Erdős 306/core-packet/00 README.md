# Erdős 306 Core Packet

This is the current working entry point for the project.

The old folders remain available as archive/reference:

- `../conditional proof/`
- `../草稿區/`
- `../Aristotle/output-final_aristotle_*/`
- `../archive/`

Do not start from those folders unless a specific detail is needed. Start here.

## Current status (updated)

Erdős 306 is **not proved**, but the project has advanced from "open analytic
mystery" to a concrete, partly machine-verified program. The entry point for the
live work is now the SBEE notes **29–32**, not the older 02–19 (which trace how we
got here; superseded where they conflict with 29+).

State of the **SBEE single-block counting condition** (CP 02's "single remaining
condition" of the conditional proof):

* A complete elementary paper proof exists (notes **29**, **30**), built on a
  **deterministic dispersion lemma** (Lemma D) — no Irving/Kloosterman/Fourier at
  the block level (a real simplification of the original route).
* **MACHINE-VERIFIED (sorry-free, 2026-06-09): ALL of SBEE single-block counting**
  — `single_block_counting : SBEEPartitionBound c` (`SBEEAssembly.lean`), resting on
  the dispersion engine, Theorems A/B/C, and Lemma E. This is CP 02's "single
  remaining condition", proved elementarily. See note **33**.

Beyond SBEE: the block-to-global chain is **proved on paper** (note 34, no Irving
anywhere), and the circle method is spec'd with computations (note 35). The
latest Aristotle recovery package has machine-verified the faithful finite
global-assignment interface, G2, G3, and the exceptional G3 corollary; the honest
remaining Lean targets are now **G5**, **G7**, and **Phase C**
(`CircleMethod.exists_positive_weighted_construction`). Note **37** is the current
formalization blueprint, correcting the G5/G7 constant quantifiers and splitting
the remaining proof into abstract Peierls bookkeeping plus circle-method lemmas.
The earlier "rational-collision / Fourier positivity" framing (notes 02–16) was
the exploratory route; the SBEE route (29+) is the one being carried to machine
verification.

## Read order

1. [[01 Minimal Proof Spine]]
2. [[02 Active Rational-Collision Problem]]
3. [[03 Lean Formalization Map]]
4. [[04 Failure and Risk Ledger]]
5. [[05 Next Work Plan]]
6. [[06 Archive Map]]
7. [[07 Diagonal Ledger]] — Task 1 done: exact reduced sum $N_H'$
8. [[08 Anchor Energy and the Joint Obstruction]] — Task 2 done; C–S fails; Task 4 framed
9. [[09 Cluster Concentration and the Structured Family]] — Lemmas B, C; structured family made explicit; Task 4 reduced to one counting step
10. [[10 Kloosterman Reduction of the Correlation]] — main term recovered unconditionally; error = Irving's reciprocal prime sums in the good regime $x\asymp q$
11. [[11 Irving Toolbox and the Finish Roadmap]] — Irving's lemmas; why primes (not Weil) supply the spare power; average-over-seeds = SBEE averaging; step-by-step finish
12. [[12 M_B Computation and the Bilinear Necessity]] — explicit completion: clean main term $H^4/X^2$; cancellation must stay single-modulus; $M_B$ already needs the bilinear method
13. [[13 The Averaged Framing Is Essential]] — size computation kills the per-tuple bound; the theorem is an average-over-seeds statement (= SBEE's average = Irving's modulus average); needs Fouvry–Shparlinski explicit forms
14. [[14 Fouvry-Shparlinski Is the Template]] — FS study exactly $XY+XZ+YZ$ over primes; their Thm 1.2 + toolkit (Cayley congruence, Lemma 2.3 averaging, Thm 3.1, double sums) is the template; remaining work = adaptation, not invention. PDF in archive.
15. [[15 The Cube Structure from Cluster-Seed Averaging]] — averaging over cluster seeds turns $N_H'$ into a cube $\sum_p A_{04}(p)\sum_{x_4}g(p,x_4)^3$ (composite-modulus obstruction gone); §7: but the cube is *coupled* through $x_4$ (a frequency condition $\|q_4\sum b_j/q_j\|\lesssim1/H$), a genuinely new sub-problem beyond FS
16. [[16 Stratifying the Cube - Strata 0,1 Done]] — executed strata 0,1 on the frequency side (superseded by note 17's simpler spatial argument for the first moment)
17. [[17 The First Moment Is Trivial (Correction)]] — spatial side: a short form has ≤1 large prime factor, so the cluster-averaged first moment is trivially in budget; notes 14–16 unnecessary for it; structured family is log-thin by Markov
18. [[18 What SBEE Actually Needs (Synthesis)]] — read CP 02: it wants a per-(non-structured)-tuple dichotomy; structured side is power-thin ELEMENTARILY (CP 02 kernel count); regular side reduces to $|P_B|\ll(\log)^C$ (equidistribution, FS) — but needed only if the FIE seed-pool is small.
19. [[19 The Selection Closes Elementarily (Likely No FS)]] — read the cluster-cover machinery: the good-seed selection uses a SUMMED codegree incidence ledger + elementary cluster sizes ($\ll M_\tau$), closing with $\ge4$ seeds ($M_\tau^{k+1}\ll X^{k-1}$) — first-moment, elementary. **Likely no FS needed for the correlation endpoint; FS only in Irving-good pruning.** (Caveats: FIE entropy/$T_{aux}$ bookkeeping unverified.)
20. [[20 Lean Core Audit and Dependency Map]] — **authoritative Lean audit** (supersedes 03): one real sorry; `erdos_306` ⟸ that sorry cleanly; three disconnected components (main / SBEE-laundered / collision-infra); duplication + cleanup actions. Read this to know what's real vs assumed.
21. [[21 Cleanup Tasks for Aristotle]] — safe cleanup applied locally (honest docstrings/markers in SBEE & Erdos306Unconditional, orphan `SemiprimeReciprocals` deleted); rebuild-requiring tasks C1 (de-vacuize SBEE), C2 (factor CRT dup), C3 (connect/label Component C) packaged for Aristotle.
22. [[22 The Real Gap, Atomic Form]] — traced the whole SBEE/FIE route to its atomic endpoint: the **reciprocal-cluster selection lemma**. Hard input (global singular-tuple sparsity) is ELEMENTARY/proved with $k\ge4$ seeds; residual is finite hypergraph-cover packaging (large-intersection failure mode = small-determinant structure). The SBEE route's remaining math is combinatorial, not analytic.
23. [[23 Proof of the Reciprocal-Cluster Selection Lemma]] — **PROVES** the §22 atom: incidence ledger + cluster-size $\ll M_\tau$ + cluster-count $\ll XM_\tau$ ⇒ for $|F|\gg X^{1/2+\delta}$, $k>3/(2\delta)$ (e.g. $k=4$), $\binom{|F|}{k}>\#\mathcal C\binom{M_\tau}{k}$, so a good $k$-tuple (regular for ALL $p$) always exists. Elementary; no FS. Interface-checked (§6): matches the formalized `anchoredCluster`/pipeline, formalization-ready (§7).
24. [[24 End-to-End Core Map and How Close We Are]] — full chain `fourier_positivity` ⟸(circle method, STANDARD) ConditionSBEE ⟸(counting) ⟸(FIE) {cluster selection PROVED + descent + ledger}. **No research-level analytic gap left on this route; remaining = audit edge construction (DONE ✓) + entropy-descent algebra + formalization.** Circle method's only SBEE input = minor arc.
25. [[25 Closure Plan - Lean-Verified vs Markdown]] — **answers "didn't Lean audit this already?"**: Lean verified only the disconnected Component C + leaves; the load-bearing main chain (L1 circle method, edge construction, FIE descent, the connections) is **markdown-only**, hand-audited (fallible), NOT machine-checked. Closure = formalize the chain: F1 (done) → F2 (FIE⇒ConditionSBEE, decisive) → F3 (circle method) → F4 (connect).
26. [[26 F2 Is the Test - Strategy and Decomposition]] — **F2 is the crux test of the route.** If F2 formalizes clean ⇒ high confidence (F3 standard); if F2 needs an uncloseable sorry ⇒ that's the fundamental problem (deepest = ConditionSBEE false). Decomposed: F2a (skeleton) → F2b (non-dominant FIE core, decisive). F1/F1b done: cluster selection UNCONDITIONAL.
27. [[27 F2a Took Shortcuts - Faithful Encoding Required]] — **F2a trivialized** (proved `partitionFun ≤ N`); fixed by faithful CRT `QP`/`sigmaP` (F2a'). §4c: but F2a' bound `∃C per-block` was still **vacuous** — I wrongly called it faithful; Aristotle caught it. Fix = uniform C (F2a''').
28. [[28 Faithful SBEE Statement - Design (4th iteration)]] — **4th faithfulness failure**: F2a''' uniform-C still unfaithful (free labeling `∀bl` that `blockPartFun` ignores ⇒ `bl≡0` collapses to a FALSE unconditional bound). **I stop iterative patching and DESIGN the full faithful statement**: `SBEEPartitionBound = ∃C, ∀ pruned `IrvingGood` block P, blockPartFun ≤ C/σ` — uniform C, **pruning hypothesis**, **NO free labeling** (dominant/tiny/non-dom = internal proof cases, label energy-determined). Meta: stating SBEE faithfully is a multi-round design problem; my specs were incomplete each time; **no Aristotle round until I fully pin the statement.**
29. [[29 SBEE Master - Dominant Case Proved, Window Isolated]] — **mathematical center, part 1.** Full proofs: **Lemma D** (deterministic dispersion, no Kloosterman), **Theorem A** (dominant case: PROVED, elementary, no Irving), **Lemma E** (cross-label energy), **Theorem B** (non-dominant forces $R\gg X/\log^3X$). SBEE unconditional for all $R\le c'X/\log^3X$; window isolated.
35. [[35 Circle Method - Detailed Spec (Translation-Ready)]] — CP 01 deterministically restated: weighted count W, finite Fourier identity, Bernoulli bound (c=16/9, computed), main-arc Taylor (explicit errors), minor arc = G7, positivity ⟹ closes `fourier_positivity_unconditional`. One external input: Chebyshev block density.
37. [[37 Faithful G5 G7 C Formalization Blueprint]] — **current next-step blueprint** after Aristotle's latest recovery: finite global assignments + G2/G3/exceptions are done; G5/G7 must be restated with a uniform base constant `exp(A·#blocks)` and a growing `F0(k0)`/final `η` form; prove an abstract `GlobalPeierlsBookkeeping` layer first, then instantiate and split Phase C into C1a–C6.
36. [[36 Aristotle Append - G5 G7 C Proof]] — previous append prompt: detailed proof of finite assignment, exceptional G3, G5/G7, and Phase C. Superseded/refined by note 37 for the faithful constant quantifiers.
34. [[34 Global Control - Detailed Proof (Translation-Ready)]] — **the block-to-global chain (Prop 8.1) fully proved, NO Irving anywhere** (deterministic cross-dispersion G2 suffices: Peierls penalties Π_k≍4^k/k⁴ beat entropies ≍k doubly-exponentially, numerically verified). Theorem G (global level-set, segment/droplet encoding) + G7 partition form. Replaces CP 03 §§5–8 (no polymer expansion needed).
33. [[33 SBEE Machine-Verified - Milestone and Remaining Chain]] — **MILESTONE: SBEE single-block counting (CP 02's "single remaining condition") is fully machine-verified, sorry-free, faithful** (`single_block_counting : SBEEPartitionBound`). Elementary (deterministic dispersion, no Irving at block level). Remaining for Erdős 306: block-to-global chain (CP 03 §§5–8) + circle method (CP 01) + wiring to `erdos_306`. Process: write detailed proofs → Aristotle translates.
32. [[32 Theorem C Decomposition - Phase Identity and Cold Rigidity]] — decomposed Theorem C into 5 lemmas (phase identity, **cold rigidity = novel core**, injection, entropy). **V3+V4 RESULT: THEOREM C (`fingerprint_count`) FULLY MACHINE-VERIFIED, sorry-free** (`SBEEDispersion`+`SBEEFingerprint` clean; empty-block fixed via `1≤|P|`). So the dispersion engine + the whole novel counting core of SBEE are Lean-proved. Remaining for full SBEE: forcing layer A/E/B (`SBEEForcing.lean`, elementary energy estimates, note 29 §3/§5/§6) + assembly (`single_block_counting`). V5 = those.

31. [[31 V1 Verification Outcome and the Residue-Count Proof]] — **V1 formalization pass: faithfulness review PASSED (bodies checked), Lemma D MACHINE-VERIFIED.** Key: `IrvingGood` is correctly just dyadic-window+density (deterministic Lemma D removes all need for Irving pruning — note-28 pruning worry RESOLVED, simplifying). `phase`/`fingerprint_count`/`SBEEPartitionBound` all faithful. Substantive theorems (C,A,B) still sorry ⇒ SBEE not yet verified, but foundation solid + honest map. Full proof of `dispersion_residue_count` given (§4). Next (V2): close it → dispersion engine done → Theorem C.

30. [[30 Theorem C - The Window Counted, SBEE Assembled]] — **mathematical center, part 2 (CLAIMED PROOF of SBEE).** **Theorem C**: fingerprint argument counts the FULL level set for $R\ge C_\varepsilon X^{2/3}\log^{4/3}X$ — fixed fingerprint $F$ ($|F|=\varepsilon R/2\log2X$), cold vertices have a UNIQUE consistent residue (reciprocal dispersion ⇒ zero entropy), hot vertices $\le7R/G_F$ (polylog). A+B+C assemble into the full single-block counting theorem = **SBEE, all elementary, no Irving at block level**. The FIE difficulty dissolves via the $R$-dichotomy (rigidity below the window, fingerprint above). Status: claimed pending independent verification (adversarial checklist in §5; numerical bookkeeping verified; crossover $X_0\sim10^{35}$ crude). Remaining for Erdős 306: block-to-global chain (CP 03 §§5–8), circle method, formalization — Lean target = Lemma D + Thms A/B/C against note-28's faithful encoding.

## Aristotle delivery

`aristotle-delivery/` is the stable, self-contained upload bundle (Lean package +
`TASK.md` + latest notes). It has been refreshed to the latest recovery state:
faithful finite `GlobalAssignment`, G2/G3, and `mismatch_penalty_with_exceptions`
are in `GlobalControl.lean`; remaining named targets are G5, G7, and Phase C.
For the next Aristotle round, upload this folder and include note **37** as the
active instruction.

Lean-side work should use:

- [[lean/README]]

## One-sentence target

Prove that short rational-value collisions

$$
p
=
\frac{q_4z_4-q_0x_0}{y_4}
=
\frac{q_i x_i-q_4x_4}{a_i}
\qquad(1\le i\le3)
$$

occur only at the random scale, unless the seed primes lie in a low-height
structured family.
