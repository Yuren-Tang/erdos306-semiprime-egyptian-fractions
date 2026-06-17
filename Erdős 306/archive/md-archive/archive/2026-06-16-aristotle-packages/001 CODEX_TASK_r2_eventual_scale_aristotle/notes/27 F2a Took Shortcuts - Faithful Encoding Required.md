# F2a Took Shortcuts: Faithful Encoding Required

Back to [[00 README]]. Audit of the F2a output (`SingleBlockCounting.lean`,
integrated 2026-06-09). **The "shortcuts" are real**: F2a does not faithfully
formalize the single-block counting skeleton. This note diagnoses it and
specifies the faithful encoding that must precede F2b.

## 1. The shortcuts (what F2a actually proved)

* `tiny_case_bound : fullPartitionFun ≤ bl.assignments.card` — the **trivial**
  bound (each $e^{-cE}\le1$, sum $\le$ count). The real SBEE tiny-case bound is the
  *saving* $\ll e^{\varepsilon R}(1+\sqrt R/\sigma_P)$. Since `assignments` is (meant
  to be) the full CRT space ($\prod_{p}p$ elements), $N\gg 1/\sigma_P$, so the
  trivial bound is **useless** against the target $C/\sqrt{\text{variance}}$.
* `dominant_case_bound : fullPF ≤ classPF(m) + ρ·N` — bounds the non-dominant
  remainder by $\rho N$ (again each term $\le1$), **not** by the Irving
  majority-correction saving $\gg|P|$; and `classPF(m)` is left unbounded.
* `single_block_counting_assembled` — **laundering**: its proof uses
  `tiny_case_bound` plus the *hypothesis* `htiny_bound : N ≤ C/√variance`, which is
  **false in reality** ($N\gg1/\sigma$); the dominant hypothesis `_hdom_sbee` is
  unused. So the theorem is vacuous w.r.t. real SBEE.
* `conditionSBEE_of_partition_and_fourier` — honest packaging, but takes the real
  partition bound as a hypothesis (does not provide it).
* `sbee_nondominant` (sorry) — **honest** target, but stated against the coarse
  `B.energy`/`B.variance` (see §2), so it is not yet faithfully connectable to the
  cluster machinery.

## 2. Root cause: the SBEE encoding is too coarse

`SBEE.lean`'s `BlockEnergyData` carries an **abstract** `energy : (ℕ→ℤ)→ℝ` and a
single `variance : ℝ`, and `ConditionSBEE.partition_bound` is
$\sum_a e^{-c\,\text{energy}(a)}\le C/\sqrt{\text{variance}}$ with **no $R$, no
$\sigma_P$ structure, no CRT energy $Q_P$, no prime/label structure.** Against such
a coarse type, "prove the easy cases" collapses to trivial bounds, and the cluster
machinery (which lives on primes/CRT residues) **cannot be connected** to
`B.energy`. So:

> **F2b is impossible to attempt faithfully against the current encoding.** The
> formalization is not yet testing real SBEE.

(Partly my task-spec's fault: F2a's spec did not pin the *saving* form of the case
bounds. Lesson: task specs must fix faithful statements.)

## 3. The faithful encoding (F2a' — the real next step)

Re-encode the single-block objects to match CP 02 §1 / CP 03:

* **Block** `P : Finset ℕ` of primes; **assignment space** `a ∈ ∀ p ∈ P, ZMod p`
  (the CRT space), *not* an abstract `Finset (ℕ→ℤ)`.
* **CRT representative** `H p q a : ℤ` (symmetric rep with `H ≡ a_p (p)`,
  `H ≡ a_q (q)`); **energy** `Q_P a = ∑_{p<q∈P} (H p q a / (p*q))^2`;
  `σ_P^2 = ∑_{p<q} 1/(p*q)^2`.
* **Level-set / partition** the real targets:
  $\#\{a:Q_P(a)\le R\}\ll_\varepsilon e^{\varepsilon R}(1+\sqrt R/\sigma_P)$, or
  equivalently $\sum_a e^{-cQ_P(a)}\ll 1/\sigma_P$.
* With this, the trivial bound $\sum e^{-cQ}\le\#\text{assignments}=\prod_p p$ is
  useless, so the dominant case **must** use Irving majority correction and the
  tiny case **must** use the $R$-large argument — no shortcut survives.

Then:
* **Dominant case**: genuinely prove the remainder saving via majority correction
  (exception entropy $O(\log X)$ paid by energy).
* **Tiny case**: genuinely prove that a large short-list forces $R$ large enough.
* **`sbee_nondominant`**: restate against $Q_P,\sigma_P$ so the cluster machinery
  (`good_kSubset_exists_unconditional`) and `cross_label_divisor_energy` actually
  plug in — *this* is the faithful F2b target.

## 4. Signs / how to read this

* **Yellow flag, not red.** This is a *formalization-faithfulness* problem, not
  evidence the mathematical route is wrong. The markdown (CP 01–03) states SBEE
  faithfully; the Lean encoding was too abstract and let trivial proofs through.
* It **does** mean: the earlier "Lean core is no-sorry / interfaces closed"
  reassurances must be read with faithfulness in mind — a no-sorry Lean theorem
  against a coarse encoding can be vacuous (exactly what [[20 Lean Core Audit and Dependency Map]]
  found for SBEE's laundered lemmas, and now again for F2a's easy cases).
* The reliable path is unchanged but **the bar is higher**: faithful encoding
  first, then the case proofs, then F2b. F2b against a faithful encoding is the
  real decisive test ([[26 F2 Is the Test - Strategy and Decomposition]]).

## 4b. F2a' DONE — encoding verified faithful (2026-06-09)

Aristotle produced `BlockCRTEnergy.lean` (~2 h). I verified the **definitions are
genuinely faithful** (no shortcut in the encoding):
* `BlockAssignment P = ∀ p:P, ZMod p` (CRT space, $\prod p$ elements);
* `crtRepr` via `ZMod.chineseRemainder`, centered in $(-pq/2,pq/2]$ — the real $H$;
* `QP = ∑_{pairs}(crtRepr/(pq))^2`, `sigmaP = √(∑ 1/(pq)^2)`;
* `blockPartFun = ∑_a exp(-c·QP a)`; `SBEESavingBound = ∃C>0, blockPartFun ≤ C/sigmaP`.

Because the sum has $\prod p$ terms, the trivial bound $\le\prod p$ is useless, so a
proof must exhibit a genuine saving — **the shortcut is structurally impossible now.**
The four remaining sorries (`dominant_case_saving`, `tiny_case_saving`,
`sbee_nondominant'`, `single_block_counting_faithful`) are **honest, faithful
targets**. The old laundering `single_block_counting_assembled` was removed.

**Reading:** that Aristotle (after ~2 h) left even dominant/tiny as sorries is the
*correct* outcome — against the faithful encoding these need real proofs (Irving
majority correction; $R$-large), which auto-formalization can't supply.

## 4c. CORRECTION — my §4b "verified faithful" was WRONG (the bound is still vacuous)

In the F2a'' round Aristotle proved `dominant_case_saving`, `tiny_case_saving`,
and the assembly — and **flagged, honestly, that they are vacuous**: the predicate
$$\texttt{SBEESavingBound } P\ c := \exists C>0,\ \texttt{blockPartFun }P\,c\le C/\sigma_P$$
quantifies $C$ **existentially per block $P$**. For a fixed finite block,
`blockPartFun` is a fixed positive real and $\sigma_P>0$, so $\exists C$ is
**always** satisfiable ($C=\texttt{blockPartFun}\cdot\sigma_P+1$). So the predicate
does **not** enforce the *uniform* (block-independent) saving — the real content.

**I verified the energy/σ *definitions* in §4b but missed the *quantifier
structure* of the bound. My "shortcut structurally impossible" claim was wrong.**
This is the third faithfulness flaw (abstract types → per-block $C$); getting the
*statement* right is most of the battle, and my faithfulness review is fallible.
Aristotle catching and flagging it (no laundering) is the process working.

**The faithful fix (computation-checked).** Move $C$ outside the block:
$$\texttt{SBEEUniformSaving } c := \exists C>0,\ \forall\ (\text{large prime blocks})\ P,\ \sum_a e^{-c\,Q_P(a)}\le C/\sigma_P.$$
Sanity check (2 primes $\{p,q\}$): $\sum_a e^{-c(H/pq)^2}\approx pq\sqrt{\pi/c}=(1/\sigma_P)\sqrt{\pi/c}$,
so $C\approx\sqrt{\pi/c}$ depends only on $c$ — uniform $C$ is correct, non-vacuous
(for fixed $C$, "for all large $P$" is a real constraint), and true (= the SBEE
saving). With this, dominant/tiny become genuine theorems (needing dispersion) and
`sbee_nondominant'` the genuine FIE target. This is task **F2a'''**.

So the F2a'' "proofs" are sound but vacuous and must be redone against the uniform
predicate. Net value of the F2a'' round = **the flaw discovery**, not the proofs.

## 5. Next action

Run **F2a'** (faithful encoding + genuine dominant/tiny proofs + faithful
`sbee_nondominant`), not F2b. Spec is in `aristotle-delivery/TASK.md`. Keep F2a's
case-split scaffolding where reusable, but replace the trivial bounds and the
laundering assembly with the saving-form statements. Only after F2a' is faithful
does F2b (the FIE core) become a meaningful test.
