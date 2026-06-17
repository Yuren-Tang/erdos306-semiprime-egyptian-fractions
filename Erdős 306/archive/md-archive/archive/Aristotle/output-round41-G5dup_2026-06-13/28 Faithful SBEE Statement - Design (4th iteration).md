# Faithful SBEE Statement: Design (4th iteration)

Back to [[00 README]]. The SBEE encoding has now failed faithfulness **four**
times. This note stops the iterative patching and **designs the faithful
statement in full**, so the next Aristotle round formalizes a correct target
rather than discovering the next flaw.

## 1. The four faithfulness failures (history)

1. **Abstract `BlockEnergyData`** (no CRT structure) → trivial proofs
   ([[27 F2a Took Shortcuts - Faithful Encoding Required]] §1).
2. **F2a': per-block `∃C`** in `SBEESavingBound P c := ∃C, blockPartFun ≤ C/σ` →
   vacuous (any single block satisfies it); I wrongly called it faithful
   (note 27 §4b/§4c).
3. **F2a''': uniform `C`** fixed (2), but the case theorems take the **labeling
   `bl` as a free `∀`-parameter** while `blockPartFun` does **not** depend on `bl`.
   Instantiating `bl ≡ 0` (which makes label `0` dominant) collapses
   `dominant_case_uniform` to the **unconditional** uniform bound
   `∀P, ∑exp(-cQP) ≤ C/σ` — which is **false** for structured blocks. So the
   F2a''' case theorems are not vacuous but **too strong (false / unprovable)**.
4. Underlying both 2–3: **my task specs were incomplete** (didn't pin the
   quantifier, the pruning hypothesis, or that the statement must not contain a
   free labeling).

**Meta-lesson:** faithfully *stating* CP 02's single-block counting is itself a
multi-round design problem; the difficulty is not only proving SBEE but encoding
it. My faithfulness specs/reviews are fallible and must be done to the
quantifier-and-hypothesis level, by me, before handing off.

## 2. What CP 02 §4 actually says (the faithful content)

**Conditional single-block counting.** For every $\varepsilon>0$, after
Irving-good pruning, every block $P\subset[X,2X]$ satisfies
$$
\#\{a_P:\ Q_P(a_P)\le R\}\ \ll_\varepsilon\ e^{\varepsilon R}\Big(1+\tfrac{\sqrt R}{\sigma_P}\Big)\quad\text{uniformly for }R\ge1,
$$
with each low-energy $a$ encoded by **one ordinary label** $m$, $|m|\ll\sqrt
R/\sigma_P$ (the label is **determined by the assignment's energy**, *not* a free
parameter), plus an exception set paid by energy.

Two non-negotiables this forces:
* **Pruning/dispersion hypothesis on $P$** (structured blocks are excluded — they
  genuinely violate the bound).
* **No free labeling in the statement** — the label is internal to the proof; the
  statement is purely about the energy level-set count (or its partition-function
  Laplace transform).

## 3. The faithful Lean statement (design)

Use the partition-function form (equivalent by Laplace; it is what the circle
method consumes in CP 01 §6), with a **single uniform constant** and a **pruning
hypothesis**, and **no labeling**:

```
/-- Irving-good pruning hypothesis: phase dispersion of the block. -/
def IrvingGood (P : Finset ℕ) : Prop := …   -- ∀ nonzero h, ∑_{p∈P} ‖h·p̄/q‖² ≥ c·|P|, faithfully

def SBEEPartitionBound (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p),
      IrvingGood P → 2 ≤ P.card →
      blockPartFun P hP c ≤ C / sigmaP P
```

* `C` outside all `∀` (uniform) — fixes failure 2.
* `IrvingGood P` hypothesis — fixes failure 3 (structured blocks excluded), so the
  statement is **true**, not too strong.
* **No `bl`/labeling in the statement** — fixes the collapse; the dominant / tiny /
  non-dominant split is **internal proof structure**, realized as `have`-cases or
  private lemmas, never as the statement's hypotheses.

The dominant/tiny/non-dominant become **proof cases** of the single
`SBEEPartitionBound`, where the label $m$ is *constructed* from the assignment
(the nearest ordinary label), not quantified.

### Level-set variant (if the partition form is awkward)
```
def SBEELevelSet : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
    ∀ P hP, IrvingGood P → 2 ≤ P.card → ∀ R : ℝ, 1 ≤ R →
      ((Finset.univ.filter (fun a => QP P a ≤ R)).card : ℝ)
        ≤ Cε * Real.exp (ε * R) * (1 + Real.sqrt R / sigmaP P)
```
This is the most literal transcription of CP 02 §4.

## 4. Open design sub-point: encoding `IrvingGood`

`IrvingGood P` must faithfully encode the dispersion from CP 03 §2 (the pruned
block has $\sum_{p}\|h\bar p/q\|^2\gg|P|$ for all nonzero $h$). This references a
companion block $Q$ (the $q$'s), so the faithful form may be
`IrvingGood P Q : Prop`. Getting this right is itself part of the design (it must
be a real dispersion property, not `True`). It connects to `IrvingKloostermanBound'`
(the external input that yields the pruning).

## 5. Action

Replace the F2a''' free-labeling case theorems with the single faithful
`SBEEPartitionBound` (and `IrvingGood`), with dominant/tiny/non-dominant as
**internal** proof cases (honest sorries). **I (not Aristotle) own the statement
design**; Aristotle formalizes against it. This is task **F2a⁴** in the delivery
`TASK.md`. Only once the statement is faithful (uniform C, pruning hypothesis, no
free labeling, label energy-determined) does proving it (dominant/tiny standard;
non-dominant = FIE core) become meaningful.

## 6. Honest trajectory note

Four faithfulness iterations on one condition is slow, and reflects that the hard
part right now is *stating* SBEE correctly in Lean. This is not evidence the
mathematical route is wrong, but it is a real cost, and it means: **no Aristotle
round should be dispatched until I have fully pinned the statement** (quantifiers,
hypotheses, no proof-structure leaking into the statement). That discipline is the
fix for the repeated flaws.
