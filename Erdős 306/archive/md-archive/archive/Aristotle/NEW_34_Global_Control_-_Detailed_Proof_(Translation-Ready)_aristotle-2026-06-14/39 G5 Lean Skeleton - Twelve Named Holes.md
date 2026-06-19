# G5 Lean Skeleton — Twelve Named Holes

Back to [[00 README]]. Note [[38 G5-G7 Instantiation - Complete Proofs for Translation]]
gave the complete paper proof of G5; two direct monolithic attempts have timed
out. **Diagnosis: not a mathematical problem — a granularity problem.** A
several-hundred-line Lean proof cannot be built in one session, and when the
attempt dies nothing survives. The fix is the same one that closed Theorem C
(note 32): pre-commit the decomposition INTO THE FILE as named lemmas with
`sorry` bodies, then close holes one at a time. Every closed hole is durable.

**Workflow instruction (binding).** First paste the whole skeleton below into
`GlobalControl.lean` (before `global_levelset`), adjusting syntax/namespaces
until the file compiles WITH the sorries. Commit that state. Then close holes
in the listed order. Do NOT attempt `global_levelset` monolithically again;
its final proof is hole 12 (~40 lines given holes 1–11). If a hole resists,
leave its sorry and continue: later holes mostly don't depend on earlier ones
(the true dependencies are noted per hole).

Conventions: `ρ := 1/4` fixed. `c2, X0B` are obtained once from
`theorem_B_nondominant_forcing (1/4)` and carried as section parameters.
Syntax below is best-effort; **semantics is binding, syntax is yours**.

---

## §0. Setup definitions (no proof obligations)

```lean
namespace GlobalControl
open SBEEForcing SBEEAssembly GlobalPeierls

noncomputable section
variable (BS : BlockSystem)

/-- Per-block internal energy of a global assignment. -/
def blockEnergy (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  QP (BS.P k) (restrict BS a k)

/-- The cold/hot threshold `R_w(k) = c2·2^k/log³(2^k)` (Theorem-B floor). -/
def Rw (c2 : ℝ) (k : ℕ) : ℝ := c2 * 2 ^ k / (Real.log (2 ^ k)) ^ 3

/-- Hot block: internal energy at least the forcing floor. -/
def isHot (c2 : ℝ) (a : GlobalAssignment BS) (k : ℕ) : Prop :=
  Rw c2 k ≤ blockEnergy BS a k

instance (c2 a k) : Decidable (isHot BS c2 a k) := Classical.dec _

def hotSet (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Icc BS.k0 BS.K).filter (isHot BS c2 a)

/-- The dominant label of a block (0 if none).  Uniqueness is hole 1. -/
def coldLabel (a : GlobalAssignment BS) (k : ℕ) : ℤ :=
  if h : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)
  then h.choose else 0

/-- Mismatch boundary: two consecutive cold blocks with distinct labels. -/
def boundarySet (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Ico BS.k0 BS.K).filter (fun k =>
    ¬ isHot BS c2 a k ∧ ¬ isHot BS c2 a (k+1) ∧
    coldLabel BS a k ≠ coldLabel BS a (k+1))

/-- Integer energy shell of each block. -/
def shellVec (a : GlobalAssignment BS) (k : ℕ) : ℕ := ⌊blockEnergy BS a k⌋₊

/-- Segment starts determined by the DATA (H, B) alone (no `a`):
    cold blocks that open a maximal cold run. -/
def segStarts (H B : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc BS.k0 BS.K) \ H).filter
    (fun k => k = BS.k0 ∨ (k - 1) ∈ H ∨ (k - 1) ∈ B)

/-- The start of the segment containing a cold `k` (recursion downward). -/
def segStart (H B : Finset ℕ) : ℕ → ℕ
  | k => if k ≤ BS.k0 then BS.k0
         else if (k - 1) ∈ H ∨ (k - 1) ∈ B then k
         else segStart H B (k - 1)

/-- The exception-reduced boundary penalty floor `Π(k)`
    (`mismatch_penalty_with_exceptions` with `|E| ≤ e0`). -/
def Pifloor (e0 : ℝ) (k : ℕ) : ℝ :=
  (((BS.P (k+1)).card : ℝ) - e0 - 1) * (((BS.P k).card : ℝ) - e0) ^ 3 /
    (2 ^ 13 * ((2:ℝ) ^ k) ^ 2)

/-- Label range at a segment start (L3 + cold threshold; note 38 §3 L3c). -/
def labelRange (c2 : ℝ) (k : ℕ) : ℤ := ⌈(168:ℝ) * Real.sqrt c2 *
    ((2:ℝ) ^ k) ^ (3/2 : ℝ) / Real.sqrt (Real.log (2 ^ k))⌉
```

---

## §1. The twelve holes, in closing order

**Hole 1 — `coldLabel_unique`.** If `IsDominant (2^k) (BS.P k) (restrict BS a k) (1/4)`
then `coldLabel BS a k` is THE label: any `m` with the size+class property
equals it. One-liner from `dominant_label_unique` + `Exists.choose_spec`.
Also `coldLabel_spec`: the chosen label satisfies size+class. (No deps.)

**Hole 2 — `cold_isDominant`.** ∃ `k0min₂`, for `k0min₂ ≤ BS.k0`,
`k ∈ Icc BS.k0 BS.K`, `¬ isHot BS c2 a k`, `1 ≤ blockEnergy ∨ True`:
`IsDominant (2^k) (BS.P k) (restrict BS a k) (1/4)`. Contrapositive of
`theorem_B_nondominant_forcing` via `BS.irvingGood`-style window/density
(blocks have `X = 2^k`, density `BS.hdensity`). (No deps.)

**Hole 3 — budget lemmas.** For `Qctrl BS a ≤ R`:
* `sum_blockEnergy_le : ∑ k ∈ Icc BS.k0 BS.K, blockEnergy BS a k ≤ R` and
  `sum_shellVec_le : ∑ k, (shellVec a k : ℝ) ≤ R` — from `energy_splits`
  (drop the bipartite sum) and `Nat.floor_le`.
* `sum_Rw_hot_le : ∑ k ∈ hotSet, Rw c2 k ≤ R` — each hot `Rw ≤ blockEnergy`.
* `sum_Pi_boundary_le : ∑ k ∈ boundarySet, Pifloor e0 k ≤ R` — for
  `k ∈ boundarySet`, both blocks cold ⟹ dominant (hole 2) with labels =
  `coldLabel` (hole 1); apply `mismatch_penalty_with_exceptions` with
  `E = exception sets` (`cold_exception_bound` gives `|E| ≤ e0`;
  `cold_label_size` gives the `hm`-hypotheses); the bipartite pair sets are
  disjoint across `k` (proved inside `energy_splits`), so the penalties sum
  inside `Qctrl ≤ R`. *(Heaviest hole of the support kind; deps: 1, 2.)*

**Hole 4 — `segStart` facts.** Pure ℕ-recursion, no `a`:
`segStart_mem : k ∈ Icc BS.k0 BS.K \ H → segStart H B k ∈ segStarts BS H B`;
`segStart_le : segStart H B k ≤ k`;
`segStart_run : ∀ j, segStart H B k ≤ j → j ≤ k → j ∉ H ∧ (j < k → j ∉ B)`
(every block in the run is cold-by-data and no internal edge is in `B`).
Induction on `k` unfolding the recursion. (No deps.)

**Hole 5 — `coldLabel_eq_segStart`.** With `H = hotSet c2 a`,
`B = boundarySet c2 a`, `k` cold:
`coldLabel BS a k = coldLabel BS a (segStart H B k)`.
By `GlobalPeierls.segment_label_constant` applied to
`label := coldLabel BS a`, `P j := (j ∉ H ∧ j+1 ∉ H ∧ j ∉ B)` over the run
(hole 4 gives the run; the definition of `boundarySet` gives label equality
across non-boundary cold edges). (Deps: 4.)

**Hole 6 — `cover_subset`.** The levelset injects into the data product:
```lean
{a | Qctrl BS a ≤ R} ⊆ ⋃ (H ∈ adm-H) (B ∈ adm-B) (v ∈ adm-shells)
    (ℓ ∈ (segStarts BS H B).pi (fun k => Finset.Icc (-(labelRange c2 k)) (labelRange c2 k))),
  fiber H B v ℓ
where fiber H B v ℓ :=
  {a | ∀ k ∈ Icc BS.k0 BS.K,
        blockEnergy BS a k ≤ v k + 1 ∧
        (k ∉ H → (1 - 1/4) * N_k ≤ classCount k (ℓ (segStart H B k)))}
```
(Formulate with `Finset.biUnion`; admissibility = the hole-3 budgets;
the label of each cold block is in the range Finset by `cold_label_size`
at the segment-start block + hole 5.) Membership: take `H/B/v/ℓ` to be the
invariants of `a`. (Deps: 1,2,3,4,5.)

**Hole 7 — `fiber_card_le`.** For fixed data,
`fiber.card ≤ ∏ k, (per-block count)` via `restrict_filter_card_le` (D4),
with `Φ k b := QP b ≤ v k + 1 ∧ (k ∉ H → class …)`. One application + a
`filter` reshuffle. (No deps beyond defs.)

**Hole 8 — `hot_factor` (numeric).** ∃ `k0min₈`, for `k0 ≥ k0min₈`,
`k ∈ Icc`, `n+1 ≥ Rw c2 k`, `n ≤ R ≤ Rtriv BS eps` (see hole 11):
`#{b : QP b ≤ n+1} ≤ exp (2*eps*(n+1))`. From `unified_levelset` + the (\*)
comparison `log C_ε + (k+1) + log(k+1) + ½·log(n+1) ≤ eps·Rw c2 k`
(note 38 §5 table row "hot"; `sigmaP_lower` for `1/σ_k`). (No deps.)

**Hole 9 — `cold_factor`.** For `k ∈ Icc`, label `|m| ≤ labelRange c2 (segStart …)`,
`X = 2^k ≥ X0(L5)`: `#{b : QP b ≤ n+1, class m} ≤ exp (eps*(n+1))`.
`fixed_label_count` + the monotonicity `labelRange c2 k† ≤ N_k·2^k/16` for
`k† ≤ k` (same computation as `cold_label_size`, lavish constants). (No deps.)

**Hole 10 — label-range factors (numeric).**
* `label_initial : 2·labelRange c2 BS.k0 + 1 ≤ c_init·BS.k0·(1 + Real.sqrt R / sigmaCtrl BS)`
  using `sigmaCtrl_le_sigmaP_k0` (S3) and `√(Rw) /σ_{k0} ≲ √R/σ_{k0}`.
* `label_noninitial : k† ∈ segStarts, k† ≠ BS.k0 ⟹
  (2·labelRange c2 k† + 1 : ℝ) ≤ exp (eps * w (k†-1))` where `w = Rw c2` if
  `k†-1 ∈ H`, `w = Pifloor e0` if `k†-1 ∈ B` — the (\*) comparison
  `(3/2)k† + ½log log + C ≤ eps·min(Rw, Π)(k†−1)`, valid for `k0 ≥ k0min₁₀`.
  (No deps.)

**Hole 11 — `trivial_regime`.** `Rtriv BS eps := eps⁻¹ * 2^(BS.K+2) * (BS.K+1)`;
for `R ≥ Rtriv`: `(#all assignments : ℝ) ≤ exp (eps*R)` — count
`∏ p ≤ exp(∑_k N_k (k+1) log 2)`, `N_k ≤ 2^k` (interval card). Also the cap
`R ≤ Rtriv ⟹ Real.log R ≤ 4*BS.k0 + log(1/eps) + 2` used by holes 8/10
under `admissibleGlobalRange`. (No deps.)

**Hole 12 — assembly = `global_levelset`.** Chain (note 38 §5 step 5 with the
merged label payment):
```
N(R) ≤ Σ_{H,B,v,ℓ} fiber.card                       (holes 6)
     ≤ Σ_{H,B} [labelProd(H,B)] · Σ_v ∏_k c k (v k)  (hole 7, separate v from ℓ)
     ≤ Σ_{H,B} labelProd · e^{3εR}·e^{A₂·nB}          (shell_sum_bound, α=2ε β=ε; holes 8,9)
     ≤ c_init·k0·(1+√R/σctrl) · [Σ_H ∏_{k∈H} e^{εRw}]·[Σ_B ∏ e^{εΠ}] · …  (hole 10)
     ≤ … e^{2εR}·e^{nB} each                          (weighted_subset_entropy, eps'=4ε)
     ≤ e^{A·nB}·e^{8εR}·(1+√R/σctrl)                  (k0 ≤ e^{nB} by 2k0 ≤ K)
```
plus the `R ≥ Rtriv` branch (hole 11). Budget: 2ε+2ε+3ε = 7ε ≤ 8ε. (Deps: all.)

---

## §2. Per-hole effort estimate

Holes 1, 4, 7: small (≤ 30 lines each). Holes 2, 5, 9, 11: medium. Holes 3, 8,
10: medium-numeric (threshold chases — the `theoremB_logthreshold` pattern).
Hole 6: medium (set-theoretic bookkeeping). Hole 12: the visible assembly,
~40–60 lines once 1–11 stand. **Each hole individually is no harder than
things already proved in this project** (hole 3 ≈ `mismatch_penalty` assembly;
hole 8 ≈ `theoremA_entropy`; hole 12 ≈ `unified_levelset` assembly).
