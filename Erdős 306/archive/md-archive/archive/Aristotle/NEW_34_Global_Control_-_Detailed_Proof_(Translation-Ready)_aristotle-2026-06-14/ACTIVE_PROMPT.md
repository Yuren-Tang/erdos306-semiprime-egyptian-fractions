# ACTIVE TASK: prove the G6 localization dichotomy (`g6_localization`)

## Startup — DO NOT rebuild the verified core (it is pre-built here)
The compiled `.olean` files for ALL of RequestProject are already laid out under
`.lake/build/lib/lean/RequestProject/` and match the source exactly. After
`lake exe cache get` (Mathlib only), run `lake build` — it should SKIP the whole
verified core and elaborate only your new file. Do NOT delete `.lake`. If you
flatten sources to the repo root, move them back under `RequestProject/` first
(the lakefile expects `RequestProject/*`).

## File-split strategy (keep it — it is why iteration is fast)
Work ONLY in a NEW leaf `RequestProject/GlobalControlG6.lean` that
`import RequestProject.GlobalControl`. Do NOT edit `GlobalControl.lean`,
`GlobalControlG7.lean`, `GlobalControlG5Assembly.lean`, or `CircleMethod.lean`
(those are driven separately and the G7 file already contains the assembly that
consumes your result). Build with `lake build RequestProject.GlobalControlG6`.

## Task
Prove the G6 localization dichotomy, fully decomposed (L1–L5) with
translation-ready proofs in **note `43 G6 Localization - Translation-Ready
Decomposition.md`** (read it fully). The target theorem (give it this exact
signature, namespace `GlobalControl`, in your new file):

```lean
def globalControlFloor (BS : BlockSystem) (c2 e0 : ℝ) : ℝ :=
  min (Rw c2 BS.k0) (Pifloor BS e0 BS.k0)

def diagSector (BS : BlockSystem) (C : ℝ) (a : GlobalAssignment BS) : Prop :=
  ∃ m : ℤ,
    (∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (m : ZMod p.1)) ∧
    C / sigmaCtrl BS < |(m : ℝ)| ∧
    Qctrl BS a = (m : ℝ) ^ 2 * (sigmaCtrl BS) ^ 2

theorem g6_localization :
    ∃ (k0loc : ℕ) (c2 e0 : ℝ), 0 < c2 ∧ 0 < e0 ∧
      ∀ (BS : BlockSystem), k0loc ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ a : GlobalAssignment BS, a ∉ mainArc BS C →
        globalControlFloor BS c2 e0 ≤ Qctrl BS a ∨ diagSector BS C a
```

(These `globalControlFloor`/`diagSector` defs are byte-identical to the ones in
`GlobalControlG7.lean`; redeclaring them in your namespace is expected — keep the
bodies identical so the G7 assembly can use yours.)

## Order of work (note 43)
1. `crtRepr_eq_label_of_small` — small CRT centered-rep lemma (L5 core).
2. `Rw_mono` (needs `4 ≤ k0`) — analytic monotonicity (L1). **A verified proof of
   the single step is given below — paste it, then induct.**
3. `Pifloor_mono` / `min(Rw k0, Pifloor k0) ≤ Pifloor e0 k` — density + super-linear (L2).
4. `cold_no_exceptions` — **the one substantive new step** (L3): in the no-hot/
   no-boundary case every cold block has empty exception set, because an exception
   prime carries block energy `≥ Rw c2 k` (reuse Theorem-A §3 (A3) per-exception
   energy via `dispersion_energy_bound`), contradicting `¬ isHot`.
5. Assemble L1–L5 into `g6_localization`.

If `cold_no_exceptions` resists full formalization, isolate IT as the single named
`sorry` and close everything else (L1/L2/L4/L5 + the assembly skeleton) — that is
still major progress and the precise diagnostic.

## Verified `Rw_mono` single step (paste directly — already machine-checked here)
```lean
lemma Rw_mono_step (c2 : ℝ) (hc2 : 0 < c2) (k : ℕ) (hk : 4 ≤ k) :
    Rw c2 k ≤ Rw c2 (k+1) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hcube : ((k:ℝ)+1)^3 ≤ 2 * (k:ℝ)^3 := by
    nlinarith [hkR, mul_nonneg (show (0:ℝ) ≤ (k:ℝ)-4 by linarith) (sq_nonneg (k:ℝ)),
      mul_nonneg (show (0:ℝ) ≤ (k:ℝ) by linarith) (show (0:ℝ) ≤ (k:ℝ)-3 by linarith)]
  have hrw : ∀ j:ℕ, 1 ≤ j → Rw c2 j = (c2/(Real.log 2)^3) * ((2:ℝ)^j/(j:ℝ)^3) := by
    intro j hj
    have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
    unfold Rw; rw [Real.log_pow, mul_pow]; field_simp
  have key : (2:ℝ)^k / (k:ℝ)^3 ≤ (2:ℝ)^(k+1) / ((k:ℝ)+1)^3 := by
    have hps : (2:ℝ)^(k+1) = 2 * 2^k := by rw [pow_succ]; ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcube (pow_pos (show (0:ℝ)<2 by norm_num) k).le, hps]
  rw [hrw k (by omega), hrw (k+1) (by omega)]
  push_cast
  exact mul_le_mul_of_nonneg_left key (by positivity)
```
Then `Rw_mono : 4 ≤ k0 → k0 ≤ k → Rw c2 k0 ≤ Rw c2 k` by `Nat.le_induction` on `k`
from `k0`, each step `Rw_mono_step` (note `k ≥ k0 ≥ 4`).

## Available verified machinery to reuse
`energy_splits`, `QP_restrict_eq_internal`, `boundary_penalty_per_k`,
`cold_isDominant`, `cold_exceptions_small`, `cold_block_facts`,
`coldLabel`/`coldLabel_eq`, `segment_label_constant`
(`GlobalPeierlsBookkeeping`), `crtRepr`/`crtRepr_congr` (`CRTLatticeCore`),
`dispersion_energy_bound` (`SBEEDispersion`), `pow_beats_poly_log`
(`GlobalControlG5Assembly`). Keep every hypothesis faithful; report which
sub-lemmas closed and the residual sorry pattern.
