# Aristotle task — finish the R2 arc construction (`exists_arcConstruction_final`)

**Mode: TRANSLATE, not explore.** The full proof route is given below with exact lemma names and
argument lists. Your job is to render it into compiling Lean 4 (Mathlib v4.28.0), handling the one
structural refactor (§A) that the current inline proof needs. Leave exactly ONE named `sorry`
(`hextraLight`, §D.6) — that is a separate math problem being handled elsewhere. Do NOT touch the 3
cited axioms (`dyadic_prime_density`, `dyadic_mertens_cumulative`,
`dyadic_control_recipLoad_eventually_small`) — keep them `axiom`.

File: `RequestProject/R2TopAssembly.lean`. Build: `lake env lean RequestProject/R2TopAssembly.lean`
(single file, ~70s, uses cached dep oleans). Green = no `error`, at most the one `sorry` warning.

## Current state (already fixed; do not redo)
`exists_arcConstruction_final` (~line 629) sets up all parameters and structural `have`s and ends at
`h2N1sigma` with the goal `Nonempty (ArcConstruction T b)` STILL OPEN. The `hsumE` /
`r2_extra_inv_sq_le` block, `hNsigma`, `h2N1sigma` are already fixed and correct. Two problems remain:
1. **3 `maximum recursion depth` errors** in the σ_E block (`hsumE`'s closing `nlinarith`,
   `hsigmaE2_le`, `hsigmaE_ub`) — see §A.
2. **The closing is unwritten** (goal open) — see §D.

## §A. The refactor (fixes the recursion — REQUIRED first)
**Cause.** In the theorem, `D, W, σ, N, C, Dmp, η` are introduced with `set` (let-bindings). `D`
holds `Q = Classical.choose (r2_getQ …)`, `σ = √(huge sum)`, `N = ⌈C/σ⌉`. Any `nlinarith`/`set`/
kernel `isDefEq` over a goal containing `sigmaE2 D.E W.theta` or `∑_{D.E} 1/e²` unfolds these and
recurses → stack blow-up. Bumping `maxRecDepth` does NOT work (8000 too low; 64000 makes elaboration
pass but the olean KERNEL check crashes with a stack-space exception).

**Fix.** Extract the analytic body into a standalone lemma whose `D W N σ` are ORDINARY parameters
(not `set`/let-bound), so they stay opaque atoms and nothing unfolds. Concretely create:

```lean
lemma r2_arcConstruction_of_assembled
    {T : Finset ℕ} {b : ℕ} (hb : 3 ≤ b) (hbsf : Squarefree b) (hbpos : 0 < b)
    (D : R2ConcreteData T b) (W : R2ConcreteData.Weights D) (N : ℤ)
    (C η Ctail Dmp : ℝ) (G : ℕ) (k0minM : ℕ)
    (QB : R2MassBatchSupply D)
    (hMR : ∀ (Ablock Aextra ρ Cextra : ℝ) (Cls : R2MinorClassificationData D W N),
        k0minM ≤ D.BS.k0 → admissibleGlobalRange D.BS →
        R2MinorEndgameFrequencyLanes D W N (Ablock / sigmaCtrl D.BS) (Aextra / sigmaCtrl D.BS)
          η Ctail ρ Cextra Cls →
        Ablock + Aextra < r2MinorMainCtrlConstant → Nonempty (R2MinorReadyData D W N))
    -- … all structural/numeric hypotheses below as EXPLICIT args (no `set`) …
    (hadm : admissibleGlobalRange D.BS) (hk0minM : k0minM ≤ D.BS.k0)
    (hk0 : 14 ≤ D.BS.k0) (hCge3 : (3:ℝ) ≤ C) (hηdef : η = r2MinorMainCtrlConstant / (2004 * b))
    (hDmpdef : Dmp = r2MinorMainCtrlConstant / (2004 * b * (2*C+3)))
    (hC0bd : (b:ℝ) * Ctail * Real.exp (-C^2 * (16/9) / 2) < r2MinorMainCtrlConstant / 2004)
    (hσstrong : (1:ℝ)/(100 * (D.BS.k0:ℝ) * 2^D.BS.k0) ≤ sigmaCtrl D.BS)
    (hNlo : C / sigmaCtrl D.BS ≤ (N:ℝ)) (hNnonneg : 0 ≤ N)
    (hEmin : ∀ e ∈ D.E, (2:ℝ)^(2*D.BS.k0) ≤ (e:ℝ)) (he0 : ∀ e ∈ D.E, 0 < e)
    (hsumE : ∑ e ∈ D.E, (1:ℝ)/(e:ℝ)^2 ≤ 1000001 * (sigmaCtrl D.BS)^2)
    (hsigmaE_lb : Real.sqrt (2/9) * sigmaCtrl D.BS ≤ Real.sqrt (sigmaE2 D.E W.theta))
    (hN2 : 2 * N < (2:ℤ)^(2*D.BS.k0)) (hNL : 2*N + 1 ≤ (D.L:ℤ))
    (hbuildLanes : Nonempty (R2MinorEndgameFrequencyLanes D W N
        ((b:ℝ)*(η + Ctail*Real.exp (-C^2*(16/9)/2))/sigmaCtrl D.BS)
        ((b:ℝ)*(2*(N:ℝ)+1)*Dmp) η Ctail (N:ℝ) Dmp (mainArcClassificationData D W N C)))
    (hextraLight : ∑ e ∈ D.E \ ctrlEdges D.BS, 1/(e:ℝ)^2 ≤ 3*(sigmaCtrl D.BS)^2) :
    Nonempty (ArcConstruction T b) := by
  …  -- §B + §C + §D below, all with D/W/σ opaque ⇒ no recursion
```
Then `exists_arcConstruction_final` keeps everything up to and including the structural `have`s,
builds `hbuildLanes` via `r2_buildFreqLanes` and `hMR`/`hsumE`/… , and finishes with one
`exact r2_arcConstruction_of_assembled …`. (You may split differently; the ONLY requirement is that
the `nlinarith`/numeric steps over `sigmaE2`/edge-sums run with `D` as an opaque parameter.)
Replace `sigmaCtrl D.BS` for `σ` throughout the extracted lemma (don't reintroduce a `set σ`).

## §B. The σ_E control facts (inside the extracted lemma, D opaque)
With `D` opaque these go through as Aristotle originally wrote them. The goals:
- `hsumE` already proved upstream (passed in).
- `hsigmaE2_le : sigmaE2 D.E W.theta ≤ 250001*(sigmaCtrl D.BS)^2` :=
  `by have h := sigmaE2_le_quarter_sum_inv_sq D.E W.theta; nlinarith [hsumE, h, sq_nonneg (sigmaCtrl D.BS)]`
- `hsigmaE_ub : Real.sqrt (sigmaE2 D.E W.theta) ≤ 501*sigmaCtrl D.BS` (sqrt monotone + hsigmaE2_le).
- `hsigmaEpos`, etc. (already in file, copy over).

## §C. The two large-`k0` domination facts
Reuse the exponential-beats-polynomial induction already in the file (`r2_getQ`, the
`2^BS.k0 > BS.k0^3 * 2` step via `Nat.le_induction` from `k0 ≥ 30`). You have
`hk0dom : 10^6 * (⌈C⌉₊ + 1)^4 ≤ D.BS.k0` available in the theorem (pass it in).
- `hexp : (D.BS.k0:ℝ)^3 * 2 < 2^D.BS.k0` (the induction; `30 ≤ k0` from `hk0dom`).
- `hNub : (N:ℝ) ≤ 100*C*(D.BS.k0:ℝ)*2^D.BS.k0 + 1` from `hNlo`→`hNhi`(`N ≤ C/σ+1`) and
  `1/σ ≤ 100 k0 2^k0` (from `hσstrong`).
- **`hN2 : 2*N < (2:ℤ)^(2*k0)`**: cast to ℝ, `2^{2k0} = 2^{k0}·2^{k0}`; from `hNub` and
  `200*C*k0 + 1 < 2^{k0}` (which follows from `hexp` + `C ≤ ⌈C⌉₊+1 ≤ k0` + `k0 ≥ 101`, all via
  `hk0dom`). Pattern: let `P = 2^{k0} ≥ 2`; `2N ≤ 200 C k0 P + 2 ≤ (200Ck0+1)P + P < P·P`.
- **`hNL : 2N+1 ≤ (D.L:ℤ)`**: first `(2:ℤ)^(2*k0) ≤ (D.L:ℤ)` (since `D.L = b·∏_{p∈blockSupport}p`
  and `∏ ≥ (2^{2k0})^{|S|} ≥ 2^{2k0}` because `S ⊆ blockSupport`, each `s ≥ 2^{2k0}`, `|S|=G ≥ 1`;
  use `Finset.prod_le_prod'`/`prod_le_prod_of_subset_of_one_le'`). Then `omega` with `hN2`
  (`2N < 2^{2k0} ≤ D.L` ⟹ `2N+1 ≤ D.L`, treating `2^{2k0}` as an opaque ℤ atom).

## §D. The closing assembly
Let `σ := sigmaCtrl D.BS` for readability (it is `D.BS`-based; do NOT `set`). All pieces below
are already-proven lemmas in scope.

1. **Frequency lanes** — `hbuildLanes` is built (in `exists_arcConstruction_final`) by
   `r2_buildFreqLanes D W N C η Ctail Dmp G hbpos hbsf hcovR hcopB (fun r hr => hRp r hr) hSprime
     hRdvd hSblock hlt' hctrlAvoid hgadgetAvoid heL he0 hL hLeq hCge1 hNnonneg hSge hScard hNlo
     hN2 hDmppos.le hG`. (All args are existing `have`s except `hN2` from §C.)
   `obtain ⟨Lanes⟩ := hbuildLanes`.
2. **Minor-ready data via `hMR`** — set
   `Ablock := (b:ℝ)*(η + Ctail*Real.exp (-C^2*(16/9)/2))`, `Aextra := (b:ℝ)*(2*(N:ℝ)+1)*Dmp*σ`.
   `obtain ⟨MR⟩ := hMR Ablock Aextra (N:ℝ) Dmp (mainArcClassificationData D W N C) hk0minM hadm ?lanes hbeat`.
   - `?lanes : R2MinorEndgameFrequencyLanes D W N (Ablock/σ) (Aextra/σ) η Ctail (N:ℝ) Dmp (mainArc…)`.
     `Ablock/σ` is syntactically the lanes' 1st param. `Aextra/σ = (b(2N+1)Dmp·σ)/σ` must be shown
     `= b(2N+1)Dmp` (the lanes' 2nd param): `convert Lanes using 2; field_simp` (σ ≠ 0).
   - **`hbeat : Ablock + Aextra < r2MinorMainCtrlConstant`** — the beat. Let `c3 := r2MinorMainCtrlConstant`.
     - `(b:ℝ)*η = c3/2004`  (from `hηdef`, `field_simp; ring`, `b ≠ 0`).
     - `(b:ℝ)*Ctail*Real.exp (-C^2*(16/9)/2) < c3/2004`  — note `Ablock = bη + b·Ctail·exp(…)`;
       use `hC0bd` directly (it already states `< c3/2004`; if `hC0bd` is at `C0` not `C`, monotone:
       `C ≥ C0 ⟹ exp(-C²·) ≤ exp(-C0²·)`, `Real.exp_le_exp`, `nlinarith` on the squares).
     - `Aextra = b·Dmp·((2N+1)σ) ≤ b·Dmp·(2C+3) = c3/2004`  (from `h2N1sigma : (2N+1)σ ≤ 2C+3`,
       `mul_le_mul_of_nonneg_left`, and `b·Dmp·(2C+3) = c3/2004` via `hDmpdef`, `field_simp; ring`).
     - Sum `< 3·c3/2004 < c3` by `linarith` (`c3 > 0`; `hc3pos`).
3. **Numeric fields** — `hNF : MainArcNumericFields D.E W.theta N :=`
   `r2_numericFields D W N (Emin := (2:ℝ)^(2*D.BS.k0)) (B := 1000001*(C+1)^2) (by positivity) he0
     (by positivity) hEmin hN hNnonneg h10N hsumsq hsmallN` where:
   - `hN : 1/√(sigmaE2 D.E W.theta) ≤ N` — from `hsigmaE_lb` (`√(sigmaE2) ≥ √(2/9)·σ > 0`) so
     `1/√sigmaE2 ≤ 1/(√(2/9)σ) ≤ C/σ ≤ N`; the middle uses `1 ≤ C·√(2/9)` (since `C ≥ 3` and
     `√(2/9) ≥ 1/3`: `nlinarith [Real.sq_sqrt (show (0:ℝ)≤2/9 by norm_num), Real.sqrt_nonneg _]`).
   - `h10N : 10*N ≤ (2:ℝ)^(2*k0)` — like `hN2`/§C, large-`k0`.
   - `hsumsq : (N:ℝ)^2 * (∑_{D.E} 1/e²) ≤ 1000001*(C+1)^2` — from `hsumE` and `hNsigma : Nσ ≤ C+1`:
     `N²·∑ ≤ N²·1000001σ² = 1000001·(Nσ)² ≤ 1000001(C+1)²` (use `sq_le_sq'`/`nlinarith`).
   - `hsmallN : (N:ℝ)/(2^{2k0}) ≤ 1/(10^6·1000001·(C+1)^2)` — large-`k0` (cross-multiply, then the
     same exp-beats-poly chase; `hk0dom` gives ample slack since RHS-denominator is `poly(C) ≤ poly(k0)`).
4. **Apply the endpoint.** `exists_arcConstruction_of_componentData_numeric_minor_window`
   (`R2FinalAssembly:356`):
   ```
   exact exists_arcConstruction_of_componentData_numeric_minor_window hb D W N MR.Bblock MR.Bextra
     hadm hNF hNL (QB.q_semiprime) (fun r hr => hRp r hr) hSprime hlt' hctrlAvoid QB.hQavoid
     hgadgetAvoid QB.hQne (QB.q_dvd_period) hRdvd hSblock QB.hloadDisj QB.hloadLower QB.hloadUpper
     (fun MA => ⟨MR.MB.Sblock MA, MR.MB.Sextra MA, MR.MB.hcover MA⟩)
     (fun MA => MR.MB.hblock MA) (fun MA => MR.MB.hextra MA) hextraLight MR.hminorCtrl
   ```
   - The minor cover `C MA := ⟨MR.MB.Sblock MA, MR.MB.Sextra MA, MR.MB.hcover MA⟩ : R2MinorCoverData MA.Sm`
     (fields `Sblock`,`Sextra`,`hcover` — `R2MinorCover:19`). `(C MA).Sblock` is then defeq
     `MR.MB.Sblock MA`, so `MR.MB.hblock`/`MR.MB.hextra` match the endpoint's `hblock`/`hextra` args.
   - `MR.hminorCtrl` matches the endpoint's `hminorCtrl` VERBATIM (both `< (0.8·exp(-π²/2)/2)/σ`).
   - `hNL` from §C.
5. **`hEmin`** (needed for `hNF`): `∀ e ∈ D.E, 2^{2k0} ≤ e`. `D.E = r2Edges D.BS D.Q D.R D.S`
   `= (ctrlEdges D.BS ∪ D.Q) ∪ gadgetEdges D.R D.S` (`Finset.mem_union` twice). Cases:
   ctrl: `ctrlEdges_ge_k0_square` (`2^{k0}·2^{k0} ≤ e`, `= 2^{2k0}`); Q: `QB.hQpair` gives `e=p·q`
   with `p,q ∈ blockSupport`, each `≥ 2^{k0}` (window) ⟹ `e ≥ 2^{2k0}`; gadget: `r·s`, `r≥2`,
   `s ≥ 2^{2k0}` ⟹ `≥ 2^{2k0}`. Cast ℕ→ℝ via `push_cast`.
6. **`hextraLight` — LEAVE AS `sorry`.** Insert:
   ```lean
   (by sorry)  -- PROBLEM_extra_light_3sigma.md: ∑_{E\ctrl}1/e² ≤ 3σ². Crux: ∑_{NonAdj}1/(pq)² ≤ 2σ².
   ```
   Do NOT attempt it; do NOT weaken the endpoint's constant `3`.

## Acceptance
`lake env lean RequestProject/R2TopAssembly.lean` shows NO `error`, exactly ONE `sorry`
(the `hextraLight`). Bundle the updated `R2TopAssembly.lean` (+ any oleans) back. Do NOT convert the
3 cited axioms to `theorem … := by sorry`.
