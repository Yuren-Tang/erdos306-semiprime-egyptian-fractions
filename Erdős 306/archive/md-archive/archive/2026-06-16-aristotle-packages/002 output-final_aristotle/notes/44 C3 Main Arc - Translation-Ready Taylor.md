# Note 44 — C3 main arc (Bernoulli Taylor), translation-ready

**Goal.** Provide the positive real main term for C5: for the Construction
`(E, θ, L)` with weights `θ_e ∈ [1/3,2/3]`, mass `∑_e θ_e/val(e) = 1/b`, and
deviation `σ_E² = ∑_e θ_e(1-θ_e)/val(e)²`, the main-arc Fourier sum is a positive
real `≥ c₃/σ_E`. Feeds `positivity_from_arcs` (done) via the split
`L·Wcount = main + minorSum` (`wcount_fourier_identity`, done) and
`main_arc_gaussian_lower` (done, `CircleMethodArcs`).

Recall the term for frequency `h`: `term(h) = (∏_e φ_{θ_e}(h/val(e)))·e(-h·(L/b)/L)`
where `φ_θ(t) = (1-θ)+θ·e(t)` = `bernoulliCharFun θ t` (root namespace),
`e(x)=exp(2πix)`. Main arc `M_C = {h : a(h) diagonal with label m, |m| ≤ C/σ_E}`,
`a(h)_p = h mod p`. For `h ∈ M_C` with label `m`, `h/val(e) ≡ m/val(e)` so
`φ_{θ_e}(h/val(e)) = φ_{θ_e}(m/val(e))` (periodicity; `val(e)=pq | L`).

## L1 — per-edge complex Taylor (the analytic core)
For `θ ∈ [1/3,2/3]` and real `t` with `|t| ≤ 1/10` (here `t = m/val(e)`,
`|t| ≤ (C/σ_E)/val(e) ≤ C/(σ_E·4^{k0}) ≤ 1/10` for `k0 ≥ k0(C)`):
```
Log φ_θ(t) = 2πi θ t − 2π² θ(1−θ) t² + r_e,   |r_e| ≤ K₀ |t|³
```
with an ABSOLUTE constant `K₀` (e.g. `K₀ = 100`). Derivation: `φ_θ(t) =
1 − θ(1 − e(2πit))`; set `w := θ(1 − e(2πit))`. `|1−e(2πiu)| = 2|sin(πu)| ≤ 2π|u|`,
so `|w| ≤ θ·2π|t| ≤ 2π/10 < 0.63 < 1`, hence `Log(1−w) = −w − w²/2 − w³/3 − …`,
`|Log(1−w) + w + w²/2| ≤ |w|³/(3(1−|w|)) ≤ |w|³`. And expand
`w = θ(1−e(2πit)) = θ(−2πi t + 2π² t² + O(t³))` (Taylor of `1−e^{ix}`,
`|1−e^{ix} − (−ix + x²/2)| ≤ |x|³/6`). Collect:
`−w − w²/2 = 2πi θ t − 2π² θ t² + 2π² θ² t² + O(t³) = 2πiθt − 2π²θ(1−θ)t² + O(t³)`
(since `−2π²θ t² + 2π²θ² t² = −2π²θ(1−θ)t²`). All `O(t³)` constants absolute for
`|t| ≤ 1/10`. **Formalization tools:** `Complex.log`, the geometric remainder for
`Log(1−w)` (or `Complex.abs_log_sub_add_sum_range_le` / `Complex.log_one_add_…`
remainder lemmas), and the `exp`/`sin` Taylor bounds already used in
`BernoulliFourier` (`Complex.exp`, `Real.sin`). This is the single hardest sub-step;
isolate the remainder bound `hrem_edge : |Log φ_θ(t) − (2πiθt − 2π²θ(1−θ)t²)| ≤ K₀|t|³`
as a named lemma.

## L2 — sum over edges + linear cancellation
Sum L1 over `e ∈ E` at `t_e = m/val(e)`:
```
Log ∏_e φ_{θ_e}(m/val(e)) = 2πi m (∑_e θ_e/val(e)) − 2π² m² (∑_e θ_e(1−θ_e)/val(e)²) + δ
                          = 2πi m / b − 2π² m² σ_E² + δ,   |δ| ≤ K₀ |m|³ ∑_e val(e)^{-3}.
```
using the **mass identity** `∑_e θ_e/val(e) = 1/b` (linear coeff) and the σ_E²
definition (quadratic coeff). Then `∏_e φ = exp(2πi m/b − 2π² m² σ_E² + δ)`.
**Bound on δ:** `∑_e val(e)^{-3} ≤ (max_e val(e)^{-1})·∑_e val(e)^{-2} ≤
(1/4^{k0})·σ_E²·(9)` (since `θ(1−θ) ≥ 2/9` so `val^{-2} ≤ (9/2)θ(1−θ)val^{-2}`,
`∑ ≤ (9/2)σ_E²`). So `|δ| ≤ K₀·(9/2)·|m|³ σ_E² / 4^{k0} ≤ K₀·(9/2)·(C/σ_E)³ σ_E²/4^{k0}
= (9K₀/2)·C³/(σ_E·4^{k0}) ≤ 1/10` for `k0 ≥ k0(C)`. (Note `|m| ≤ C/σ_E`.)

## L3 — multiply by `e(−m/b)` (cancel linear) ⇒ real Gaussian
`term(h) = (∏_e φ)·e(−h(L/b)/L) = (∏_e φ)·e(−m/b)` (since `h(L/b)/L = h/b ≡ m/b`).
`= exp(2πi m/b − 2π²m²σ_E² + δ)·exp(−2πi m/b) = exp(−2π²m²σ_E² + δ)`.
So `term(h) = exp(−2π²m²σ_E²)·exp(δ)`, `|δ| ≤ 1/10`. Hence
`Re term(h) ≥ exp(−2π²m²σ_E²)·cos(Im δ)·e^{Re δ} ≥ exp(−2π²m²σ_E²)·(9/10)`
(for `|δ|≤1/10`: `e^{Re δ}cos(Im δ) ≥ e^{-1/10}cos(1/10) ≥ 0.88 ≥ 9/10`? use
`≥ 0.85`; pick the constant so it works). Simpler: `|term(h) − exp(−2π²m²σ_E²)|
≤ exp(−2π²m²σ_E²)·|e^δ − 1| ≤ exp(−2π²m²σ_E²)·(e^{1/10}−1) ≤ 0.11·exp(−2π²m²σ_E²)`,
so `Re term(h) ≥ 0.89·exp(−2π²m²σ_E²)` and `|Im term(h)| ≤ 0.11·exp(−…)`.

## L4 — main = real, positive, ≥ c₃/σ_E
`main := ∑_{h∈M_C} term(h)`. The label-`m` fibre: for each `m` with `|m|≤C/σ_E`
there is exactly one diagonal `a(h)` (the all-`P_E` CRT bijection), so the sum is
indexed by `m ∈ [-⌊C/σ_E⌋, ⌊C/σ_E⌋]`.
- **Re main** `≥ 0.89·∑_{|m|≤C/σ_E} exp(−2π²σ_E²m²) ≥ 0.89·(e^{-π²/2}/2)/σ_E`
  by L3 + `main_arc_gaussian_lower` (with `σ = σ_E`, `N = ⌊C/σ_E⌋ ≥ 1/σ_E` since
  `C ≥ 1`). Set `c₃ := 0.89·e^{-π²/2}/2 > 0`.
- **Im main `= 0`** by the symmetry `m ↦ −m`: `term` at label `m` and `−m` are
  complex conjugates (`exp(−2π²m²σ²+δ_m)` with `δ_{-m} = conj δ_m`, since the
  Taylor coeffs are real×(powers of `m`): linear `2πiθt` is odd→imaginary,
  cancels with `e(-m/b)`; quadratic real even; remainder conj-symmetric). So
  `term(−m) = conj(term(m))`, pairing gives `main ∈ ℝ`. (For the C5 application it
  suffices that `Re main ≥ c₃/σ` and `|main| ≥ Re main`; or feed `main := Re(LW −
  minorSum)` and bound. Cleanest: take `main := (∑_{h∈M_C} term h).re` as the real
  number, and bound `‖minorSum‖ < main` using `Re main ≥ c₃/σ`; positivity_from_arcs
  uses `minorSum.re` so only `Re` is needed — NO need to prove `Im main = 0`.)

> **Implementation note:** `positivity_from_arcs` only uses `minorSum.re` and a real
> `main` with `L·W = main + minorSum.re`-type extraction. So define
> `main := (∑_{h ∈ M_C} term h).re`, `minorSum := ∑_{h ∉ M_C} term h` (complex).
> Then `L·W = (main : ℂ) + (i·Im(mainsum)) + minorSum`; fold `i·Im(mainsum)` into
> minorSum' and bound `‖minorSum'‖ ≤ |Im mainsum| + ‖minorSum‖`. To avoid bounding
> `Im mainsum`, instead PAIR `m,−m` first so the main sum is manifestly real
> (`term m + term (−m) = 2 Re(term m)`), making `main` real by construction. Decide
> at formalization time; the `m↔−m` pairing is the clean route.

## Assembly (R3, after L1–L4)
`L·Wcount = ∑_{h<L} term h` (`wcount_fourier_identity`) `= main + minorSum`
(split `range L = M_C-freqs ⊎ minor`). `main ≥ c₃/σ_E` (L4),
`‖minorSum‖ ≤ (η + Ctail e^{-C²(8/9)})/σ_ctrl` (`minor_arc_bound`, with the
construction discharging its `hQE/hnotmain/hinj` — needs `E`-primes ⊆ blockSupport
& `E ⊇ ctrlPairs` & `L = ∏ blockSupport`, so the CRT map is a genuine bijection and
strict injectivity holds; see the gadget caveat in memory — resolve by putting all
edge primes in blocks). With `σ_E ≍ σ_ctrl`, choose `k0` large then `C` large so
`minor < main`. `positivity_from_arcs` ⇒ `Wcount > 0` ⇒
`exists_positive_weighted_construction`.

## Lemma list (priority)
1. `hrem_edge` (L1) — per-edge complex-log Taylor remainder ≤ K₀|t|³. **Hardest.**
2. `prod_log_expansion` (L2) — sum + mass-identity cancellation + δ bound.
3. `term_eq_gaussian_mul` (L3) — `term(h) = exp(−2π²m²σ²)·exp(δ)`, `|δ|≤1/10`.
4. `main_re_lower` (L4) — `Re main ≥ c₃/σ_E` via 3 + `main_arc_gaussian_lower`.
5. assembly (R3) — split + `positivity_from_arcs`.

L1 is the single hard analytic step (complex Taylor remainder); 2–5 are bookkeeping
on top of it + the already-verified `main_arc_gaussian_lower`. Everything else in
Phase C (entire minor arc, Fourier identity, arc separation) is machine-verified.
