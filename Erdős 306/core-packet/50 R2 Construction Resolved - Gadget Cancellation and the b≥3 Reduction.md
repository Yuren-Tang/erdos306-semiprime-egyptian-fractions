# R2 Construction Resolved: Gadget Cancellation and the b≥3 Reduction

Back to [[00 README]]. This note resolves the R2 construction design that
[[46 R2 Construction Design - Multiplicity Is Not Enough]],
[[48 R2 Extra Support Bookkeeping Completed]] and
[[49 R2 Extra-Energy Minor Arc Interface Task]] left open. It corrects an
over-optimistic reading in the handoff (which called the remainder "delicate
parameter bookkeeping, no new idea"). There **was** a genuine missing idea; it
is now supplied. The frontier is `CircleMethod.exists_arcConstruction` in
`CircleMethodAssembly.lean` (the last sorry of the R2 lane; see
[[35 Circle Method - Detailed Spec (Translation-Ready)]] C0–C5).

## 0. The consumer's contract (verified)

`exists_pos_weighted_of_construction` consumes an `ArcConstruction T b`: data
`E, θ, L, N, SM, Sm, lbl, Bm` and the fields `hsemi … hbeat`. Crucially it needs
only `range L = SM ⊎ Sm` (`hpart`/`hdisj`), the label bijection `SM ≃ [-N,N]`
with `fourierTerm = term_label` (`hterm`), the main smallness (`htw`/`hsmall`),
and `hminor : ‖∑_{Sm} fourierTerm‖ ≤ Bm < c₃/σ_E` (`hbeat`). There is **no**
`hnotmain` field — that is an internal obligation when discharging `hminor` via
`minor_arc_bound_fiber_tail`. The verified main lower bound is
`main_sum_re_lower : c₃/σ_E ≤ Re ∑_{SM} fourierTerm`, `c₃ = 0.8·e^{-π²/2}/2`.

## 1. Pure block-alignment forces W = 0 (gadgets are essential)

Write `M := ∏_{p∈blockSupport} p`, and suppose **every** edge prime lies in
`blockSupport` (no edge involves a prime of `b`). Then `L = b·M` (we always need
`b ∣ L` for the phase `e(-h/b)`), and every edge value divides `M`. Hence the
Bernoulli product `∏_e (1-θ_e+θ_e e(h/e))` depends only on `u := h mod M`, while
the target phase `e(-h/b)` depends only on `v := h mod b`. Since `gcd(M,b)=1`,
the Fourier identity factors:
$$W=\frac1L\sum_{h\bmod L}\Big[\prod_e\cdots\Big]e(-h/b)
   =\frac1L\Big[\sum_{u\bmod M}\prod_e\cdots\Big]\Big[\sum_{v\bmod b}e(-v/b)\Big]=0,$$
because $\sum_{v=0}^{b-1}e(-v/b)=0$ for $b\ge2$.

**Consequence.** A gadget-free `ArcConstruction` is *unsatisfiable*: `hmain_re`
gives `Re ∑_{SM} ≥ c₃/σ>0`, so if `W=0` the minor part must cancel the main part,
forcing `‖∑_{Sm}‖ ≥ c₃/σ`, contradicting `hbeat`. Note 35's gadget edges
`{r,s_r}` (`r∣b`) are therefore **mandatory**: they inject `b`'s primes into the
Bernoulli product, breaking the `v`-sum factorization.

## 2. Keep the extra primes equal to the primes of b (kills the parameter cycle)

Note 46 §2's parameter cycle — `η` is fixed before `BS`, but the fiber
multiplicity `M = L/∏blockSupport` (or the fiber-tail `K`) depends on the
mass batch chosen after `BS` — only bites if mass/gadget edges use primes
*outside* the blocks. **Avoid this entirely**: take

* **mass edges** = products of two *block* primes (block-aligned), and
* **gadget edges** `{r, s}` with `r∣b` and `s` a *block* prime.

Then `edgePrimeSupport E ⊆ blockSupport BS ∪ {primes of b}`, so
`extraPrimeSupport BS E = {primes of b}` — a set of size `ω(b)`, *independent of
the construction*. With `L = b·∏blockSupport`, the block-frequency fiber has
multiplicity exactly `b` (`FiberCount.mainArc_fiber_card_le`), and the
fiber-tail `K` of `minor_arc_bound_fiber_tail` is a genuine **constant**
(depends only on `b`, not on the batch). The cycle dissolves: `K` is known
before `η` is chosen.

This needs block-aligned mass to reach the common-θ load window
`load ∈ [3/(2b), 3/b]` (so `θ=(1/b)/load ∈ [1/3,2/3]`, the C1 trick in
`circle_method_edge_mass_package`). The block-aligned reciprocal mass available
under `admissibleGlobalRange` (`k0 ≤ k ≤ K=3k0`) is
$$\sum_{\substack{p<q\\ \text{block primes}}}\frac1{pq}
  \approx\tfrac12\Big(\sum_{p}\tfrac1p\Big)^2
  \approx\tfrac12(\log3)^2\approx0.60.$$
For `b≥3`, `3/(2b)≤0.5≤0.60`, so a greedy subset hits the window. **For `b=2`
the window is `[0.75,1.5]` and `0.60<0.75`: block-aligned mass is provably
insufficient.**

## 3. The b = 2 reduction (sidestep the deficit)

Run the circle method only for **squarefree `b ≥ 3`**, and represent the small
cases by composition on cumulative obstruction sets, exactly as the existing
`exists_semiprime_egyptian_one` does for `b=1`:

* `1/2 = 1/3 + 1/6` (both `b∈{3,6}`, squarefree `≥3`);
* `1` already handled (`1 = 1/2 + 1/3 + 1/6`, with `1/2` re-expanded as above so
  no `b=2` circle-method call is needed).

The `HasEgyptianSemiprimeReprAvoiding` machinery already supports disjoint-union
composition on growing `T`, so this is a finite add-on, not new analysis.

## 4. The real crux: the b-fiber siblings ("extra-minor"), damped by O(log C) gadgets

Even with multiplicity `b`, the **fiber siblings of main-arc frequencies** break
the naive minor split. Let `SM` be the canonical small lifts (one `h≡m mod L`
per label `|m|≤N`, from `exists_mainArc_bijection`). A sibling
`h' = h + jM (mod L)`, `j=1,…,b-1`, has the *same* block residues
`a(h')=a(h)`; so if `a(h)∈mainArc`, then `a(h')∈mainArc` too, yet `h'∈Sm`. Thus
`hnotmain` **fails** on `Sm = range L \ SM`, and `minor_arc_bound_fiber_tail`
(which requires `a(h)∉mainArc` on all of `Sm`) covers only the **block-minor**
part `{h∈Sm : a(h)∉mainArc}`. The siblings are the **extra-minor** part of
note 46 §4, and they are *not* negligible in count: `(2N+1)(b-1) ≈ (2C/σ)(b-1)`.

**Why one gadget per prime is not enough.** On the diagonal the block charfactors
are `≈1`, so a sibling's term has modulus `≈ ∏_{gadgets}|cf|`. A single gadget
gives only constant damping (e.g. `|cos(π/3)|=1/2` for `b=3`), so
`‖extra-minor‖ ≲ (2C/σ)(b-1)·\text{const} ∼ C/σ ≫ c₃/σ`. Insufficient.

**The fix: use `G` gadgets `{r, s_1},…,{r, s_G}` per prime `r∣b`** (`s_i`
distinct block primes). For a sibling with `t_r≠0` (some prime `r` of `b`):
since each `s_i ∣ M` and `gcd(s_i,r)=1`, the CRT difference `h' - h (mod r s_i)`
is a nonzero multiple of `s_i` congruent to `t_r (mod r)`, of size in
`[s_i, r s_i/2]`, so
$$\Big\|\tfrac{h'}{r s_i}\Big\|\in\Big[\tfrac1r,\tfrac12\Big],\qquad
  |cf(h'/(r s_i))|^2=1-4\theta(1-\theta)\sin^2(\pi\|\cdot\|)\le 1-\tfrac89\sin^2(\tfrac\pi r)=:\rho_r^2<1.$$
Hence each of the `G` gadgets for `r` damps the sibling by `ρ_r<1`, giving
per-sibling damping `≤ ρ_r^G` (the other primes' gadgets contribute `≤1`). So
$$\big\|{\textstyle\sum_{\text{extra-minor}}}\big\|
  \le (2N+1)(b-1)\,\rho_{\max}^{\,G}\cdot\max_m\!\prod_{\text{block}}|cf(m)|
  \le (2C/\sigma+1)(b-1)\,\rho_{\max}^{\,G}.$$
Choosing `G ≥ log\big(4Cb/c₃\big)/\log(1/ρ_{\max})` makes this `< c₃/(2σ)`. The
factor `1/σ ∼ k₀` cancels against the budget `c₃/σ`, so **`G` is independent of
`k₀`**; it depends only on `C` and `b`, and `C` is a fixed (large) constant from
the block-minor chase. `G = O(\log C)` gadgets per prime — finite, no cycle.

## 5. The de-risked parameter order (no circularity)

1. Fix `ε=1`. Pick `η = c₃/(4K)` (`K` the constant fiber-tail of §2).
2. `minor_arc_bound_fiber_tail` returns `k0min, Ctail` (depend on `η`).
3. Pick `C ≥ 1` large with `K·Ctail·e^{-C²·8/9} < c₃/4` (block-minor tail).
4. Pick `G = O(\log(Cb/c₃))` (extra-minor damping, §4).
5. Pick `k₀ = max(k0min, …)` large: density window, `htw`/`hsmall`/`hN`
   smallness, `2N+1 ≤ L`, and `∑_{extra}1/e² ≤ 3σ_ctrl²` so `σ_E ≤ σ_ctrl`
   (`ArcConstructionSigma.sigmaE_le_sigmaCtrl_of_extra_light`).
6. Build `BS`, then `E = ctrlEdges ∪ massBatch ∪ gadgets`, `θ` common, `L = b·∏blockSupport`.

Then `Bm = ‖block-minor‖ + ‖extra-minor‖ ≤ K(η+Ctail e^{-C²8/9})/σ_ctrl + c₃/(2σ)
< c₃/σ_ctrl ≤ c₃/σ_E` (using `σ_E ≤ σ_ctrl`), i.e. `hbeat`. ∎(design)

## 6. What is now banked vs. remaining

**Banked & green:** `exists_blockSystem`, `ctrlEdges`(+semiprime/injOn),
`QE_ge_Qctrl`, `minor_arc_bound_fiber_tail` (block-minor), `exists_mainArc_bijection`,
`fourierTerm_eq_term_label_of_modL` (`hterm`), `FiberCount.mainArc_fiber_card_le`,
`ArcConstructionExtra` support split, `ArcConstructionSigma` (`σ_E ≤ σ_ctrl`),
and the C1 mass package `circle_method_edge_mass_package` (common-θ, exact mass)
— though the latter is *window*-aligned and must be redone block-aligned.

**Remaining (real Lean work, design now fixed):**
- **(R2-mass)** a *block-aligned* mass batch: products of two block primes,
  reciprocal load in `[3/(2b),3/b]`, avoiding `T` and `ctrlEdges` (adapt
  `MassBatch`/`exists_finset_primes_recip_between` to draw from `blockSupport`).
- **(R2-extra-minor)** the new lemma of §4: `‖∑_{extra-minor} fourierTerm‖ ≤ c₃/(2σ)`
  via `G` gadgets — the genuinely new estimate (a CRT/product damping bound).
  This is note 46 §4's "extra-minor direct estimate", now with the explicit
  `G = O(log C)` gadget count.
- **(R2-assembly)** populate the 30 fields and run §5's parameter order.
- **(b=2/b=1)** the `1/2 = 1/3+1/6` add-on (§3), mirroring `exists_semiprime_egyptian_one`.

## 7. Honest status

The R2 **design is now complete and internally consistent** (gadgets mandatory,
extra primes = primes of `b`, `b≥3` only, `O(log C)` gadgets damp the siblings,
parameter order acyclic). This is a real correction to the "bookkeeping-only"
framing. It is still a multi-session *formalization*; the one genuinely new
estimate is R2-extra-minor (§4). No research-level analytic gap remains on the
route — the heavy SBEE/FS machinery stays off this critical path. See
[[35 Circle Method - Detailed Spec (Translation-Ready)]] and
[[46 R2 Construction Design - Multiplicity Is Not Enough]].
