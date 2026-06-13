# G5–G7 Instantiation: Complete Proofs for Translation

Back to [[00 README]]. This note supersedes the *instantiation* part of
[[37 Faithful G5 G7 C Formalization Blueprint]] (§§3–5). The abstract layer of
note 37 §3 is now machine-verified (`GlobalPeierlsBookkeeping.lean`). What
remains for Phase G is closing `GlobalControl.global_levelset` (G5) and
`GlobalControl.global_control_partition` (G7). **This note writes out every
remaining step with full proofs, in dependency order, so the work is
translation, not rediscovery.**

Three corrections to earlier specs are flagged inline; read §0 first.

---

## §0. Three corrections (read before anything else)

**(C-a) `admissibleGlobalRange` must also bound K from below.** Change

```lean
def admissibleGlobalRange (BS : BlockSystem) : Prop := BS.K ≤ 3 * BS.k0
```

to

```lean
def admissibleGlobalRange (BS : BlockSystem) : Prop :=
  2 * BS.k0 ≤ BS.K ∧ BS.K ≤ 3 * BS.k0
```

Reason: the initial-segment label factor (§5, step L) produces `1 + 2C√R/σ_{k0}`,
and the comparison `σctrl ≤ C·k0·σ_{k0}` (§4, Lemma S3) carries a factor `k0`,
which must be absorbed into `exp(A·numBlocks)`. That requires
`numBlocks = K+1−k0 ≥ k0+1`, i.e. `2k0 ≤ K`. Faithful: the circle-method
construction (note 35 / CP 01) takes `K ≈ 3k0` anyway; a lower bound on `K`
costs nothing.

**(C-b) The note-37 §4 uniqueness sketch is WRONG; use the two-prime proof.**
Note 37 suggested deriving label uniqueness from one common prime and
`|m−m′| < p`. But `IsDominant` only gives `|m| ≤ X²/2`, so `|m−m′|` can be as
large as `X² ≥ p`. The correct argument (note 29 §3 A1, simplified) uses TWO
common primes: see §3, Lemma L2u below.

**(C-c) `GlobalPeierls.prod_local_count_le` is NOT sufficient for the
energy-shell bookkeeping.** It bounds the product for ONE fixed energy vector,
but the decoder does not know the per-block energies; the encoding must record
an integer shell vector, and the enumeration of shell vectors needs a geometric
discount. The missing lemma (`shell_sum_bound`) is stated and proved in §1.

---

## §1. Shell-sum lemma (new lemma for `GlobalPeierlsBookkeeping.lean`)

> **Lemma SH (shell sum).** Let `I` be a finite index set, `α, β > 0`, and for
> each `k ∈ I` and each `n ∈ ℕ` a count `c k n ≥ 0` with
> `c k n ≤ exp(α(n+1))`. Then for every `R ≥ 0`:
> $$\sum_{\substack{(n_k)\in\mathbb N^I\\ \sum_k n_k\le R}}\ \prod_{k\in I}c_k(n_k)
> \ \le\ e^{(\alpha+\beta)R}\cdot
> \exp\Big(|I|\cdot\big(\alpha+\log\tfrac1{1-e^{-\beta}}\big)\Big).$$

*Proof.* For any admissible vector, `∏ c_k(n_k) ≤ ∏ e^{α(n_k+1)} =
e^{α|I|}·e^{α∑n_k} ≤ e^{α|I|}·e^{(α+β)R}·∏ e^{−βn_k}` (using `∑n_k ≤ R`).
Drop the constraint and sum over ALL of `ℕ^I`:
`∑_{(n_k)∈ℕ^I} ∏ e^{−βn_k} = ∏_k ∑_{n≥0} e^{−βn} = (1−e^{−β})^{−|I|}`. ∎

Lean shape (finitize the vector space as `I → Finset.range (⌊R⌋₊+1)` or sum
over `Finset.Nat.antidiagonal`-style products; the inner identity is
`Finset.prod_sum` / geometric series `∑_{n<N} e^{−βn} ≤ 1/(1−e^{−β})`):

```lean
lemma shell_sum_bound {ι : Type*} (I : Finset ι) (c : ι → ℕ → ℝ)
    (alpha beta R : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) (hR : 0 ≤ R)
    (hc0 : ∀ k ∈ I, ∀ n, 0 ≤ c k n)
    (hcb : ∀ k ∈ I, ∀ n : ℕ, c k n ≤ Real.exp (alpha * (n + 1))) :
    ∑ v ∈ (I.pi fun _ => Finset.range (⌊R⌋₊ + 1)) |>.filter
        (fun v => (∑ k ∈ I.attach, (v k.1 k.2 : ℝ)) ≤ R),
      ∏ k ∈ I.attach, c k.1 (v k.1 k.2)
    ≤ Real.exp ((alpha + beta) * R) *
      Real.exp ((I.card : ℝ) * (alpha + Real.log (1 / (1 - Real.exp (-beta)))))
```

(Use whatever finite encoding of the shell vector is most convenient — the
restriction `n_k ≤ ⌊R⌋₊` is harmless since `∑ n_k ≤ R`. Only the INEQUALITY
shape matters; keep `alpha, beta` universally quantified.)

**Usage in G5:** `α = 2ε`, `β = ε`; the absolute constant
`A₂(ε) := 2ε + log(1/(1−e^{−ε}))` joins the `exp(A·numBlocks)` factor.

---

## §2. Block decomposition of the global assignment

Three small structural lemmas in `GlobalControl.lean`.

> **Lemma D1 (windows disjoint).** For `k ≠ k'`, `BS.P k ∩ BS.P k' = ∅`.

*Proof.* `p ∈ P k` forces `2^k ≤ p < 2^{k+1}` (BS.hwindow); the dyadic windows
are pairwise disjoint. ∎

> **Definition (block restriction).** For `a : GlobalAssignment BS` and
> `k ∈ [k0,K]`, let `restrict BS a k : BlockAssignment (BS.P k)` be
> `fun p => a ⟨p.1, mem_blockSupport …⟩` (each `p ∈ P k` lies in
> `blockSupport BS`).

> **Lemma D2 (joint injectivity).** The map
> `a ↦ (restrict BS a k)_{k ∈ Icc k0 K}` is injective.

*Proof.* Every `p ∈ blockSupport BS` lies in some `P k`, `k ∈ [k0,K]`
(definition of `blockSupport`); two assignments agreeing on every restriction
agree at every such `p`, hence are equal (funext on the subtype). ∎

> **Lemma D3 (energy splits).** With `R_k := QP (BS.P k) (restrict BS a k)`
> and `Xen_k := ∑_{pq ∈ bipartitePairs BS k} (Hglob (toPlain BS a) pq.1 pq.2 / (pq.1·pq.2))²`:
> $$\sum_{k=k_0}^{K}R_k\ +\ \sum_{k=k_0}^{K-1}\mathrm{Xen}_k\ \le\ Q_{\rm ctrl}(BS,a).$$

*Proof.* `ctrlPairs` is the disjoint union of the internal pair sets (per
block, disjoint by D1) and the bipartite pair sets (disjoint across `k`: a
bipartite pair for `k` has its smaller element in window `k`, larger in window
`k+1`, so `k` is determined). Each summand of `Qctrl` is nonnegative, and
`QP (P k) (restrict a k)` is literally the sub-sum of `Qctrl` over
`internalPairs BS k` (the CRT representative depends only on `a p, a q`). ∎

(Check the existing defs `internalPairs` / `bipartitePairs` / `Qctrl` to align
index conventions; if `QP`'s pair set `orderedPrimePairsA` differs from
`internalPairs` by ordering, add the one-line reindexing lemma.)

> **Lemma D4 (product count).** For predicates `Φ_k` on `BlockAssignment (BS.P k)`:
> $$\#\{a:\ \forall k\in[k_0,K],\ \Phi_k(\mathrm{restrict}\,a\,k)\}\ \le\
> \prod_{k=k_0}^{K}\#\{b:\ \Phi_k(b)\}.$$

*Proof.* D2's injection lands in the product of the filtered finsets;
`Fintype.card_pi` / `Finset.card_le_card_of_injOn`. ∎

---

## §3. Extraction lemmas from the verified single-block package

All four live most naturally in `SBEEForcing.lean` (or a small new file
importing it). They are restatements of material ALREADY INSIDE proved
theorems; no new mathematics.

### L2u — dominant label uniqueness (two-prime argument; replaces note 37 §4's wrong sketch)

```lean
lemma dominant_label_unique (X : ℕ) (hX : 4 ≤ X) (P : Finset ℕ)
    [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 4 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (m m' : ℤ)
    (hm : |m| ≤ (X:ℤ)^2 / 2) (hm' : |m'| ≤ (X:ℤ)^2 / 2)
    (hclass : (1-ρ)*(P.card:ℝ) ≤ ((P.attach.filter
        (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ))
    (hclass' : (1-ρ)*(P.card:ℝ) ≤ ((P.attach.filter
        (fun p => a p = ((m':ℤ):ZMod (p:ℕ)))).card:ℝ)) :
    m = m'
```

*Proof.* Let `C, C'` be the two filtered sets. `|C|+|C'| ≥ 2(1−ρ)N ≥ (3/2)N`,
so `|C ∩ C'| ≥ N/2 ≥ 2`. Pick distinct `p, q ∈ C ∩ C'`. At each,
`m ≡ a_p ≡ m' (mod p)` and likewise mod `q`, so `p ∣ m−m'` and `q ∣ m−m'`,
hence (p, q distinct primes) `pq ∣ m−m'`. But `pq ≥ X(X+1) > X² ≥ |m−m'|`
(since `|m|,|m'| ≤ X²/2`). A nonzero multiple of `pq` has absolute value
`≥ pq`; therefore `m−m' = 0`. ∎

(Everything is `Int` arithmetic plus `ZMod.intCast_eq_intCast_iff'` /
`Int.emod`-style divisibility; no analysis.)

### L5 — fixed-label fiber bound (extract `hfibcard` from `theorem_A_dominant_count`)

```lean
lemma fixed_label_count (eps ρ : ℝ) (hε : 0 < eps) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (m : ℤ) (hm : |(m:ℝ)| ≤ (P.card:ℝ)*(X:ℝ)/16)
          (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter (fun a : BlockAssignment P =>
                QP P a ≤ R ∧
                (1-ρ)*(P.card:ℝ) ≤ ((P.attach.filter
                  (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ))).card : ℝ)
              ≤ Real.exp (eps * R)
```

*Proof: verbatim the `hfibcard` block inside the proved
`theorem_A_dominant_count`* (SBEEForcing.lean, the `calc` chain
`fib m ⊆ {exceptions ≤ ⌊Hr⌋₊}` → `exception_count_bound` →
`dominant_encoding_card` → `theoremA_entropy`). Take
`X0 := max X0e (max X0c 16)` where `X0e` is from `theoremA_entropy` and `X0c`
from `exists_X0_logbnd` (needed for `32 ≤ P.card` from the density). The
hypothesis `hm` here replaces the internal `hmabs` derivation — note the
extraction does NOT need the `htriv` case split or `theoremA_R_poly`; those
were only used in `theorem_A_dominant_count` to DERIVE `hmabs` from the label
range, which we now assume. ∎

### L4c — absolute exception bound for cold blocks

```lean
lemma cold_exception_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ (e0 X0 : ℝ), 0 < e0 ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
          QP P a ≤ R → R ≤ c2 * X / (Real.log X)^3 →
          |(m:ℝ)| ≤ (P.card:ℝ)*(X:ℝ)/16 →
          (1-ρ)*(P.card:ℝ) ≤ ((P.attach.filter
              (fun p => a p = ((m:ℤ):ZMod (p:ℕ)))).card:ℝ) →
            ((P.attach.filter (fun q => a q ≠ ((m:ℤ):ZMod (q:ℕ)))).card : ℝ) ≤ e0
```

*Proof.* `exception_count_bound` gives `|E| ≤ 2^15·R·X²/((1−ρ)N³)`. Insert
`R ≤ c2·X/log³X` and `N ≥ X/(2logX)`:
`|E| ≤ 2^15·c2·(X³/log³X)·(8log³X)/((1−ρ)X³) = 2^18·c2/(1−ρ) =: e0`. ∎

### L3 range / L2 cold-dominance — already usable as-is

* **L3** is `theoremA_label_range` verbatim.
* **L2** is the contrapositive of `theorem_B_nondominant_forcing`: it yields
  `c2, X0` such that `QP P a ≤ R < c2·X/log³X ⟹ IsDominant X P a ρ`.
  Fix `ρ := 1/4` throughout Phase G.

### Cold-label size chain (small consequence, needed twice)

> **Lemma L3c.** There is `X0` such that for `X ≥ X0`, a cold block
> (`R_k ≤ c2 X/log³X`) with dominant label `m` satisfies BOTH
> `|m| ≤ N·X/16` (for L5/L4c) AND `32|m| ≤ 2^k·(N−e0)` etc. (the `hm`-type
> hypotheses of `mismatch_penalty_with_exceptions`).

*Proof.* L3 + `sigmaP_lower` give
`|m| ≤ (5/(1−ρ))·√R_k/σ_P ≤ 7·√(c2·X/log³X)·(6X²/N)
≤ 84·√c2·(X^{5/2}/log^{3/2}X)·(2logX/X) = 168√c2·X^{3/2}/√(logX)`.
Both targets are `≥ X²/(64 logX)`-sized, and
`X^{3/2}/√logX ≪ X²/(64logX)` ⟺ `(constants)·√logX·logX ≤ √X` — true for
`X ≥ X0(c2)`. (Constants lavish; just chase them.) ∎

---

## §4. Sigma comparison lemmas (`GlobalControl.lean`)

With `σ_k := sigmaP (BS.P k)` (note: `sigmaP` is over the SAME internal pairs
as `Qctrl`'s internal part — add the alignment lemma if pair-set encodings
differ).

> **Lemma S1.** `sigmaP (BS.P BS.k0) ≤ sigmaCtrl BS`.

*Proof.* `sigmaCtrl²` is a sum of nonnegative terms over `ctrlPairs ⊇`
internal pairs of block `k0`. ∎

> **Lemma S2.** `sigmaCtrl BS ≤ 4 · 2^{−k0}` and in particular
> `sigmaCtrl BS ≤ 1` (for `k0 ≥ 2`).

*Proof.* Internal block `k`: pairs `≤ N_k²/2 ≤ 4^k/2`, each term
`≤ (2^k·2^k)^{−2} = 16^{−k}`, subtotal `≤ 4^{−k}/2`. Bipartite `k`:
`≤ N_kN_{k+1} ≤ 2·4^k` terms, each `≤ (2^k·2^{k+1})^{−2} = 16^{−k}/4`,
subtotal `≤ 4^{−k}/2`. Sum the geometric series over `k ≥ k0`:
`sigmaCtrl² ≤ ∑_{k≥k0} 4^{−k} ≤ (4/3)·4^{−k0} ≤ 16·4^{−k0}`. ∎
(`N_k ≤ 2^k` because `P_k` sits in an interval of length `2^k`.)

> **Lemma S3.** There is an absolute `c_σ > 0` with
> `sigmaCtrl BS ≤ c_σ · BS.k0 · sigmaP (BS.P BS.k0)` (for `k0 ≥ 2`).

*Proof.* Lower-bound `σ_{k0}`: density gives
`N_{k0} ≥ 2^{k0}/(2·k0·log 2)`; `sigmaP² ≥ (N(N−1)/2)·(4X²)^{−2}`
(`sigmaP_lower`) with `X = 2^{k0}`: `σ_{k0} ≥ c·2^{−k0}/k0`. Combine with S2. ∎

**This `k0` factor is why §0 (C-a) requires `2k0 ≤ K`**: then
`numBlocks ≥ k0+1`, so `k0 ≤ e^{numBlocks}` and the factor
`c_σ·k0` is absorbed as `exp((1+log c_σ)·numBlocks)`.

---

## §5. G5 assembly (the main proof)

Fix `ρ := 1/4`. Inputs: L1 = `unified_levelset` (constants `C_ε, X1`), L2
(`c2, X0_B`), L2u, L3, L3c, L4c (`e0`), L5 (`X0_A`), G3 =
`mismatch_penalty_with_exceptions`, SH, D1–D4, S1–S3,
`subset_count_entropy`, `segment_label_constant`.

Throughout, `X_k := 2^k`, `N_k := (BS.P k).card`,
`R_w(k) := c2·X_k/(log X_k)³`,
`Π(k) := (N_{k+1}−e0−1)·(N_k−e0)³/(2^{13}·X_k²)` (the deterministic floor of
G3-with-exceptions when both blocks are cold; using `|E| ≤ e0` and `N_k`
density, `Π(k) ≥ 4^k/(C·k⁴)`).

Choose `k0min = k0min(ε)` large enough that all the finitely many numeric
inequalities marked (\*) below hold for `k0 ≥ k0min`; each is an explicit
`2^k`-vs-`poly(k)` comparison.

**Step 0 (trivial regime).** If `ε·R ≥ 2^{K+2}·(K+1)` then count ALL
assignments: `#GlobalAssignment ≤ ∏_k ∏_{p∈P_k} p ≤ exp(∑_k N_k·(k+1)·log2)
≤ exp(2^{K+2}(K+1)) ≤ e^{εR}`. Done (the other factors are `≥ 1`).
**Hence below assume `log R ≤ (K+2)·log 2 + log(K+1) + log(1/ε) ≤ 4·k0·(\*)`**
— this caps every `½·log R` term that appears in the entropy payments.

**Step 1 (per-assignment data).** Fix `a` with `Qctrl(a) ≤ R`. Set
`a_k := restrict a k`, `R_k := QP(a_k)`. By D3: `∑R_k ≤ R` and
`∑_k Xen_k ≤ R`. Call `k` **hot** if `R_w(k) ≤ R_k`, else **cold**. For cold
`k`, L2 applies (`R_k < R_w(k)`, valid once `X_{k0} ≥ X0_B` (\*)): `a_k` is
dominant; by L2u its label `m_k` is unique; by L3c `|m_k|` satisfies the L5/G3
size hypotheses; by L4c its exception set has `≤ e0` elements. Let
`H := {k : hot}`, `B := {k ∈ [k0,K−1] : k,k+1 both cold, m_k ≠ m_{k+1}}`.

**Step 2 (budgets).** `∑_{k∈H} R_w(k) ≤ ∑_{k∈H} R_k ≤ R`. For `k ∈ B`, G3
(`mismatch_penalty_with_exceptions`, hypotheses by Step 1) gives
`Π(k) ≤ Xen_k`, so `∑_{k∈B} Π(k) ≤ R`.

**Step 3 (segments).** On the cold indices, cut at `B`: by
`segment_label_constant` (with `P k := "k,k+1 cold and k ∉ B"`; the label map
extended arbitrarily at hot `k`), the label is constant on each maximal cold
run. Segments are determined by `(H, B)`. Each non-initial segment start
`k† > k0` has predecessor `k†−1` either hot or in `B`; this assignment of
payments is injective (each `k†−1` precedes one segment).

**Step 4 (the covering).** The level set is contained in the union over
`(H, B, shell vector (n_k), label choices)` of the product fibers:

$$\#\{Q_{\rm ctrl}\le R\}\ \le\
\underbrace{\sum_{H\ \text{adm}}}_{(\mathrm a)}\
\underbrace{\sum_{B\ \text{adm}}}_{(\mathrm b)}\
\underbrace{\sum_{(n_k):\ \sum n_k\le R}}_{(\mathrm c)}\
\underbrace{\sum_{\text{labels}}}_{(\mathrm d)}\
\prod_k \#\{b_k\}$$

where admissible means `∑_{k∈H}R_w(k) ≤ R`, `∑_{k∈B}Π(k) ≤ R`; `n_k = ⌊R_k⌋`;
labels = one integer per cold segment; and the per-block fiber is
`{b : QP ≤ n_k+1}` (hot) or `{b : QP ≤ n_k+1, label-m_k class ≥ (1−ρ)N_k}`
(cold, `m_k` from its segment's label). Formally this is D4 applied per
`(H,B,(n_k),labels)` plus `Finset.card_biUnion_le` — the exact pattern of
`hcover` in `theorem_A_dominant_count`, two levels up.

**Step 5 (per-factor bounds and the ε-budget).**

| factor | bound | proof |
|---|---|---|
| (a) #hot sets | `e^{εR/2}·e^{numBlocks}` | `subset_count_entropy`, weights `R_w(k)`, each `exp(−εR_w/4) ≤ 1` |
| (b) #boundary sets | `e^{εR/2}·e^{numBlocks}` | same, weights `Π(k)` |
| (c)+hot fibers+cold fibers | `e^{3εR}·e^{A₂(ε)·numBlocks}` | SH with `α=2ε, β=ε`; hot fiber `≤ C_ε e^{ε(n_k+1)}(1+√(n_k+1)/σ_k) ≤ e^{2ε(n_k+1)}` by L1 + the G4 absorption (\*) (hot ⟹ `n_k+1 > R_w(k)`, and `log C_ε + log(1+√(n_k+1)/σ_k) ≤ k+1+log(k+1)+½log(n_k+1)+O(1) ≤ ε·R_w(k) ≤ ε(n_k+1)` for `k ≥ k0min`, using Step 0's `log R` cap); cold fiber `≤ e^{ε(n_k+1)}` by L5 (X ≥ X0_A (\*)) |
| (d) non-initial segment labels | `e^{2εR}` | per segment starting at `k†`: label range L3 gives `≤ 1+2·7√R/σ_{k†}` choices `≤ exp(k†+log k†+½logR+O(1)) ≤ exp(ε·payment(k†−1))` (\*), payments injective (Step 3) and total payment `≤ 2R` (Step 2) |
| (d) initial segment label | `c_σ'·k0·(1+√R/σctrl)` | L3 at block `k0` + S3: `1+14√R/σ_{k0} ≤ 1+14c_σk0√R/σctrl ≤ 14c_σk0(1+√R/σctrl)`; the `k0` absorbed via §0 (C-a) |

Total ε-exponent: `½+½+3+2 = 6 ≤ 8` ✓ (two ε of slack for translation
friction). All block-counted constants collect into `exp(A·numBlocks)` with
`A := 2 + A₂(ε) + (1+log(14c_σ)) + …` — uniform in `BS`. ∎

**Remarks for the translator.**
* Do the whole thing concretely in `GlobalControl.lean` (the abstract-first
  route of note 37 §3 is DONE for the small lemmas; do not build a further
  abstract `GlobalCode` layer — instantiate directly, mirroring the proved
  `hcover`/`hfibcard` pattern of `theorem_A_dominant_count`).
* Private helper defs (e.g. `isHot`, `coldLabel` via `Classical.choice` on
  L2+L2u, `segments`) are fine; the THEOREM statement stays as in the file
  (modulo §0 (C-a)).
* Every (\*) is a finite `2^k` vs `poly(k)` comparison; bundle them into one
  `∃ k0min, ∀ k0 ≥ k0min, …` conjunction proved by explicit monotone
  calculus, the way `theoremB_logthreshold` / `exists_X0_logbnd` do.

---

## §6. G6 localization (new lemma, `GlobalControl.lean`)

> **Lemma G6.** Set `F0(BS) := min(R_w(k0), Π(k0), E1(k0))` where
> `E1(k) := (1−ρ)·(N_k−0)³/(2^{15}X_k²)` is the per-exception energy floor
> (all three are increasing in `k`, so the min over blocks is at `k0` (\*)).
> For `k0 ≥ k0min` and any `a ∉ mainArc BS C` with: then EITHER
> `Qctrl(a) ≥ F0(BS)`, OR `a` is globally diagonal — `∃m, ∀p, a_p ≡ m (p)` —
> with `|m| > C/σctrl`, in which case `Qctrl(a) = m²·σctrl² > C²`.

*Proof.* If some block is hot: `Qctrl ≥ R_k ≥ R_w(k) ≥ R_w(k0)`. If some
`k ∈ B`: `Qctrl ≥ Xen_k ≥ Π(k) ≥ Π(k0)` (G3). If some cold block has an
exception `q`: `exception_single_energy` gives cross-energy `≥ E1(k)` inside
that block, and that cross-energy is a sub-sum of `Qctrl` (D3). Otherwise: all
blocks cold, no boundaries (one segment ⟹ all labels equal `m` by Step-3
constancy), no exceptions ⟹ `a_p ≡ m (p)` for EVERY `p`. Then for every
control pair, `2|m| ≤ X_{k0}² < pq`, so `crtRepr = m` exactly
(`crtRepr_eq_label`), giving `Qctrl = m²σctrl²`. `a ∉ mainArc` forces
`|m| > C/σctrl`. ∎

---

## §7. G7 assembly

**Step 1 (full partition sum).** Apply the verified
`partfun_series_bound` with `ι = GlobalAssignment BS`, `q = Qctrl BS`,
`sig = sigmaCtrl BS`, level bound = G5 at `ε := c/32` (so `8ε = c/4 < c/2`),
`C0 = e^{A·numBlocks}`:
$$\sum_a e^{-(c/2)Q_{\rm ctrl}(a)}\ \le\ C(c)\,e^{A\cdot\mathrm{nB}}\cdot\big(1+\tfrac1{\sigma_{\rm ctrl}}\big)\ \le\ 2C(c)\,e^{A\cdot\mathrm{nB}}/\sigma_{\rm ctrl}$$
using S2 (`σctrl ≤ 1`). Same at exponent `c` for the first G7 inequality.

**Step 2 (sector I: energy floor).** By G6, off-arc non-diagonal `a` have
`Qctrl ≥ F0(BS)`:
$$\sum_{(\mathrm I)}e^{-cQ}\le e^{-cF_0/2}\sum_a e^{-(c/2)Q}\le
2C(c)\,e^{A\cdot\mathrm{nB}-cF_0(BS)/2}/\sigma_{\rm ctrl}.$$
With `admissibleGlobalRange` (`nB ≤ 2k0+1`) and `F0(BS) ≥ c'·2^{k0}/k0³` (\*):
`exp(A(2k0+1) − c·c'·2^{k0}/(2k0³)) ≤ η` for all `k0 ≥ k0min(η, c)`. This is
the ONLY place the `η` of the statement enters; `k0min` is chosen here.

**Step 3 (sector II: Gaussian tail).** Diagonal `a ↔ m` is injective for
`|m| ≤ X_{k0}²/2` (two distinct primes in `P_{k0}` divide `m−m'`; same
two-prime argument as L2u). So
$$\sum_{(\mathrm{II})}e^{-cQ}\le\sum_{|m|>C/\sigma}e^{-c\,m^2\sigma^2}
\le e^{-cC^2/2}\sum_{m\in\mathbb Z}e^{-c\,m^2\sigma^2/2}
\le e^{-cC^2/2}\cdot\Big(1+\tfrac{6}{\sigma\sqrt{c/2}}\Big)
\le C_{\rm tail}(c)\,e^{-cC^2/2}/\sigma.$$
The middle bound is the elementary Gaussian-sum lemma: with `A := cσ²/2 ≤ 1`,
$$\sum_{m\ge1}e^{-Am^2}\ \le\ \underbrace{\tfrac1{\sqrt A}}_{m\le1/\sqrt A}
+\sum_{m>1/\sqrt A}e^{-\sqrt A\,m}\ \le\ \tfrac1{\sqrt A}+\tfrac{2}{\sqrt A}
=\tfrac3{\sqrt A}$$
(using `m² ≥ m/√A` in the tail and `1−e^{−x} ≥ x/2` on `x ∈ (0,1]`). State it
as a standalone lemma `gaussian_int_sum_le`:

```lean
lemma gaussian_int_sum_le (A : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∑' m : ℤ, Real.exp (-A * (m:ℝ)^2) ≤ 1 + 6 / Real.sqrt A
```

(or the `Finset.Icc`-truncated version if `tsum` is awkward — the index set in
G7's statement is a finite type, so everything can stay finite).

Adding sectors I+II gives exactly the stated
`(η + Ctail·e^{−C²c/2})/σctrl`. ∎

---

## §8. After Phase G: Phase C pointers

No change to the plan: note 35 has the full circle-method computations
(C2 pointwise `|μ̂| ≤ e^{−(16/9)Q_E}`, C3 main-arc with exact mass
cancellation, C4 = G7 via the CRT bijection `h ↔ a` and `Q_E ≥ Q_ctrl`), and
note 37 §6 has the file split (C1a/C1b/C2/C3/C4/C5). The single allowed named
external input remains `chebyshev_block_density`. If a specific C-step stalls,
report which hypothesis/computation resists — a note-38-grade elaboration of
that step will follow.
