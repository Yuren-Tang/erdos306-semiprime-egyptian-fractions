# Faithful G5/G7/C formalization blueprint

Back to [[00 README]].  This note updates [[36 Aristotle Append - G5 G7 C Proof]]
after the latest Aristotle recovery package `output-final_aristotle/`.

## 1. What the latest package really established

The latest run made real progress.

* `GlobalControl.blockSupport`, `GlobalAssignment`, `toPlain`, and
  `ctrlPairs_mem_blockSupport` are in place.  Global assignments are now finite
  dependent products over the block support, not infinite functions
  `(p : Nat) -> ZMod p`.
* G2 is proved.
* Corrected no-exception G3 is proved.
* `mismatch_penalty_with_exceptions` is proved.
* The run caught a real faithfulness bug: if `Cglob` is chosen after `BS`, then
  G5 can be proved vacuously by taking `Cglob` to be the total number of global
  assignments of that fixed block system.

So the remaining mathematical/formal targets are exactly:

1. G5: global level-set, the segment/Peierls encoder.
2. G7: Laplace summation plus off-main-arc localization.
3. Phase C: construction + Fourier positivity, using G7.

## 2. One more statement correction before proving G5/G7

The latest package fixed one vacuity but overcorrected the constants.

The theorem should not say

```lean
exists Cglob, forall BS, ...
```

with a single absolute `Cglob` independent of the number of blocks.  Note 34
allows a harmless factor `C ^ (#blocks)`; G7 kills this because
`#blocks = O(k0)` while the Peierls floor is
`F0(k0) >= c * 2^k0 / k0^A`.

Use this faithful formulation instead.

```lean
def numBlocks (BS : BlockSystem) : Nat := BS.K + 1 - BS.k0

def admissibleGlobalRange (BS : BlockSystem) : Prop :=
  -- choose whichever form is easiest:
  BS.K <= 3 * BS.k0 ∧ 1 <= BS.k0
  -- or the weaker analytic form actually used:
  -- Real.log (BS.K + 2) <= eta * Rw (2^BS.k0)
```

Then state G5 as:

```lean
theorem global_levelset
    (eps : Real) (heps : 0 < eps) (heps1 : eps < 1) :
    exists k0min : Nat, exists A : Real, 0 < A ∧
      forall BS : BlockSystem,
        k0min <= BS.k0 ->
        admissibleGlobalRange BS ->
        forall R : Real, 1 <= R ->
          ((Finset.univ.filter
              (fun a : GlobalAssignment BS => Qctrl BS a <= R)).card : Real)
            <= Real.exp (A * numBlocks BS)
              * Real.exp (8 * eps * R)
              * (1 + Real.sqrt R / sigmaCtrl BS)
```

This is the faithful meaning of the old `Cglob = C^(K-k0)`.

For G7, do not use a fixed positive `F0`.  Either expose the growing floor
`F0 BS`, or state the final useful form directly:

```lean
theorem global_control_partition
    (c : Real) (hc : 0 < c) :
    forall eta : Real, 0 < eta ->
    exists k0min : Nat, exists Ctail : Real, 0 < Ctail ∧
      forall BS : BlockSystem,
        k0min <= BS.k0 ->
        admissibleGlobalRange BS ->
        forall C : Real, 1 <= C ->
          tsum (fun a : {a : GlobalAssignment BS // a.val notin mainArc BS C} =>
            Real.exp (-c * Qctrl BS a.val))
          <= (eta + Ctail * Real.exp (-c * C^2 / 2)) / sigmaCtrl BS
```

This is exactly what Phase C needs: choose `eta` small, then choose `C` large.

## 3. Do not prove G5 monolithically first

Ask Aristotle to create a new file, for example
`RequestProject/GlobalPeierlsBookkeeping.lean`, and prove the abstract finite
encoder before instantiating it with CRT/SBEE data.

### 3.1 Abstract inputs

For a finite interval of blocks `I`, assume:

* local finite types `A k`;
* local energies `Rk : A k -> Real`;
* global assignments are products `forall k in I, A k`;
* cold blocks have a label `label k x : Int` and an exception set;
* local fixed-label count:

```lean
fixedLabelCount k m R <= Real.exp (eps * R)
```

* local hot count, after hot absorption:

```lean
hotCount k R <= Real.exp (2 * eps * R)
```

* if adjacent cold labels disagree, the global cross-energy pays a penalty
  `Pi k`;
* label range:

```lean
abs (label k x : Real) <= L k R
```

and for non-initial segments the logarithm of the label range is paid by the
preceding hot energy or preceding boundary penalty.

The abstract theorem should conclude:

```lean
globalCount R <= exp(A * #I) * exp(8*eps*R) *
                 (1 + sqrt R / sigma0)
```

where `sigma0` is the lowest-block scale, later compared to `sigmaCtrl BS`.

This file is pure finite combinatorics: no CRT, no primes.

### 3.2 Required finite lemmas

Prove these small lemmas first.

**Weighted subset entropy.**
If weights `w k >= wmin`, costs `cost k` satisfy
`log cost k <= eps * w k / 4`, and `sum_{k in S} w k <= R`, then

```text
# {S with paid weight <= R} * product_{k in S} cost k <= exp(eps * R)
```

Formal proof: inject subsets into a weighted partition sum:

```text
1_{sum w <= R} * product cost
  <= exp(eps R / 2) * product_{k in S} exp(-eps w_k / 2) * cost_k
```

then sum over all subsets:

```text
sum_S product (cost_k * exp(-eps w_k/2))
  = product_k (1 + cost_k * exp(-eps w_k/2))
  <= exp(sum_k exp(-eps w_k/4)).
```

For dyadic weights `w_k >= c * 2^k / k^A`, the final sum is `< eps R + O(#I)`
after increasing `k0`.

Use this lemma twice:

* hot set, with weights `Rw_k`;
* mismatch boundary set, with weights `Pi_k`.

**Energy shell product.**
If local count in shell `n <= R_k < n+1` is at most
`exp(alpha*(n+1))`, then the product over blocks with
`sum R_k <= R` is at most

```text
exp(alpha * R) * exp(O_alpha(#blocks)).
```

This is just the number of weak integer compositions, absorbed into
`exp(A * #blocks)`.

**Segment construction.**
Given hot set `H` and boundary set `B`, define cold segments as maximal
connected components of the line graph on `I \ H` after cutting edges in `B`.
Prove:

* every cold block belongs to exactly one segment;
* if an adjacent cold edge is not in `B`, the two labels are equal;
* therefore labels are constant on each segment.

This is the cleanest way to formalize the decoder.

**Decoder injection.**
Define a code with fields:

```lean
structure GlobalCode where
  hotSet : Finset Nat
  hotShell : ...
  hotData : ...
  boundarySet : Finset Nat
  initialSegmentLabel : Option Int
  otherSegmentLabels : ...
  coldShell : ...
  coldFixedLabelData : ...
```

The map `encode : {a // Qctrl BS a <= R} -> GlobalCode` records:

1. hot blocks;
2. hot local assignments, or enough data to reconstruct them;
3. mismatch boundaries;
4. one common label per cold segment;
5. fixed-label cold local data.

The decoder reconstructs a global assignment block by block.  Hence `encode`
is injective.

## 4. Instantiating the abstract G5 with the current Lean files

Use existing theorems as follows.

**L1.** `SBEEAssembly.unified_levelset`.

**L2.** Cold dominant label.  From
`SBEEForcing.theorem_B_nondominant_forcing`: if
`R_k < c2 * X_k / log(X_k)^3`, then every assignment with `QP <= R_k` is
`IsDominant X_k P_k a rho`.

**L2 uniqueness.** Add a small lemma:
if `rho <= 1/4` and an assignment is both `m`-dominant and `m'`-dominant, then
`m = m'`.  Reason: two residue classes modulo a prime are disjoint unless the
integer labels agree mod that prime; the two large classes have intersection
size at least `(1-2rho)N > 0`; pick a prime in the intersection.  Since both
labels satisfy the L3 small range, `|m-m'| < p` for large blocks, so congruence
mod `p` implies equality.

**L3.** `SBEEForcing.theoremA_label_range`.

**L4.** `SBEEForcing.exception_count_bound`.
For cold `R_k < Rw_k`, this gives an absolute exception bound `e0` after the
dyadic density estimate `N_k >= X_k/(2 log X_k)`.

**L5.** Fixed-label dominant count.
Do not use the full `theorem_A_dominant_count` directly, because it includes a
label-range factor.  Instead extract the internal proof around
`dominant_encoding_card` and `exception_count_bound`:
for fixed `m`,

```lean
#{a : QP P a <= R and m-dominant} <= exp(eps * R)
```

This is exactly the `hfibcard` part inside `theorem_A_dominant_count`.
Make it standalone.

**Mismatch boundaries.** Use the already-proved
`GlobalControl.mismatch_penalty_with_exceptions`.

**Global sigma comparison.** Prove:

```lean
sigmaCtrl BS >= sigmaP (BS.P BS.k0)
sigmaP (BS.P BS.k0) >= c / (2^BS.k0 * BS.k0)
```

and for later blocks:

```lean
log (1 + sqrt R / sigmaP(P_k))
```

is paid either by hot energy or boundary penalty, except for the lowest cold
segment, which contributes the single global factor
`1 + sqrt R / sigmaCtrl BS`.

## 5. G7 proof after G5

Once G5 has the form with `exp(A*numBlocks BS)`, prove:

```text
sum_a exp(-c Qctrl a) <= C(A,c,eps) * exp(A*numBlocks BS) / sigmaCtrl BS.
```

This is exactly `SBEEAssembly.partfun_series_bound`, with

```text
C0 = exp(A*numBlocks BS)
sigma = sigmaCtrl BS
q = Qctrl BS
```

For the off-main-arc sum, prove the localization lemma:

If `a notin mainArc BS C`, then either

1. `Qctrl BS a >= F0 BS`, where

```text
F0 BS = min( min_k Rw_k, min_k Pi_k, min_k E1_k )
```

or

2. `a` is globally diagonal with label `m` and `|m| > C/sigmaCtrl BS`, hence
   `Qctrl BS a = m^2 * sigmaCtrl BS^2 > C^2`.

Then

```text
sector I <= exp(-c F0 BS / 2)
            * C(A,c,eps) * exp(A*numBlocks BS) / sigmaCtrl BS.
```

Using `admissibleGlobalRange`, prove

```text
exp(A*numBlocks BS - c*F0 BS/2) <= eta
```

for all `BS.k0 >= k0min(eta)`.

Sector II is the one-dimensional Gaussian tail:

```text
sum_{|m| > C/sigma} exp(-c*m^2*sigma^2)
  <= Ctail * exp(-c*C^2/2) / sigma.
```

This proves the final useful G7 statement:

```text
offMain <= (eta + Ctail*exp(-c*C^2/2)) / sigmaCtrl BS.
```

## 6. Phase C should be split into six named lemmas

Do not keep `exists_positive_weighted_construction` as one giant proof.  Split
`CircleMethod.lean` as follows.

**C1a: `Construction` structure.**
Fields: `BS`, `E`, `theta`, `theta in [1/3,2/3]`, `IsSemiprime`, avoids `T`,
mass identity, `sigmaE`, `sigmaE comparable sigmaCtrl`, control-pair inclusion.

**C1b: edge construction.**
May depend on the single named input
`chebyshev_block_density`.  Everything else is finite greedy mass tuning.

**C2: pointwise Fourier bound.**
Upgrade `BernoulliFourier.product_charFun_bound` from the sine version to the
CRT-energy version:

```text
|muhat h| <= exp(-(16/9) * QE(a(h))).
```

**C3: main-arc Taylor.**
State with hypotheses:

* mass identity `sum theta_e/e = 1/b`;
* `theta in [1/3,2/3]`;
* smallest edge value sufficiently large;
* `|m| <= C/sigmaE`.

Conclusion:

```text
Re (muhat(m) * exp(-2*pi*I*m/b))
  >= (1/2) * exp(-2*pi^2*m^2*sigmaE^2)
```

and summing gives `>= c3(C)/sigmaE`.

**C4: minor arc.**
Use CRT bijection, `QE >= Qctrl`, and G7:

```text
minor <= (eta + Ctail*exp(-c*C^2/2)) / sigmaCtrl
       <= (1/2)*c3(C)/sigmaE
```

by first choosing `eta`, then `C`, then `k0`.

**C5: positivity.**
Fourier inversion gives `L * Wcount = main + minor`; C3-C4 imply
`Wcount > 0`.

**C6: extraction.**
Already proved as `Wcount_pos_imp_repr`.

## 7. Copy-paste task for Aristotle

Use this as the next prompt:

```text
Continue from the latest package. Do not redo G2/G3 or the finite
GlobalAssignment interface. They are already done.

First correct the faithful statements once more:
do not use a `Cglob` chosen after `BS`, but also do not demand a single absolute
`Cglob` independent of the number of blocks. Add `numBlocks BS` and an
`admissibleGlobalRange BS` hypothesis (e.g. `BS.K <= 3*BS.k0`, or the analytic
form `log(BS.K+2) <= eta*Rw(2^BS.k0)`). Restate G5 with the uniform factor
`exp(A*numBlocks BS)`, and restate G7 in the final useful form
`offMain <= (eta + Ctail*exp(-c*C^2/2))/sigmaCtrl BS`.

Then create `GlobalPeierlsBookkeeping.lean` and prove the abstract finite
segment-encoding theorem before instantiating it with CRT. Prove, in order:
weighted subset entropy; energy shell product; cold segment construction from
hot set and boundary set; decoder injectivity; abstract global count.

After that instantiate the abstract theorem using:
L1 = `SBEEAssembly.unified_levelset`;
L2 = `SBEEForcing.theorem_B_nondominant_forcing` plus a new uniqueness lemma for
dominant labels;
L3 = `SBEEForcing.theoremA_label_range`;
L4 = `SBEEForcing.exception_count_bound`;
L5 = the fixed-label fiber bound extracted from the `hfibcard` part of
`SBEEForcing.theorem_A_dominant_count`;
boundary penalty = already-proved
`GlobalControl.mismatch_penalty_with_exceptions`.

Once G5 is proved, prove G7 by `SBEEAssembly.partfun_series_bound` plus
off-main-arc localization and the Gaussian tail. Then split
`CircleMethod.exists_positive_weighted_construction` into C1a/C1b/C2/C3/C4/C5
as described in note 37, with only `chebyshev_block_density` allowed as a named
external input if Mathlib lacks it.

Keep all hypotheses faithful. If a step fails, report the exact theorem whose
statement is too strong or whose hypothesis is missing; do not close anything
by choosing constants after the object being counted.
```
