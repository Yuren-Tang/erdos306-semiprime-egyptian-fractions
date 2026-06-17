# Aristotle append: close G5, G7, and Phase C

Append this to the current Aristotle conversation.  The goal is not to
rediscover the proof, but to translate the following proof into the existing
files `GlobalControl.lean` and `CircleMethod.lean`, keeping the build green.

## 0. First fix the faithful finite interface

Before proving G5, fix the type of global assignments.  The current skeleton
uses `(p : Nat) -> ZMod p` and then counts such functions.  That is not the
faithful object: outside the block support there are infinitely many irrelevant
coordinates.  Do not prove the old statement by an artifact of `Set.ncard`.

Define
```lean
def blockSupport (BS : BlockSystem) : Finset Nat :=
  (Finset.Icc BS.k0 BS.K).biUnion (fun k => BS.P k)

abbrev GlobalAssignment (BS : BlockSystem) :=
  (p : {p : Nat // p in blockSupport BS}) -> ZMod p.1
```
and rewrite `Hglob`, `Qctrl`, `sigmaCtrl`, `mainArc`, `global_levelset`, and
`global_control_partition` over `GlobalAssignment BS`.  For a control pair
`pq in ctrlPairs BS`, obtain membership of `pq.1` and `pq.2` in
`blockSupport BS` from the definition of `ctrlPairs`; then evaluate the
assignment on the corresponding subtype elements.

Also prove or assume as large-scale hypotheses:

* `0 < sigmaCtrl BS`;
* `sigmaCtrl BS <= 1`;
* the usual large-start condition `BS.k0 >= k0(eps)` and mild range condition
  on `BS.K` used in note 34, e.g. `log (BS.K+2) <= eps * Rw(2^BS.k0)`.

The latest package already proves G2 and the corrected no-exception G3.  Do not
redo them.  But G5 needs the exceptional form of G3, because cold blocks have a
bounded exception set.  The current `mismatch_penalty` assumes every vertex in
the two blocks has the label.  Derive the following corollary from the already
proved `mismatch_per_q`, rerunning the same summation over `P_k \ Ek` and
`P_{k+1} \ Ek1`:
```lean
theorem mismatch_penalty_with_exceptions
  (Ek : Finset Nat) (Ek1 : Finset Nat)
  (hEk : Ek subset BS.P k) (hEk1 : Ek1 subset BS.P (k+1))
  (hEk_card : Ek.card <= e0) (hEk1_card : Ek1.card <= e0)
  (hlabel_k : forall p in BS.P k \ Ek, a p = (m : ZMod p))
  (hlabel_k1 : forall q in BS.P (k+1) \ Ek1, a q = (m' : ZMod q))
  (hmm : m != m') :
  Pi k <= bipartite cross energy
```
with a lavish constant, say `Pi k = N_{k+1} * N_k^3 / (2^20 * X_k^2)`.
The old no-exception theorem is the special case `Ek = Ek1 = empty`.

## 1. G5: global level-set theorem

Use the following single-block inputs, extracted from the verified SBEE files:

* L1: block level-set bound
  `#{a_k : QP(a_k) <= R_k} <= C_eps * exp(eps * R_k) *
  (1 + sqrt R_k / sigma_k)`.
* L2: if `R_k < Rw(X_k)` then the block has a unique dominant integer label
  `m_k`.
* L3: label range
  `|m_k| <= A * sqrt(R_k) / sigma_k`.
* L4: exception set
  `E_k = {p in P_k : a_p != m_k mod p}` satisfies
  `E_k.card <= R_k / E1(X_k)`, hence for cold blocks `E_k.card <= e0`.
* L5: for fixed label `m_k`, the number of dominant assignments in block `k`
  with energy `<= R_k` is `<= exp(eps * R_k)`.

Let `a : GlobalAssignment BS` satisfy `Qctrl BS a <= R`.  Put
`R_k = QP (a restricted to P_k)`.  Since internal control pairs are included in
`ctrlPairs`, `sum_k R_k <= Qctrl BS a <= R`.

Define a block to be hot if `R_k >= Rw(X_k)` and cold otherwise.

The encoding of `a` records:

1. The hot set `H`.  Since every hot block contributes at least
   `Rw_min = Rw(2^BS.k0)` and `sum_k R_k <= R`,
   `H.card <= R / Rw_min`.  Hence the number of possible hot sets is at most
   `exp(eps * R)` for large `BS.k0`, because
   `log (#blocks+1) <= eps * Rw_min`.

2. The hot block assignments.  By L1 plus hot absorption G4,
   each hot block contributes at most `exp(2 eps R_k)`.  Multiplying over hot
   blocks gives at most `exp(2 eps R)`.

3. The mismatch boundary set
   `B = {k : k,k+1 cold and m_k != m_{k+1}}`.
   The cross pair sets for distinct `k` are disjoint.  By
   `mismatch_penalty_with_exceptions`, every `k in B` contributes at least
   `Pi_k >= Pi_min` to `Qctrl`.  Therefore `B.card <= R / Pi_min`, and the
   number of possible boundary sets is at most `exp(eps * R)` for large
   `BS.k0`.

4. Cold segment labels.  Remove the hot blocks and cut cold runs at each
   boundary in `B`.  On every remaining cold segment all adjacent cold labels
   agree, hence the whole segment has one common label.

   The segment containing the lowest cold block pays the only global Gaussian
   factor.  By L3 and `sum R_k <= R`,
   `|m| <= A' * sqrt R / sigmaCtrl BS`, so it has at most
   `C * (1 + sqrt R / sigmaCtrl BS)` choices.

   Every other segment starts immediately after a hot block or a mismatch
   boundary.  Its label range has logarithmic size
   `O(k + log(1+R))`, while the preceding hot block or boundary carries energy
   at least `Rw(2^(k-1))` or `Pi_(k-1)`, both much larger than that entropy for
   large `BS.k0`.  Summing over all such starts gives at most
   `exp(2 eps R)` possible labels.

5. The cold block data once the segment label is known.  By L5, the product over
   cold blocks is at most `exp(eps * sum_cold R_k) <= exp(eps * R)`.

The decoder is injective: from the hot set and hot data we recover every hot
block; from `B` and the segment labels we know the dominant label of every cold
block; from the cold block data (equivalently the exception bookkeeping used in
L5) we recover each cold block.  Thus the global assignment is recovered block
by block.

Multiplying the five factors gives
```text
N_glob(R) <= Cglob * exp(8 * eps * R) *
             (1 + sqrt R / sigmaCtrl BS).
```
The constant `Cglob` absorbs fixed powers depending on the number of blocks and
the single-block constants.  This is `global_levelset`.

Formalization hint: model the encoder as a sigma-type of the five data items
and use the same pattern as `SBEEFingerprint.decoding_card_bound`:
construct a map from assignments with `Qctrl <= R` into the code space and prove
it injective; then multiply cardinal bounds for the factors.

## 2. G7: global control partition

First prove a reusable Laplace lemma.

If a finite type `A` has energy `Q : A -> Real` and
```text
N(R) = #{a : A | Q a <= R}
N(R) <= Cglob * exp(alpha * R) * (1 + sqrt R / sigma)
```
for all `R >= 1`, with `0 < sigma <= 1` and `alpha < c`, then
```text
sum_a exp(-c * Q a) <= C1 / sigma.
```
Proof: split into shells `n <= Q a < n+1`.  The shell size is at most `N(n+1)`.
Hence the sum is bounded by
```text
N(1) + sum_{n>=1} exp(-c*n) * N(n+1)
 <= Cglob * exp(alpha) *
    sum_{n>=0} exp(-(c-alpha)*n) * (1 + sqrt(n+1)/sigma)
 <= C1 / sigma,
```
because the numerical series converges and `sigma <= 1`.

Apply this lemma to G5 with `alpha = 8 eps` and choose `eps < c/16`.  This gives
the first partition bound.

For the off-main-arc bound, prove G6 localization:
if `a` is not in `mainArc BS C`, then either

* sector I: a hot block, a cold exception, or a cold mismatch boundary occurs,
  and therefore `Qctrl BS a >= F0`, where
  `F0 = min(Rw_min, E1_min, Pi_min)`;
* sector II: no hot block, no exception, and no mismatch boundary occurs.  Then
  every block is cold, all labels are equal, and there are no exceptions, so
  `a` is globally diagonal with some integer label `m`.  Since `a` is not in
  `mainArc BS C`, `|m| > C / sigmaCtrl BS`, and
  `Qctrl BS a = m^2 * sigmaCtrl BS^2 > C^2`.

For sector I:
```text
sum_sectorI exp(-c Q) <= exp(-c F0/2) * sum_a exp(-(c/2) Q)
                     <= exp(-c F0/2) * C1 / sigmaCtrl.
```

For sector II, the map `a -> m` is injective and
`Qctrl(a) = m^2 sigmaCtrl^2`, so the Gaussian tail gives
```text
sum_{|m| > C/sigma} exp(-c m^2 sigma^2)
  <= C2 * exp(-c C^2 / 2) / sigma.
```
This is the elementary integral comparison:
`sum_{n>N} exp(-c n^2 sigma^2) <=
 integral_{N-1}^\infty exp(-c x^2 sigma^2) dx`, and for `N >= C/sigma`,
the tail is `<= const * exp(-c C^2/2)/sigma`.

Combining the two sectors proves
```text
sum_{a notin mainArc BS C} exp(-c * Qctrl BS a)
 <= (Cglob * exp(-c*F0/2) + C1 * exp(-c*C^2/2)) / sigmaCtrl BS.
```
This is `global_control_partition`.

## 3. Phase C: circle method closure

Introduce a faithful construction structure:
```lean
structure Construction (T : Finset Nat) (b : Nat) where
  BS : GlobalControl.BlockSystem
  E : Finset Nat
  theta : Nat -> Real
  htheta : forall e in E, (1/3 : Real) <= theta e /\ theta e <= 2/3
  hsemi : forall e in E, IsSemiprime e
  havoid : forall e in E, e notin T
  hmass : (sum e in E, theta e / (e:Real)) = 1 / (b:Real)
  hsigma_comp : sigmaE E theta comparable_to GlobalControl.sigmaCtrl BS
  hctrl_subset : every control pair value p*q belongs to E
```
where
`sigmaE^2 = sum_{e in E} theta e * (1 - theta e) / e^2`.

### C1. Edge construction

Use the Chebyshev block-density theorem
```text
chebyshev_block_density :
  for all x >= x0, #{p prime : x <= p < 2x} >= x / (2 log x).
```
If Mathlib lacks this, isolate it as the single named external input with the
standard elementary proof path by Chebyshev's binomial-coefficient argument.

Choose `k0` so large that all primes in all new dyadic blocks exceed
`max(T union primeFactors(b))`, except for the deliberate gadget primes dividing
`b`.  Build the block system from all primes in each dyadic window
`[2^k,2^(k+1))`; Chebyshev gives the density hypothesis.

Include all control-pair semiprimes `p*q` from internal and consecutive control
pairs, with initial weight `theta = 1/2`.  For each prime `r | b`, choose a fresh
huge prime `s_r` and include the gadget semiprime `r*s_r`, also with
`theta = 1/2`.  Choose the `s_r` so large that every gadget value avoids `T` and
the total gadget mass and variance are negligible.  The gadgets ensure `b | L`,
where `L` is the product of all primes appearing in edges.

Let
```text
M0 = sum_{control and gadget edges e} (1/2)/e.
```
By increasing `k0` and the gadget primes, make `M0 < 1/(4b)`.  Put
`Delta = 1/b - M0`.

Now choose a high-scale reservoir of semiprime edges, disjoint from all previous
edges and using primes far beyond the control blocks.  Since the sum of
reciprocals of primes diverges, the sum of reciprocals of available semiprime
edges in a sufficiently long high-scale reservoir exceeds `3 Delta`, while each
individual reciprocal is `< Delta`.  Greedily select a finite batch `H` until
the sum
```text
W_H = sum_{e in H} 1/e
```
first exceeds `2 Delta`.  Then `2 Delta <= W_H <= 3 Delta`.  Set
`theta_e = Delta / W_H` for all `e in H`.  Thus
`theta_e in [1/3,1/2]` and
```text
M0 + sum_{e in H} theta_e/e = M0 + Delta = 1/b.
```
All weights are in `[1/3,2/3]`; all values are distinct squarefree semiprimes
avoiding `T`.

Place the reservoir so high that
```text
sum_{e in H} 1/e^2 <= (max_{e in H} 1/e) * W_H = o(sigmaCtrl^2),
```
and similarly for gadgets.  Therefore
`sigmaE^2 = sigmaCtrl^2 * (1 + o(1))`, so in particular
`sigmaE` and `sigmaCtrl` are comparable and `sigmaE -> 0`.

### C2. Pointwise Fourier bound

For `h mod L`, let `a(h)_p = h mod p`.  For each edge `e = p*q`, the phase
`h/e mod 1` equals `H_{pq}(a(h))/(p*q) mod 1`, where `H_{pq}` is the centered CRT
representative.  Therefore
```text
|1 - theta_e + theta_e exp(2 pi i h/e)|^2
 = 1 - 4 theta_e(1-theta_e) sin^2(pi h/e).
```
Since `theta_e in [1/3,2/3]`, `theta_e(1-theta_e) >= 2/9`; and
`sin^2(pi t) >= 4 ||t||^2` for `||t|| <= 1/2`.  Hence
```text
|1 - theta_e + theta_e exp(2 pi i h/e)|
 <= exp(-(16/9) * (H_{pq}(a(h))/(p*q))^2).
```
Multiplying over `e in E` gives
```text
|muhat(h)| <= exp(-(16/9) * Q_E(a(h))).
```
Since control edges are included in `E`, `Q_E(a) >= Qctrl(a)`.

### C3. Main arc

For `h` in the main arc, `a(h)` is globally diagonal with label `m` and
`|m| <= C/sigmaE`.  For each edge `e`, the phase is `m/e`.

Use the Taylor expansion, uniformly for `|m|/e <= 1/10`,
```text
log(1 - theta + theta exp(2 pi i m/e))
 = 2 pi i theta m/e
   - 2 pi^2 theta(1-theta) m^2/e^2
   + O(|m|^3/e^3 + |m|^4/e^4).
```
Summing over edges, the linear term is
`2 pi i m * sum theta_e/e = 2 pi i m/b`, which cancels exactly against the
external factor `exp(-2 pi i m/b)` in Fourier inversion.  The quadratic term is
`-2 pi^2 m^2 sigmaE^2`.  The total error is
```text
O(|m|^3 sum_e e^{-3} + |m|^4 sum_e e^{-4}) = o(1)
```
because the smallest edge tends to infinity and `|m| <= C/sigmaE`.  For `k0`
large, the error has absolute value at most `1/10`, so
```text
Re( muhat(m) * exp(-2 pi i m/b) )
 >= (1/2) * exp(-2 pi^2 m^2 sigmaE^2).
```
Therefore
```text
sum_{h in main arc} muhat(h) exp(-2 pi i h/b)
 >= c3(C) / sigmaE
```
with `c3(C) > 0`; for fixed sufficiently large `C`, take a concrete positive
constant from the Gaussian Riemann-sum lower bound.

### C4. Minor arc

The CRT map `h mod L -> a(h)` is a bijection from `ZMod L` to the product of the
local residue rings over primes appearing in edges.  Hence, using C2 and
`Q_E >= Qctrl`,
```text
sum_{h outside main arc} |muhat(h)|
 <= sum_{a outside mainArc} exp(-(16/9) * Qctrl(a)).
```
Apply G7 with `c = 16/9`:
```text
minor <= (Cglob exp(-(16/9)F0/2)
          + C1 exp(-(16/9)C^2/2)) / sigmaCtrl.
```
By the construction, `sigmaE` and `sigmaCtrl` are comparable.  First choose
`k0` large so that the `exp(-F0)` term is smaller than
`c3(C)/(4 sigmaE)`, then choose `C` large so that the Gaussian tail is also
smaller than `c3(C)/(4 sigmaE)`.  Thus the whole minor arc is at most
`(1/2)c3(C)/sigmaE`.

### C5. Positivity and extraction

Fourier inversion gives
```text
L * Wcount E theta b
 = main_arc_contribution + minor_arc_contribution.
```
By C3 and C4 the real part is positive:
```text
L * Wcount E theta b >= c3(C)/sigmaE - (1/2)c3(C)/sigmaE > 0.
```
So `Wcount E theta b > 0`.  The already proved
`Wcount_pos_imp_repr` extracts a subset `S subset E` with
`sum_{e in S} 1/e = 1/b`.  Since every `e in E` is a distinct squarefree
semiprime avoiding `T`, this proves
```lean
CircleMethod.exists_positive_weighted_construction
```
and hence closes `fourier_positivity_unconditional` through
`CircleMethod.circle_method_positivity`.

## 4. What to report

Close in this order:

1. finite `GlobalAssignment` refactor;
2. L2-L5 extraction lemmas from the verified single-block package;
3. exceptional corollary of the already-proved G3, using `mismatch_per_q`;
4. `global_levelset`;
5. `global_control_partition`;
6. `exists_positive_weighted_construction`.

If a terminal external theorem is needed, it should be only
`chebyshev_block_density`, explicitly named and documented.  Do not leave G5,
G7, C2, C3, C4, or C5 as sorries; those are exactly the tasks above.
