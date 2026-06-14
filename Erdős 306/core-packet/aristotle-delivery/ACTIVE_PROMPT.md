# Aristotle task — R2-mass: block-aligned mass batch (note 50 §2/§6)

Work in this folder as the Lake project root. Before building run
`lake exe cache get` (Mathlib cache), then `lake build RequestProject.BlockMassPool`.

## Goal

Extend `RequestProject/BlockMassPool.lean` (keep it building, no `sorry` unless
isolated and named) to produce a **block-aligned mass batch**: a finite set of
squarefree semiprimes, each a product of two distinct *block* primes, avoiding a
finite obstruction set, whose reciprocal load lands in the common-θ window
`[3/(2b), 3/b]` for squarefree `b ≥ 3`. This is the `R2-mass` input to the R2
construction `CircleMethod.exists_arcConstruction`.

## What is already proved (use, do not reprove)

In `BlockMassPool.lean`:
```lean
lemma sq_sum_eq_sum_sq_add_two_sum_lt {α : Type*} [LinearOrder α]
    (s : Finset α) (x : α → ℝ) :
    (∑ p ∈ s, x p) ^ 2
      = (∑ p ∈ s, (x p) ^ 2)
        + 2 * ∑ pq ∈ s.offDiag.filter (fun pq => pq.1 < pq.2), x pq.1 * x pq.2
```
In `BlockSystemConstruction.lean` (`GlobalControl` namespace):
```lean
def dyadicBlock (k : ℕ) : Finset ℕ := (Finset.Ico (2^k) (2^(k+1))).filter Nat.Prime
axiom dyadic_mertens_cumulative :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
      (21 : ℝ)/20 ≤ ∑ p ∈ (Finset.Icc k0 (3*k0)).biUnion dyadicBlock, (1:ℝ)/(p:ℝ)
```
In `CircleMethodConstruction.lean`: `exists_finset_primes_recip_between` — a
greedy "minimal subset hitting `[target, target+gap]`" pattern (powerset filter +
`exists_minimalFor`). **Mirror this pattern** for the greedy step below.

## Targets (in order; each a named lemma)

Let `blockPrimes k0 : Finset ℕ := (Finset.Icc k0 (3*k0)).biUnion dyadicBlock`.

**T1 — `blockPrimes_sub_sq_tail`** (S₂ small). For `5 ≤ k0`:
```lean
∑ p ∈ blockPrimes k0, (1:ℝ)/(p:ℝ)^2 ≤ 1/((2^k0 : ℝ) - 1)
```
Hint: every `p ∈ blockPrimes k0` has `2^k0 ≤ p`, and `blockPrimes k0 ⊆
Finset.Ico (2^k0) (2^(3*k0+1))`. Bound term-by-term `1/p² ≤ 1/(p*(p-1)) =
1/(p-1) - 1/p` (over ℝ, `p ≥ 2`), enlarge the index set to that `Ico`, and
telescope (cast to ℝ, `g n = 1/((n:ℝ)-1)`).

**T2 — `blockPrimes_product_load_ge`** (product-load ≥ 1/2):
```lean
∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
  (1:ℝ)/2 ≤
    ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2),
      (1:ℝ)/((pq.1 : ℝ) * (pq.2 : ℝ))
```
Proof: take `k1 = max k1₀ K` from `dyadic_mertens_cumulative`, `K` large enough
that `1/(2^k0−1) ≤ 1/10`. Apply `sq_sum_eq_sum_sq_add_two_sum_lt` with
`s = blockPrimes k0`, `x p = 1/p`. With `S := ∑ 1/p ≥ 21/20` and `S₂ ≤ 1/10`
(T1), the off-diagonal `<`-sum `= (S² − S₂)/2 ≥ ((21/20)² − 1/10)/2 =
(1.1025 − 0.1)/2 > 1/2`. (Note `x pq.1 * x pq.2 = 1/(pq.1*pq.2)`.)

**T3 — `exists_blockAligned_mass_batch`** (greedy window). For squarefree `b ≥ 3`,
finite `T`:
```lean
∃ (k0 : ℕ) (Q : Finset ℕ),
  (∀ e ∈ Q, ∃ p q, p ∈ blockPrimes k0 ∧ q ∈ blockPrimes k0 ∧ p < q ∧ e = p*q) ∧
  (∀ e ∈ Q, e ∉ T) ∧
  3/(2*(b:ℝ)) ≤ ∑ e ∈ Q, (1:ℝ)/(e:ℝ) ∧ ∑ e ∈ Q, (1:ℝ)/(e:ℝ) ≤ 3/(b:ℝ)
```
Proof: the pool `P := ((blockPrimes k0).offDiag.filter (·.1<·.2)).image
(fun pq => pq.1 * pq.2)` has `∑_{e∈P} 1/e ≥ 1/2 ≥ 3/(2b)` (T2 + injective
product map on distinct-prime pairs — see `ctrlPairs_prod_injOn` for the pattern),
each `1/e ≤ 1/4^{k0} < gap` for `k0` large, and each `e = pq ≥ 4^{k0} > max T` so
`e ∉ T`. Then take the minimal subset hitting `[3/(2b), 3/b]` exactly as
`exists_finset_primes_recip_between` does. (`b ≥ 3` ⇒ `3/(2b) ≤ 1/2 ≤ pool`;
`b=3` is the tight case `3/(2·3)=1/2`.)

## Binding rules

Do not weaken statements or hide constants. If a step resists, isolate it as a
precisely named `sorry` with a one-line reason and keep the build green. Report:
files changed, lemma names proved, `lake build RequestProject.BlockMassPool`
result, and `#print axioms` for T2 and T3.

Background: notes `50 R2 Construction Resolved …` (§2/§6) and `35 Circle Method`.
This batch feeds the R2 assembly; the parallel piece (extra-minor gadget damping)
is being done separately — **do not** attempt the full `exists_arcConstruction`.
