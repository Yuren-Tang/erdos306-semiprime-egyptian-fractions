# Clean math problem: the "extra-light" bound `∑_extra 1/e² ≤ 3σ²`

Self-contained statement + minimal environment closure, for independent work.
(R2 arc construction, the one genuine analytic residual. Everything else in the closing is
formalization engineering.) Last updated 2026-06-17.

---

## 0. The setup (a "block-structured prime set")

Fix integers `k0, K` with **`k0 ≥ 14`** and **`2·k0 ≤ K ≤ 3·k0`**.
For each `k0 ≤ k ≤ K` we are given a finite set of primes `P_k` ("the block at scale k") with:

- **(window)** every `p ∈ P_k` satisfies `2^k ≤ p < 2^{k+1}`;
- **(density, lower)** `|P_k| ≥ 2^k / (2 k log 2)`.  [Rosser–Schoenfeld; an axiom in the project.]

Also available, a matching **upper** count on the full dyadic block (all primes in `[2^k,2^{k+1})`):

- **(density, upper)** `k · #{primes in [2^k, 2^{k+1})} ≤ 2^{k+2}`, hence `|P_k| ≤ 2^{k+2}/k`.

Write `B := ⋃_{k=k0}^{K} P_k` (the "block support"). All `p ∈ B` are primes in `[2^{k0}, 2^{K+1})`.

**Control deviation.** Define `σ ≥ 0` by
```
σ²  :=  ∑_{k=k0}^{K}  ∑_{ {p,q} ⊆ P_k, p<q }  1/(pq)²            (internal, within-block pairs)
        +  ∑_{k=k0}^{K-1}  ∑_{ p ∈ P_k, q ∈ P_{k+1} }  1/(pq)²    (bipartite, ADJACENT-block pairs).
```
Call the index set of these pairs `Ctrl ⊆ { {p,q} : p≠q ∈ B }`.  Note **`Ctrl` omits every pair
whose two primes lie in blocks ≥ 2 apart.** Call those omitted pairs `NonAdj`:
```
NonAdj := { {p,q} : p ∈ P_j, q ∈ P_k, j + 2 ≤ k }.
```
So `{pairs of B} = Ctrl ⊔ NonAdj` (disjoint union).

## 1. The two "extra" edge families

- **Mass batch `Q`.** A finite set of integers, each of the form `e = p·q` with `{p,q} ⊆ B`, `p<q`.
  *Crucial structural fact (given):* `Q` is **disjoint from the control edges**, i.e. no `e ∈ Q`
  equals `p·q` for a control pair `{p,q} ∈ Ctrl`. By unique factorization of a semiprime, this means
  **every pair underlying `Q` lies in `NonAdj`** (blocks ≥ 2 apart). (`Q` also satisfies a *linear*
  load window `3/(2b) ≤ ∑_{e∈Q} 1/e + (base) < 3/b`, but you should NOT need it — the `1/e²` control
  must come from the pair structure.)
- **Gadget edges.** `{ r·s : r ∈ R, s ∈ S }`, where `R` is a set of `≤ b` primes each `≥ 2`,
  `S ⊆ P_{2k0}` (so every `s ∈ S` has `s ≥ 2^{2k0}`), and `|S| ≤ k0/1000`. (Here `b ≥ 3`,
  `b ≤ k0/1000`.) These are tiny because `s ≥ 2^{2k0}`.

## 2. The target inequality (this is what must be proved)

```
        ∑_{e ∈ Q} 1/e²   +   ∑_{r∈R, s∈S} 1/(rs)²   ≤   3 σ².
```

## 3. Recommended route (comfortable margin — NOT the borderline one)

Because `Q`'s pairs lie in `NonAdj`, `∑_{e∈Q} 1/e² ≤ ∑_{{p,q}∈NonAdj} 1/(pq)²`. So it suffices to prove:

> **(★)  `∑_{{p,q} ∈ NonAdj} 1/(pq)²  ≤  2 σ²`**  (then gadget `≤ σ²` — see §4 — gives total `≤ 3σ²`).

Heuristic sizes (PNT) showing (★) holds with **room** (true ratio ≈ ¼, not 2):
- internal sum of block `j`:  `≈ ½|P_j|² 2^{-4j} ≈ 2^{-2j}/(2 j² log²2)`;
- adjacent sum (j,j+1):  `≈ |P_j||P_{j+1}| 2^{-2j}2^{-2(j+1)} ≈` same order as internal_j;
  so `σ² ≈ 2·∑_j internal_j`;
- non-adjacent from block `j`:  `= (∑_{p∈P_j} 1/p²)·(∑_{k≥j+2}∑_{q∈P_k} 1/q²)`; the tail
  `∑_{k≥j+2}∑_{P_k}1/q² ≤ ∑_{k≥j+2}|P_k|2^{-2k}` is geometric, dominated by `k=j+2`, giving
  non-adj_j `≈ ½ internal_j`.  Hence `∑ NonAdj ≈ ¼ σ²`.

The clean way to prove (★) rigorously:
- **Upper-bound `∑NonAdj` by a geometric series** using the density-UPPER count `|P_k| ≤ 2^{k+2}/k`
  and `q ≥ 2^k`: `∑_{q∈P_k}1/q² ≤ |P_k|2^{-2k} ≤ 4/(k 2^k)`. Then
  `∑NonAdj = ∑_j (∑_{p∈P_j}1/p²)(∑_{k≥j+2} ∑_{P_k}1/q²) ≤ ∑_j (∑_{P_j}1/p²)·∑_{k≥j+2} 4/(k2^k)`.
- **Lower-bound `σ²`** by the internal sum of a single block (say block `j`), using the
  density-LOWER count `|P_j| ≥ 2^j/(2 j log2)` and `p < 2^{j+1}`:
  `internal_j = ½[(∑_{P_j}1/p²)² − ∑_{P_j}1/p⁴] ≥ …`.
- Combine block-by-block: show non-adj_j ≤ (const < 2)·(internal_j + adjacent_j), sum over j.
  The geometric tail makes each step lose only a bounded factor, so the constant is uniform.

## 4. The gadget term (easy, for completeness)
`∑_{r∈R,s∈S} 1/(rs)² ≤ (∑_{r∈R} 1/r²)(∑_{s∈S} 1/s²) ≤ (b)(1/4)·(|S| · 2^{-4k0}) ≤ σ²`
since `s ≥ 2^{2k0}`, `|S| ≤ k0`, and `σ² ≥ internal_{k0} ≥ ~2^{-2k0}/(k0² )` (dominates the
`2^{-4k0}` gadget by a factor `2^{2k0}`). Already handled crudely in the codebase
(`r2_extra_inv_sq_le` gives gadget `≤ ½σ²` with room).

## 5. What the project already has (so you know the available toolbox)
- density LOWER `|P_k| ≥ 2^k/(2k log2)` — `BlockSystem.hdensity` / axiom `dyadic_prime_density`.
- density UPPER `k|P_k| ≤ 2^{k+2}` — `dyadic_block_card_upper` (R2TopAssembly:447, proved via
  Mathlib `primorial_le_4_pow`).
- `σ² = ∑_{Ctrl} 1/(pq)²` exactly — `sum_inv_sq_ctrlEdges_eq_sigmaCtrl_sq`.
- a LOOSE lower bound `σ ≥ 1/(100 k0 2^{k0})` — `sigmaCtrl_ge_strong` (≈100× below truth; the
  tight version, if you want it, is `σ ≥ ~1/(8 k0 2^{k0})` from `internal_{k0}` + hdensity).
- the per-set square identity `(∑x)² = ∑x² + 2∑_{p<q} x_p x_q` — `sq_sum_eq_sum_sq_add_two_sum_lt`.
- a LOOSE block-support sum `∑_{p∈B}1/p² ≤ 8/(k0 2^{k0})` — `r2_blockSupport_inv_sq_le`.

## 6. Why I did not just prove it
The DIRECT route `∑_Q ≤ (∑_{p∈B}1/p²)² = 2σ² + ∑1/p⁴ + 2∑NonAdj` is asymptotically TIGHT
(`≈ 3σ²`, no margin) and the available constants are ~800× loose, so it is risky. The route in §3
(via `Q ⊆ NonAdj`, then (★)) has a real ~12× margin but requires the block-by-block geometric
comparison — a genuine (if elementary) estimate I want done carefully rather than hand-waved.
The single mathematical crux is **(★)**: `∑_{NonAdj} 1/(pq)² ≤ 2σ²`.
