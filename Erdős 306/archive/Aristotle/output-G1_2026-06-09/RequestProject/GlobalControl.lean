/-
# Global Control — translation of note `34` (Phase G)

This file translates note `34` ("Global Control: Detailed Proof"), the
block-to-global chain (CP 03 §§5–8 / Prop 8.1).  The argument mirrors the
verified single-block proof one level up: *blocks* play the role *vertices*
played inside a block, and the deterministic dispersion (`lemmaD` pattern)
suffices because the Peierls penalties exceed the entropies.

## Section map (note 34)

* **G0** — `BlockSystem`, control pairs, the global control energy `Qctrl` and
  deviation `sigmaCtrl`.  The bridge lemma `BlockSystem.irvingGood` (each block
  is `IrvingGood`) is **proved**.
* **G2** — cross-block dispersion (`crossblock_dispersion`).  Self-contained
  number theory; **named `sorry`** (deterministic, `lemmaD` pattern; fiber ≤ 1).
* **G3** — mismatch penalty `Πₖ` (`mismatch_penalty`).  **Named `sorry`**.
* **G5** — global level-set theorem (`global_levelset`).  **Named `sorry`**
  (the segment encoding; the entire "Peierls" content).
* **G7** — Prop 8.1, the global control partition bound
  (`global_control_partition`).  **Named `sorry`** (Laplace step on G5).

These results feed the minor-arc bound of the circle method (note 35 C4,
`CircleMethod.exists_positive_weighted_construction`).

## Status

This is a faithful Phase-G skeleton: the `BlockSystem` data, the `IrvingGood`
bridge (proved), and the headline theorems G2/G3/G5/G7 stated with
precisely-named `sorry`s, each with a one-line reason.  No new analytic input is
required beyond the verified single-block package (`SBEEAssembly`) and `lemmaD`.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEAssembly

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ## G0. Distance to the nearest integer -/

/-- Distance from a real to the nearest integer, `‖x‖ = |x - round x|`. -/
def nndist1 (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma nndist1_nonneg (x : ℝ) : 0 ≤ nndist1 x := abs_nonneg _

lemma nndist1_le_half (x : ℝ) : nndist1 x ≤ 1 / 2 := by
  simpa [nndist1] using abs_sub_round x

/-! ## G0. Block systems -/

/-- A **block system** (note 34 G0): for each scale `k ∈ [k₀, K]` a block `Pₖ`
    of primes in the dyadic window `[2ᵏ, 2ᵏ⁺¹)` of near-maximal density
    `|Pₖ| ≥ 2ᵏ/(2·log 2ᵏ)`.  Different windows are disjoint. -/
structure BlockSystem where
  k0 : ℕ
  K : ℕ
  hk : k0 ≤ K
  hk0 : 1 ≤ k0
  P : ℕ → Finset ℕ
  hprime : ∀ k, ∀ p ∈ P k, Nat.Prime p
  hwindow : ∀ k, ∀ p ∈ P k, 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)
  hdensity : ∀ k, k0 ≤ k → k ≤ K →
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ (P k).card

/-- **G0 bridge lemma.**  Every block of a block system is `IrvingGood`
    (the regime hypothesis of the verified single-block package).  This connects
    the global layer to `SBEEAssembly.single_block_counting`. -/
theorem BlockSystem.irvingGood (BS : BlockSystem) (k : ℕ)
    (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K) :
    SBEEAssembly.IrvingGood (BS.P k) := by
  refine ⟨2 ^ k, by positivity, ?_, ?_⟩
  · intro p hp
    refine ⟨BS.hprime k p hp, (BS.hwindow k p hp).1, ?_⟩
    have := (BS.hwindow k p hp).2
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  · simpa using BS.hdensity k hk1 hk2

/-! ## G0. Global control energy

For a global assignment `a : ∀ p, ZMod p`, the CRT representative of a control
pair `{p,q}` is `crtRepr p q (a p) (a q)`.  The control-pair energy `Qctrl`
sums `(H_{pq}/(pq))²` over internal pairs (within a block) and consecutive
bipartite pairs (between `Pₖ` and `Pₖ₊₁`); `sigmaCtrl²` is the same sum with
numerator `1`. -/

/-- Global CRT representative of a control pair under a global assignment. -/
def Hglob (a : (p : ℕ) → ZMod p) (p q : ℕ) : ℤ := crtRepr p q (a p) (a q)

/-- The internal control pairs of block `k` (unordered, `p < q`). -/
def internalPairs (BS : BlockSystem) (k : ℕ) : Finset (ℕ × ℕ) :=
  ((BS.P k) ×ˢ (BS.P k)).filter fun pq => pq.1 < pq.2

/-- The consecutive bipartite control pairs between blocks `k` and `k+1`. -/
def bipartitePairs (BS : BlockSystem) (k : ℕ) : Finset (ℕ × ℕ) :=
  (BS.P k) ×ˢ (BS.P (k + 1))

/-- All control pairs of the block system (note 34 G0):
    internal complete graphs + full bipartite between consecutive blocks. -/
def ctrlPairs (BS : BlockSystem) : Finset (ℕ × ℕ) :=
  (Finset.Icc BS.k0 BS.K).biUnion (fun k => internalPairs BS k) ∪
  (Finset.Ico BS.k0 BS.K).biUnion (fun k => bipartitePairs BS k)

/-- The global control energy `Qctrl(a) = ∑_{ctrl pairs} (H_{pq}/(pq))²`. -/
def Qctrl (BS : BlockSystem) (a : (p : ℕ) → ZMod p) : ℝ :=
  ∑ pq ∈ ctrlPairs BS,
    ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2

/-- The global control deviation `sigmaCtrl = √(∑ 1/(pq)²)`. -/
def sigmaCtrl (BS : BlockSystem) : ℝ :=
  Real.sqrt (∑ pq ∈ ctrlPairs BS, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2)

lemma Qctrl_nonneg (BS : BlockSystem) (a : (p : ℕ) → ZMod p) : 0 ≤ Qctrl BS a :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma sigmaCtrl_nonneg (BS : BlockSystem) : 0 ≤ sigmaCtrl BS := Real.sqrt_nonneg _

/-! ## G2. Cross-block dispersion (note 34 G2)

The deterministic dispersion engine, one level up.  Because the window `[X,2X)`
has length `≤ q/2`, each residue class mod `q` meets it in at most one prime, so
the "fiber ≤ 1" form of `lemmaD` applies directly. -/

/-- **G2 (cross-block dispersion).**  For `P ⊆ primes ∩ [X, 2X)`, a prime
    `q ∈ [2X, 4X)`, and `d ≠ 0` with `q ∤ d`, the reciprocal-phase energy
    `∑_{p∈P} ‖d·p⁻¹/q‖²` is bounded below by `|P|³/(2¹¹X²)`.

    `pinv p` denotes the inverse of `p` modulo `q` (as an integer in `[0,q)`).

    **Status**: named `sorry` — deterministic, follows the `lemmaD` pattern with
    fiber ≤ 1 (interval length ≤ modulus/2). -/
theorem crossblock_dispersion (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hd : d ≠ 0) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    (P.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ^ 2 := by
  sorry

/-! ## G3. Mismatch penalty (note 34 G3) -/

/-- **G3 (mismatch penalty).**  Two cold consecutive blocks with *distinct*
    labels contribute cross energy at least `Πₖ = N_{k+1}·Nₖ³/(2¹⁶·Xₖ²)`.

    Stated abstractly as a positive lower bound on the bipartite control energy
    when the block labels disagree.

    **Status**: named `sorry` — deterministic consequence of `crossblock_dispersion`
    (note 34 G3). -/
theorem mismatch_penalty (BS : BlockSystem) (a : (p : ℕ) → ZMod p) (k : ℕ)
    (hk1 : BS.k0 ≤ k) (hk2 : k < BS.K)
    (m m' : ℤ) (hmm : m ≠ m')
    (hlabel : (∀ p ∈ BS.P k, (a p : ZMod p) = (m : ZMod p)) ∧
              (∀ q ∈ BS.P (k + 1), (a q : ZMod q) = (m' : ZMod q))) :
    ((BS.P (k + 1)).card : ℝ) * ((BS.P k).card : ℝ) ^ 3 /
        (2 ^ 16 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  sorry

/-! ## G5. Global level-set theorem (note 34 G5) -/

/-- **G5 (global level-set).**  For every `ε ∈ (0,1)` there is a starting scale
    `k₀(ε)` and a constant `C_glob` such that for every block system with
    `k₀ ≥ k₀(ε)` and all `R ≥ 1`, the number of global assignments with control
    energy `≤ R` is `≤ C_glob · e^{8εR}·(1 + √R/sigmaCtrl)`.

    Phrased here via the Laplace-ready partition functional (see G7), the global
    level-set count is encoded by the segment decoder (hot set, hot data,
    mismatch boundary, segment labels, cold exceptions).

    **Status**: named `sorry` — the segment encoding of note 34 G5 (the entire
    "Peierls" content); injective decoder. -/
theorem global_levelset (BS : BlockSystem) (eps : ℝ) (heps : 0 < eps)
    (heps1 : eps < 1) :
    ∃ Cglob : ℝ, 0 < Cglob ∧
      ∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : (p : ℕ) → ZMod p | Qctrl BS a ≤ R} : ℝ) ≤
          Cglob * Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  sorry

/-! ## G7. Prop 8.1 — global control partition (note 34 G7) -/

/-- The "main arc" set `𝔐_C` (note 34 G6): global assignments that are globally
    diagonal with a small common label `|m| ≤ C/sigmaCtrl`. -/
def mainArc (BS : BlockSystem) (C : ℝ) : Set ((p : ℕ) → ZMod p) :=
  {a | ∃ m : ℤ, |(m : ℝ)| ≤ C / sigmaCtrl BS ∧
        ∀ p, (∃ k, BS.k0 ≤ k ∧ k ≤ BS.K ∧ p ∈ BS.P k) →
          (a p : ZMod p) = (m : ZMod p)}

/-- **G7 (global control partition, Prop 8.1).**  With the construction fixed
    (`k₀ ≥ k₀(ε,ρ)`, `c = 16/9`), the off-main-arc Laplace sum of the control
    energy is bounded by a quantity that tends to `0·(1/sigmaCtrl)` as the
    starting scale and the cutoff `C` grow:
    `∑_{a ∉ 𝔐_C} e^{-c·Qctrl(a)} ≤ (C_glob·e^{-F₀/2} + C₁·e^{-C²c/2})/sigmaCtrl`.

    **Status**: named `sorry` — Laplace/dyadic summation of `global_levelset`
    plus the G6 main-arc localization (note 34 G7). -/
theorem global_control_partition (BS : BlockSystem) (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps) (C : ℝ) (hC : 1 ≤ C) :
    ∃ Cglob C1 F0 : ℝ, 0 < Cglob ∧ 0 < C1 ∧ 0 < F0 ∧
      ∑' a : {a : (p : ℕ) → ZMod p // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (Cglob * Real.exp (-c * F0 / 2) + C1 * Real.exp (-C ^ 2 * c / 2)) /
          sigmaCtrl BS := by
  sorry

end GlobalControl

end
