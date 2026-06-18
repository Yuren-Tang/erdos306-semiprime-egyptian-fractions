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
  is `IrvingGood`) is **proved**.  The **faithful finite global-assignment
  interface** (note 36 §0) is now in place: `blockSupport`, `GlobalAssignment`
  (a finite dependent product over the block support), and `Qctrl`/`sigmaCtrl`/
  `mainArc`/`global_levelset`/`global_control_partition` are stated over it, so
  the level-set counts are honest cardinalities of a finite type.
* **G2** — cross-block dispersion (`crossblock_dispersion`).  Self-contained
  number theory; **proved** (deterministic, `lemmaD` pattern; fiber ≤ 1), via
  `nndist1_ratio_ge` and `crossblock_residue_count`.
* **G3** — mismatch penalty `Πₖ` (`mismatch_penalty`).  **Proved (corrected
  statement)** — the original statement is FALSE (label-size hypotheses were
  omitted; see the finding in the G3 section).  Assembled from
  `crossblock_phase_bridge` and `mismatch_per_q`.  The **exceptional corollary**
  `mismatch_penalty_with_exceptions` (note 36 §0, for cold blocks with a bounded
  exception set) is also **proved**.
* **G-2** — block decomposition (note 38 §2).  **Proved:** `blocks_disjoint`
  (D1), `restrict_injective` (D2), `restrict_filter_card_le` (D4),
  `QP_restrict_eq_internal` and `energy_splits` (D3).
* **G-4** — sigma comparison (note 38 §4).  **Proved:** `sigmaP_block_le` (S1),
  `sigmaCtrl_le_one`/`sigmaCtrl_le_geom` (S2), `sigmaCtrl_le_sigmaP_k0` (S3),
  with `block_card_le` and `sigmaP_sq_eq_internal`.
* **G5** — global level-set theorem (`global_levelset`).  **Named `sorry`**
  (the segment encoding; the entire "Peierls" content — the final assembly of
  note 38 §5).  Statement faithful with the threshold `k0min` and the constant
  `A` quantified *uniformly* over all block systems (otherwise vacuous; see the
  faithfulness note there).  Its supporting layer is now proved: G-1
  (`GlobalPeierls.shell_sum_bound`), G-2, G-4, and the single-block extraction
  lemmas `SBEEForcing.dominant_label_unique` (L2u),
  `SBEEForcing.fixed_label_count` (L5), `SBEEForcing.cold_exception_bound`
  (L4c).
* **G7** — Prop 8.1, the global control partition bound
  (`global_control_partition`).  **Named `sorry`** (Laplace step on G5, via
  `SBEEAssembly.partfun_series_bound`, plus G6 localization).  Constants are
  likewise uniform over block systems.

These results feed the minor-arc bound of the circle method (note 35 C4,
`CircleMethod.exists_positive_weighted_construction`).

## Status

Faithful Phase-G translation.  G0 data, the `IrvingGood` bridge, G2/G3, and the
full note-38 §2/§4 support layer (block decomposition G-2 and sigma comparison
G-4) are **proved**.  The two headline assembly theorems `global_levelset` (G5)
and `global_control_partition` (G7) remain precisely-named `sorry`s — the
remaining genuine combinatorial/analytic core — stated faithfully with uniform
constants.  No new analytic input is required beyond the verified single-block
package (`SBEEAssembly`), `GlobalPeierls.shell_sum_bound`, and `lemmaD`.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEAssembly
import RequestProject.GlobalPeierlsBookkeeping

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

/-! ### Faithful finite global-assignment interface (note 36 §0)

The faithful object is a global assignment that lives only on the *block
support* — the finite set of primes actually appearing in some block.  Outside
this support there are no coordinates, so the type is genuinely finite and the
level-set counts below are honest cardinalities (not `Set.ncard` artifacts of an
infinite domain). -/

/-- The block support: all primes appearing in some block `Pₖ`, `k ∈ [k₀,K]`. -/
def blockSupport (BS : BlockSystem) : Finset ℕ :=
  (Finset.Icc BS.k0 BS.K).biUnion (fun k => BS.P k)

/-- A **faithful global assignment**: a residue choice for each prime in the
    block support.  This is the finite dependent product of note 36 §0. -/
abbrev GlobalAssignment (BS : BlockSystem) :=
  (p : {p : ℕ // p ∈ blockSupport BS}) → ZMod p.1

/-- Every prime in the block support is prime (hence positive). -/
lemma blockSupport_prime (BS : BlockSystem) {p : ℕ} (hp : p ∈ blockSupport BS) :
    Nat.Prime p := by
  rw [blockSupport, Finset.mem_biUnion] at hp
  obtain ⟨k, _, hpk⟩ := hp
  exact BS.hprime k p hpk

instance instNeZeroBlockSupport (BS : BlockSystem)
    (p : {p : ℕ // p ∈ blockSupport BS}) : NeZero p.1 :=
  ⟨(blockSupport_prime BS p.2).ne_zero⟩

/-- Extend a faithful global assignment to a plain function `(p:ℕ) → ZMod p` by
    `0` outside the block support (used to feed the per-block lemmas). -/
def toPlain (BS : BlockSystem) (a : GlobalAssignment BS) : (p : ℕ) → ZMod p :=
  fun p => if h : p ∈ blockSupport BS then a ⟨p, h⟩ else 0

/-- Endpoints of a control pair lie in the block support. -/
lemma ctrlPairs_mem_blockSupport (BS : BlockSystem) {pq : ℕ × ℕ}
    (h : pq ∈ ctrlPairs BS) :
    pq.1 ∈ blockSupport BS ∧ pq.2 ∈ blockSupport BS := by
  simp only [ctrlPairs, Finset.mem_union, Finset.mem_biUnion, internalPairs,
    bipartitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Ico, blockSupport] at h ⊢
  rcases h with ⟨k, hk, ⟨hp1, hp2⟩, _⟩ | ⟨k, hk, hp1, hp2⟩
  · exact ⟨⟨k, ⟨hk.1, hk.2⟩, hp1⟩, ⟨k, ⟨hk.1, hk.2⟩, hp2⟩⟩
  · exact ⟨⟨k, ⟨hk.1, le_of_lt hk.2⟩, hp1⟩, ⟨k + 1, ⟨le_trans hk.1 (Nat.le_succ k), hk.2⟩, hp2⟩⟩

/-- The global control energy `Qctrl(a) = ∑_{ctrl pairs} (H_{pq}/(pq))²`,
    over the faithful finite assignment type. -/
def Qctrl (BS : BlockSystem) (a : GlobalAssignment BS) : ℝ :=
  ∑ pq ∈ ctrlPairs BS,
    ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2

/-- The global control deviation `sigmaCtrl = √(∑ 1/(pq)²)`. -/
def sigmaCtrl (BS : BlockSystem) : ℝ :=
  Real.sqrt (∑ pq ∈ ctrlPairs BS, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2)

lemma Qctrl_nonneg (BS : BlockSystem) (a : GlobalAssignment BS) : 0 ≤ Qctrl BS a :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma sigmaCtrl_nonneg (BS : BlockSystem) : 0 ≤ sigmaCtrl BS := Real.sqrt_nonneg _

/-! ### Global range bookkeeping

The global Peierls constants are not allowed to depend arbitrarily on a fixed
`BS`, but they also are not a single absolute constant independent of the number
of blocks.  The faithful paper statement has a uniform base constant, producing
a harmless factor `exp(A * numBlocks BS)`, later killed in G7 by the growing
floor `F0(k0)`.
-/

/-- Number of dyadic blocks in the system. -/
def numBlocks (BS : BlockSystem) : ℕ := BS.K + 1 - BS.k0

/-- Mild global range condition.  The paper only needs that the number of
    blocks grows at most linearly in `k₀` (indeed `log K` is negligible compared
    with the Peierls floors).  This concrete form is deliberately strong and
    easy to use. -/
def admissibleGlobalRange (BS : BlockSystem) : Prop :=
  2 * BS.k0 ≤ BS.K ∧ BS.K ≤ 3 * BS.k0

/-! ## G-2. Block decomposition of the global assignment (note 38 §2) -/

/-- Every prime in a block is nonzero (instance for the block assignment
    `Fintype`). -/
instance instNeZeroBlock (BS : BlockSystem) (k : ℕ) (p : {p : ℕ // p ∈ BS.P k}) :
    NeZero p.1 :=
  ⟨(BS.hprime k p.1 p.2).ne_zero⟩

/-- **Block restriction** (note 38 §2).  The restriction of a global assignment
    to the block `Pₖ`, as a `BlockAssignment (BS.P k)`.  Outside the block
    support it is `0` (harmless: every `p ∈ Pₖ` with `k ∈ [k₀,K]` lies in the
    support). -/
def restrict (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    BlockAssignment (BS.P k) :=
  fun p => if h : (p : ℕ) ∈ blockSupport BS then a ⟨p, h⟩ else 0

/-
**Lemma D1 (windows disjoint, note 38 §2).**  Distinct dyadic windows give
    disjoint blocks.
-/
lemma blocks_disjoint (BS : BlockSystem) {k k' : ℕ} (hkk : k ≠ k') :
    Disjoint (BS.P k) (BS.P k') := by
  rw [ Finset.disjoint_left ];
  intro p hp hp'; cases lt_or_gt_of_ne hkk <;> have := BS.hwindow k p hp <;> have := BS.hwindow k' p hp' <;> simp_all +decide [ Nat.pow_lt_pow_iff_right ] ;
  · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : k + 1 ≤ k' ) ];
  · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : k ≥ k' + 1 ) ]

/-
**Lemma D2 (joint injectivity, note 38 §2).**  A global assignment is
    determined by its restrictions to all blocks `k ∈ [k₀,K]`.
-/
lemma restrict_injective (BS : BlockSystem) {a b : GlobalAssignment BS}
    (h : ∀ k ∈ Finset.Icc BS.k0 BS.K, restrict BS a k = restrict BS b k) :
    a = b := by
  -- By definition, we must show that `a p = b p` for every prime `p ∈ blockSupport BS`.
  apply funext
  intro p
  -- Since `p ∈ blockSupport BS`, by definition there is `k ∈ Finset.Icc BS.k0 BS.K` with `p ∈ BS.P k`.
  obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Icc BS.k0 BS.K, p.1 ∈ BS.P k := by
    unfold blockSupport at p; aesop;
  have := congr_fun ( h k hk.1 ) ⟨ p, hk.2 ⟩ ; simp_all +decide [ restrict ] ;

/-
**Lemma D4 (product count, note 38 §2).**  The number of global assignments
    whose every block restriction satisfies `Φ k` is at most the product of the
    per-block counts.
-/
lemma restrict_filter_card_le (BS : BlockSystem)
    (Φ : ∀ k, BlockAssignment (BS.P k) → Prop) :
    (Finset.univ.filter
        (fun a : GlobalAssignment BS =>
          ∀ k ∈ Finset.Icc BS.k0 BS.K, Φ k (restrict BS a k))).card
      ≤ ∏ k ∈ Finset.Icc BS.k0 BS.K,
          (Finset.univ.filter (fun b : BlockAssignment (BS.P k) => Φ k b)).card := by
  refine' le_trans _ ( Finset.prod_le_prod' fun k hk => Finset.card_le_card _ );
  rotate_right;
  exact fun k => Finset.image ( fun a => restrict BS a k ) ( Finset.univ.filter fun a => ∀ k ∈ Finset.Icc BS.k0 BS.K, Φ k ( restrict BS a k ) );
  · have h_inj : ∀ a b : GlobalAssignment BS, (∀ k ∈ Finset.Icc BS.k0 BS.K, restrict BS a k = restrict BS b k) → a = b := by
      exact fun a b h => restrict_injective BS h
    have h_card_le : (Finset.univ.filter fun a : GlobalAssignment BS => ∀ k ∈ Finset.Icc BS.k0 BS.K, Φ k (restrict BS a k)).card ≤ (Finset.pi (Finset.Icc BS.k0 BS.K) (fun k => (Finset.univ.filter fun a : GlobalAssignment BS => ∀ k ∈ Finset.Icc BS.k0 BS.K, Φ k (restrict BS a k)).image (fun a => restrict BS a k))).card := by
      refine' le_trans _ ( Finset.card_le_card _ );
      rotate_left;
      exact Finset.image ( fun a => fun k hk => restrict BS a k ) ( Finset.univ.filter fun a : GlobalAssignment BS => ∀ k ∈ Finset.Icc BS.k0 BS.K, Φ k ( restrict BS a k ) );
      · grind +splitImp;
      · rw [ Finset.card_image_of_injOn ];
        exact fun a ha b hb hab => h_inj a b fun k hk => by simpa using congr_fun ( congr_fun hab k ) hk;
    convert h_card_le using 1;
    simp +decide [ Finset.card_pi ];
  · grind

/-
The internal-block energy `QP (BS.P k) (restrict BS a k)` equals the
    `internalPairs`-encoded sub-sum of `Qctrl`.
-/
lemma QP_restrict_eq_internal (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    QP (BS.P k) (restrict BS a k)
      = ∑ pq ∈ internalPairs BS k,
          ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  refine' Finset.sum_bij ( fun pq hpq => ( pq.1.1, pq.2.1 ) ) _ _ _ _ <;> simp +decide [ Finset.mem_filter, Finset.mem_product ];
  · unfold orderedPrimePairsA internalPairs; aesop;
  · aesop;
  · unfold internalPairs orderedPrimePairsA; aesop;
  · unfold restrict toPlain Hglob; aesop;

/-
**Lemma D3 (energy splits, note 38 §2).**  The per-block internal energies
    plus the bipartite cross energies are a sub-sum of the global control
    energy.
-/
lemma energy_splits (BS : BlockSystem) (a : GlobalAssignment BS) :
    (∑ k ∈ Finset.Icc BS.k0 BS.K, QP (BS.P k) (restrict BS a k))
      + (∑ k ∈ Finset.Ico BS.k0 BS.K,
          ∑ pq ∈ bipartitePairs BS k,
            ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2)
      ≤ Qctrl BS a := by
  -- By definition of ctrlPairs, we can split the sum into the internal pairs and the bipartite pairs.
  have h_split : ctrlPairs BS = (Finset.Icc BS.k0 BS.K).biUnion (internalPairs BS) ∪ (Finset.Ico BS.k0 BS.K).biUnion (bipartitePairs BS) := by
    rfl;
  -- By definition of ctrlPairs, we can split the sum into the internal pairs and the bipartite pairs. Since these sets are disjoint, we can apply the Finset.sum_union lemma.
  have h_disjoint : Disjoint ((Finset.Icc BS.k0 BS.K).biUnion (internalPairs BS)) ((Finset.Ico BS.k0 BS.K).biUnion (bipartitePairs BS)) := by
    simp +contextual [ Finset.disjoint_left, internalPairs, bipartitePairs ];
    intro a b x hx₁ hx₂ ha hb hab y hy₁ hy₂ ha' hb'; have := BS.hwindow x a ha; have := BS.hwindow x b hb; have := BS.hwindow y a ha'; have := BS.hwindow ( y + 1 ) b hb'; simp_all +decide [ Nat.pow_succ' ] ;
    by_cases hxy : x ≤ y;
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hxy ];
    · -- Since $x > y$, we have $2^x \geq 2^{y+1}$.
      have h_exp : 2 ^ x ≥ 2 ^ (y + 1) := by
        exact pow_le_pow_right₀ ( by decide ) ( by linarith );
      grind;
  rw [ show Qctrl BS a = ∑ pq ∈ ctrlPairs BS, ( ( Hglob ( toPlain BS a ) pq.1 pq.2 : ℝ ) / ( pq.1 * pq.2 ) ) ^ 2 from rfl, h_split, Finset.sum_union h_disjoint ];
  rw [ Finset.sum_biUnion, Finset.sum_biUnion ];
  · exact add_le_add ( Finset.sum_le_sum fun _ _ => by rw [ QP_restrict_eq_internal ] ) le_rfl;
  · intros k hk l hl hkl;
    simp +decide [ Finset.disjoint_left, bipartitePairs ];
    intro a b ha hb ha' hb'; have := blocks_disjoint BS ( show k ≠ l by aesop ) ; simp_all +decide [ Finset.disjoint_left ] ;
  · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left, internalPairs ] ;
    exact fun a b ha hb hab ha' hb' => hkl <| by have := blocks_disjoint BS ( show k ≠ l from hkl ) ; exact False.elim <| Finset.disjoint_left.mp this ha ha';

/-! ## G-4. Sigma comparison lemmas (note 38 §4) -/

/-
Reindexing the internal block deviation sum: the subtype-encoded
    `orderedPrimePairsA (BS.P k)` and the `ℕ×ℕ`-encoded `internalPairs BS k`
    carry the same `1/(p·q)²` sum.
-/
lemma sigmaP_sq_eq_internal (BS : BlockSystem) (k : ℕ) :
    (∑ pq ∈ orderedPrimePairsA (BS.P k),
        (1 : ℝ) / ((pq.1.1 : ℝ) * pq.2.1) ^ 2)
      = ∑ pq ∈ internalPairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 := by
  refine' Finset.sum_bij _ _ _ _ _;
  use fun a ha => ( a.1.1, a.2.1 );
  · unfold orderedPrimePairsA internalPairs; aesop;
  · grind +qlia;
  · unfold internalPairs orderedPrimePairsA; aesop;
  · grind +splitIndPred

/-
**Lemma S1 (note 38 §4).**  Each internal block deviation is dominated by the
    global control deviation (its squares are a sub-sum).
-/
lemma sigmaP_block_le (BS : BlockSystem) (k : ℕ) (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K) :
    sigmaP (BS.P k) ≤ sigmaCtrl BS := by
  refine Real.sqrt_le_sqrt ?_;
  have h_subset : Finset.image (fun pq => (pq.1.1, pq.2.1)) (orderedPrimePairsA (BS.P k)) ⊆ ctrlPairs BS := by
    intro pq hpq
    simp [ctrlPairs] at *;
    rcases hpq with ⟨ a, ha, b, ⟨ hb, h ⟩, rfl ⟩ ; exact Or.inl ⟨ k, ⟨ hk1, hk2 ⟩, by unfold orderedPrimePairsA at h; unfold internalPairs; aesop ⟩ ;
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg h_subset fun _ _ _ => by positivity );
  rw [ Finset.sum_image ] ; aesop

/-
Each block has at most `2^k` primes (the window `[2^k, 2^{k+1})` has that
    length).
-/
lemma block_card_le (BS : BlockSystem) (k : ℕ) : (BS.P k).card ≤ 2 ^ k := by
  convert Set.ncard_le_ncard ( show ( BS.P k : Set ℕ ) ⊆ Set.Icc ( 2 ^ k ) ( 2 ^ ( k + 1 ) - 1 ) from fun p hp => ?_ ) using 1;
  · rw [ Set.ncard_coe_finset ];
  · norm_num [ Set.ncard_eq_toFinset_card' ];
    grind;
  · grind +suggestions

/-
**Lemma S2 (note 38 §4).**  The global control deviation is bounded by a
    geometric tail, in particular `≤ 1` once `k₀ ≥ 2`.
-/
lemma sigmaCtrl_le_one (BS : BlockSystem) (hk0 : 2 ≤ BS.k0) :
    sigmaCtrl BS ≤ 1 := by
  -- We bound the sum inside the square root by considering the contributions from the internal and bipartite pairs separately.
  have h_sum_bound : ∑ pq ∈ ctrlPairs BS, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, ((1 / 4 : ℝ) ^ k) + ∑ k ∈ Finset.Ico BS.k0 BS.K, ((1 / 4 : ℝ) ^ k * (1 / 2)) := by
    have h_sum_bound : ∀ k ∈ Finset.Icc BS.k0 BS.K, ∑ pq ∈ internalPairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
      intro k hk
      have h_card : (internalPairs BS k).card ≤ (BS.P k).card ^ 2 := by
        exact le_trans ( Finset.card_filter_le _ _ ) ( by norm_num [ sq ] )
      have h_bound : ∀ pq ∈ internalPairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (1 / 4 : ℝ) ^ k / (BS.P k).card ^ 2 := by
        intro pq hpq
        have h_bound : (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (1 / 4 : ℝ) ^ k / (2 ^ k) ^ 2 := by
          have h_bound : (pq.1 : ℝ) ≥ 2 ^ k ∧ (pq.2 : ℝ) ≥ 2 ^ k := by
            exact ⟨ mod_cast BS.hwindow k pq.1 ( Finset.mem_filter.mp hpq |>.1 |> Finset.mem_product.mp |>.1 ) |>.1, mod_cast BS.hwindow k pq.2 ( Finset.mem_filter.mp hpq |>.1 |> Finset.mem_product.mp |>.2 ) |>.1 ⟩;
          rw [ div_pow, div_div, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ pow_mul' ] at *;
          · rw [ show ( 4 : ℕ ) ^ k = ( 2 ^ k ) ^ 2 by rw [ pow_right_comm ] ; norm_num ] ; nlinarith [ Nat.mul_le_mul ( show pq.1 ≥ 2 ^ k from mod_cast h_bound.1 ) ( show pq.2 ≥ 2 ^ k from mod_cast h_bound.2 ) ] ;
          · exact pow_pos ( mul_pos ( Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) h_bound.1 ) ) ( Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) h_bound.2 ) ) ) _;
        refine le_trans h_bound ?_;
        gcongr;
        · exact sq_pos_of_pos <| Nat.cast_pos.mpr <| Finset.card_pos.mpr <| by obtain ⟨ p, hp ⟩ := Finset.nonempty_of_ne_empty ( by aesop_cat : BS.P k ≠ ∅ ) ; exact ⟨ p, hp ⟩ ;
        · exact_mod_cast block_card_le BS k
      have h_sum_bound : ∑ pq ∈ internalPairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (1 / 4 : ℝ) ^ k := by
        refine' le_trans ( Finset.sum_le_sum h_bound ) _;
        norm_num [ div_eq_mul_inv ] at *;
        rw [ mul_left_comm ];
        exact mul_le_of_le_one_right ( by positivity ) ( div_le_one_of_le₀ ( mod_cast h_card ) ( by positivity ) )
      exact h_sum_bound;
    have h_sum_bound_bipartite : ∀ k ∈ Finset.Ico BS.k0 BS.K, ∑ pq ∈ bipartitePairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (1 / 4 : ℝ) ^ k * (1 / 2) := by
      intros k hk
      have h_card_bipartite : (bipartitePairs BS k).card ≤ 2 ^ k * 2 ^ (k + 1) := by
        exact le_trans ( Finset.card_product _ _ |> le_of_eq ) ( mul_le_mul' ( block_card_le BS k ) ( block_card_le BS ( k + 1 ) ) );
      have h_sum_bipartite : ∑ pq ∈ bipartitePairs BS k, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (2 ^ k * 2 ^ (k + 1)) * (1 / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2) := by
        refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le _ <| pow_le_pow_left₀ ( by positivity ) ( mul_le_mul ( show ( x.1 : ℝ ) ≥ 2 ^ k by exact_mod_cast BS.hwindow k x.1 ( Finset.mem_product.mp hx |>.1 ) |>.1 ) ( show ( x.2 : ℝ ) ≥ 2 ^ ( k + 1 ) by exact_mod_cast BS.hwindow ( k + 1 ) x.2 ( Finset.mem_product.mp hx |>.2 ) |>.1 ) ( by positivity ) ( by positivity ) ) 2 ) _;
        · positivity;
        · norm_num +zetaDelta at *;
          exact_mod_cast h_card_bipartite;
      convert h_sum_bipartite using 1 ; ring;
      norm_num [ pow_mul', ← mul_pow ];
    refine' le_trans _ ( add_le_add ( Finset.sum_le_sum h_sum_bound ) ( Finset.sum_le_sum h_sum_bound_bipartite ) );
    rw [ ← Finset.sum_biUnion, ← Finset.sum_biUnion ];
    · rw [ ← Finset.sum_union_inter ];
      exact le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset_of_nonneg ( by aesop_cat ) fun _ _ _ => by positivity ) ( Finset.sum_nonneg fun _ _ => by positivity );
    · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left, bipartitePairs ] ;
      intro a b ha hb ha' hb'; have := blocks_disjoint BS ( show k ≠ l by tauto ) ; simp_all +decide [ Finset.disjoint_left ] ;
    · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left, internalPairs ] ;
      exact fun a b ha hb hab ha' hb' => hkl <| by have := blocks_disjoint BS ( show k ≠ l from hkl ) ; exact False.elim <| Finset.disjoint_left.mp this ha ha';
  refine Real.sqrt_le_iff.mpr ?_;
  -- Evaluate the geometric series sum.
  have h_geo_sum : ∑ k ∈ Finset.Icc BS.k0 BS.K, (1 / 4 : ℝ) ^ k ≤ (4 / 3) * (1 / 4) ^ BS.k0 := by
    erw [ geom_sum_Ico ] <;> ring <;> norm_num;
    linarith [ BS.hk ];
  norm_num [ ← Finset.sum_mul _ _ _ ] at *;
  linarith [ pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 4 ) ( by norm_num ) hk0, show ( ∑ x ∈ Ico BS.k0 BS.K, ( 1 / 4 : ℝ ) ^ x ) ≤ ( 4 / 3 ) * ( 1 / 4 ) ^ BS.k0 by exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Ico.mp hx |>.1, Finset.mem_Ico.mp hx |>.2.le ⟩ ) fun _ _ _ => by positivity ) h_geo_sum ]

/-
**Lemma S2' (note 38 §4, geometric form).**  The global control deviation
    is bounded by `4·2^{-k₀}`.
-/
lemma sigmaCtrl_le_geom (BS : BlockSystem) (hk0 : 2 ≤ BS.k0) :
    sigmaCtrl BS ≤ 4 / 2 ^ BS.k0 := by
  refine Real.sqrt_le_iff.mpr ⟨ by positivity, ?_ ⟩;
  -- Bound S exactly as in sigmaCtrl_le_one: split ctrlPairs into internal and bipartite biUnions (disjoint), each block internal sum ≤ (1/4)^k and bipartite sum ≤ (1/4)^k*(1/2).
  have h_split : ∑ pq ∈ ctrlPairs BS, (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (1 / 4 : ℝ) ^ k + ∑ k ∈ Finset.Ico BS.k0 BS.K, (1 / 4 : ℝ) ^ k * (1 / 2) := by
    rw [ ctrlPairs, Finset.sum_union ];
    · refine' add_le_add _ _;
      · rw [ Finset.sum_biUnion ];
        · refine' Finset.sum_le_sum fun k hk => _;
          refine' le_trans ( Finset.sum_le_sum fun pq hpq => one_div_le_one_div_of_le _ <| pow_le_pow_left₀ ( by positivity ) ( mul_le_mul ( show ( pq.1 : ℝ ) ≥ 2 ^ k by exact_mod_cast BS.hwindow k pq.1 ( Finset.mem_filter.mp hpq |>.1 |> Finset.mem_product.mp |>.1 ) |>.1 ) ( show ( pq.2 : ℝ ) ≥ 2 ^ k by exact_mod_cast BS.hwindow k pq.2 ( Finset.mem_filter.mp hpq |>.1 |> Finset.mem_product.mp |>.2 ) |>.1 ) ( by positivity ) ( by positivity ) ) 2 ) _ <;> norm_num;
          -- The cardinality of the internal pairs is at most (P k).card * (P k).card.
          have h_card_internal : (internalPairs BS k).card ≤ (BS.P k).card * (BS.P k).card := by
            exact le_trans ( Finset.card_filter_le _ _ ) ( by norm_num );
          rw [ ← div_eq_mul_inv, div_le_iff₀ ] <;> norm_num [ pow_mul' ];
          norm_num [ sq, ← mul_pow ];
          exact_mod_cast by nlinarith [ block_card_le BS k, show ( 4 : ℕ ) ^ k = ( 2 ^ k ) ^ 2 by rw [ pow_right_comm ] ; norm_num ] ;
        · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left, internalPairs ] ;
          exact fun a b ha hb hab ha' hb' => Finset.disjoint_left.mp ( blocks_disjoint BS hkl ) ha ha';
      · rw [ Finset.sum_biUnion ];
        · refine' Finset.sum_le_sum fun k hk => _;
          refine' le_trans ( Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le ( by positivity ) <| pow_le_pow_left₀ ( by positivity ) ( mul_le_mul ( show ( x.1 : ℝ ) ≥ 2 ^ k by exact_mod_cast BS.hwindow k x.1 ( Finset.mem_product.mp hx |>.1 ) |>.1 ) ( show ( x.2 : ℝ ) ≥ 2 ^ ( k + 1 ) by exact_mod_cast BS.hwindow ( k + 1 ) x.2 ( Finset.mem_product.mp hx |>.2 ) |>.1 ) ( by positivity ) ( by positivity ) ) 2 ) _ ; norm_num [ pow_add, pow_mul ];
          unfold bipartitePairs; norm_num [ pow_mul', mul_pow ] ; ring_nf; norm_num;
          refine' le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul ( Nat.cast_le.mpr ( block_card_le BS k ) ) ( Nat.cast_le.mpr ( block_card_le BS ( 1 + k ) ) ) ( by positivity ) ( by positivity ) ) ( by positivity ) ) ( by positivity ) ) _ ; ring_nf ; norm_num;
          norm_num [ pow_mul', ← mul_pow ] ; ring_nf ; norm_num;
          norm_num [ pow_mul', ← mul_pow ];
        · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left, bipartitePairs ] ;
          intro a b ha hb ha' hb'; have := BS.hwindow k a ha; have := BS.hwindow ( k + 1 ) b hb; have := BS.hwindow l a ha'; have := BS.hwindow ( l + 1 ) b hb'; norm_num at *;
          cases lt_or_gt_of_ne hkl <;> simp_all +decide [ pow_succ' ];
          · -- Since $k < l$, we have $2^l \geq 2^{k+1}$.
            have h_exp : 2 ^ l ≥ 2 ^ (k + 1) := by
              exact pow_le_pow_right₀ ( by decide ) ( by linarith );
            grind;
          · -- Since $l < k$, we have $2^l \leq 2^{k-1}$.
            have h_exp : 2 ^ l ≤ 2 ^ (k - 1) := by
              exact pow_le_pow_right₀ ( by decide ) ( Nat.le_pred_of_lt ‹_› );
            cases k <;> simp_all +decide [ pow_succ' ] ; linarith;
    · simp +decide [ Finset.disjoint_left, internalPairs, bipartitePairs ];
      intro a b x hx₁ hx₂ ha hb hab y hy₁ hy₂ ha' hb'; have := BS.hwindow x a ha; have := BS.hwindow x b hb; have := BS.hwindow ( y + 1 ) a; have := BS.hwindow ( y + 1 ) b; simp_all +decide [ Nat.pow_succ' ] ;
      by_cases hxy : x = y + 1;
      · have := BS.hwindow y a ha'; have := BS.hwindow y b; simp_all +decide [ Nat.pow_succ' ] ;
        grind;
      · have := blocks_disjoint BS ( show x ≠ y by rintro rfl; exact hxy <| by linarith ) ; simp_all +decide [ Finset.disjoint_left ] ;
  refine le_trans h_split ?_;
  erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ pow_mul', ← mul_pow ] ; ring_nf ; norm_num;
  norm_num [ pow_mul', ← Finset.mul_sum _ _ _, ← Finset.sum_mul, geom_sum_eq ] ; ring_nf ; norm_num;
  exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( by norm_num ) ( by positivity ) ) ( by positivity ) ) ( by positivity )

/-
**Lemma S3 (note 38 §4).**  The global control deviation is dominated by
    `c·k₀·σ_{k₀}` for an absolute constant `c`.  The `k₀` factor is what forces
    the lower bound `2k₀ ≤ K` in `admissibleGlobalRange`.
-/
lemma sigmaCtrl_le_sigmaP_k0 :
    ∃ csig : ℝ, 0 < csig ∧
      ∀ BS : BlockSystem, 2 ≤ BS.k0 →
        sigmaCtrl BS ≤ csig * (BS.k0 : ℝ) * sigmaP (BS.P BS.k0) := by
  use 64 * Real.log 2;
  have h_sigmaP_bound : ∀ (BS : BlockSystem), 2 ≤ BS.k0 → sigmaP (BS.P BS.k0) ≥ 1 / (16 * BS.k0 * Real.log 2 * 2 ^ BS.k0) := by
    intros BS hBS
    have hN : 2 ≤ (BS.P BS.k0).card := by
      have := BS.hdensity BS.k0 le_rfl ( by linarith [ BS.hk ] );
      rw [ Real.log_pow, div_le_iff₀ ] at this <;> norm_num at *;
      · contrapose! this;
        interval_cases _ : Finset.card ( BS.P BS.k0 ) <;> norm_num at *;
        rcases n : BS.k0 with ( _ | _ | k0 ) <;> simp_all +decide [ pow_succ' ];
        exact Nat.recOn k0 ( by norm_num; have := Real.log_two_lt_d9; norm_num1 at *; linarith ) fun n ihn => by norm_num [ pow_succ' ] at * ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) n.zero_le ] ;
      · positivity;
    have h_sigmaP_bound : sigmaP (BS.P BS.k0) ≥ (BS.P BS.k0).card / (8 * (2 ^ BS.k0 : ℝ) ^ 2) := by
      have := @SBEEForcing.sigmaP_lower ( 2 ^ BS.k0 ) ?_ ( BS.P BS.k0 ) ?_ ?_ ?_ <;> norm_num at *;
      · exact this;
      · exact one_le_pow₀ ( by norm_num );
      · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime _ _ hp ) ⟩;
      · exact fun p hp => ⟨ BS.hprime _ _ hp, BS.hwindow _ _ hp |>.1, by linarith [ BS.hwindow _ _ hp |>.2, pow_succ' 2 BS.k0 ] ⟩;
      · linarith;
    have h_density_bound : (BS.P BS.k0).card ≥ (2 ^ BS.k0 : ℝ) / (2 * BS.k0 * Real.log 2) := by
      have := BS.hdensity BS.k0 ( by linarith ) ( by linarith [ BS.hk ] );
      convert this.ge using 1 ; norm_num [ Real.log_pow ] ; ring;
    refine le_trans ?_ h_sigmaP_bound;
    rw [ div_le_div_iff₀ ] <;> try positivity;
    rw [ ge_iff_le, div_le_iff₀ ] at h_density_bound <;> nlinarith [ show 0 < ( 2 : ℝ ) ^ BS.k0 by positivity, show 0 < ( BS.k0 : ℝ ) * Real.log 2 by positivity ];
  refine' ⟨ by positivity, fun BS hBS => le_trans ( sigmaCtrl_le_geom BS hBS ) _ ⟩;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( h_sigmaP_bound BS hBS ) ?_ ) <;> ring <;> norm_num;
  · norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos, show BS.k0 > 0 by linarith ];
  · positivity

/-! ## G2. Cross-block dispersion (note 34 G2)

The deterministic dispersion engine, one level up.  Because the window `[X,2X)`
has length `≤ q/2`, each residue class mod `q` meets it in at most one prime, so
the "fiber ≤ 1" form of `lemmaD` applies directly. -/

/-
**Phase lower bound.**  If `q ∤ n` then the distance from `n/q` to the
    nearest integer is at least `1/q` (the numerator is a nonzero residue).
-/
lemma nndist1_ratio_ge (q : ℕ) (hq0 : 0 < q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    1 / (q : ℝ) ≤ nndist1 ((n : ℝ) / (q : ℝ)) := by
  -- Let $k = \text{round}(n/q)$, then $n - kq \neq 0$ since $q \nmid n$.
  set k := round ((n : ℝ) / q)
  have hk_ne_zero : n - k * q ≠ 0 := by
    exact fun h => hn <| ⟨ k, by linarith ⟩;
  -- Since $|n - kq| \geq 1$, we have $|(n : ℝ) / q - k| \geq 1 / q$.
  have h_abs : |(n : ℝ) / q - k| ≥ 1 / q := by
    rw [ div_sub', abs_div ] <;> norm_cast;
    · simp +decide [ mul_comm, Rat.divInt_eq_div ];
      exact le_mul_of_one_le_left ( by positivity ) ( mod_cast abs_pos.mpr ( show ( n - q * k : ℤ ) ≠ 0 from by simpa [ mul_comm ] using hk_ne_zero ) );
    · linarith;
  exact h_abs

/-
**G2 residue count** (the `dispersion_residue_count` analog, fiber ≤ 1).
    The number of `p ∈ P` whose reciprocal phase `‖d·p̄/q‖` is `≤ δ := |P|/(32X)`
    is at most `|P|/4 + 1`.
-/
lemma crossblock_residue_count (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hd : d ≠ 0) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    ((P.filter (fun p =>
        nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ)
      ≤ (P.card : ℝ) / 4 + 1 := by
  -- Set δ := (P.card : ℝ)/(32*X).
  set δ := (P.card : ℝ) / (32 * X);
  -- Step 1 (witness): If p ∈ P and nndist1((d:ℝ)*(pinv p:ℝ)/q) ≤ δ, then there is an integer u with |u| ≤ δ*q and (q:ℤ) ∣ (d * pinv p - u).
  have h_witness : ∀ p ∈ P, nndist1 ((d : ℝ) * (pinv p : ℝ) / q) ≤ δ → ∃ u : ℤ, |u| ≤ δ * q ∧ (q : ℤ) ∣ (d - u * p) := by
    intro p hp hδ
    obtain ⟨u, hu⟩ : ∃ u : ℤ, |u| ≤ δ * q ∧ (q : ℤ) ∣ (d * pinv p - u) := by
      refine' ⟨ d * pinv p - round ( ( d : ℝ ) * pinv p / q ) * q, _, _ ⟩ <;> norm_num [ nndist1 ] at *;
      convert mul_le_mul_of_nonneg_right hδ ( Nat.cast_nonneg q ) using 1 ; rw [ div_sub', abs_div ] <;> norm_num [ hq.ne_zero ] ; ring;
    have h_div : (q : ℤ) ∣ (p * pinv p - 1) := by
      exact ⟨ p * pinv p / q - 1 / q, by linarith [ Nat.mod_add_div ( p * pinv p ) q, Nat.mod_add_div 1 q, hpinv p hp ] ⟩;
    exact ⟨ u, hu.1, by convert hu.2.mul_left p |> Int.dvd_sub <| h_div.mul_left d using 1; ring ⟩;
  -- Step 3 (cover): The filtered set is contained in the union over integers u ∈ Icc (-m) m (where m := ⌊δ*q⌋ ≥ 0) of {p ∈ P : (q:ℤ) ∣ (d - u*p)}.
  have h_cover : {p ∈ P | nndist1 ((d : ℝ) * (pinv p : ℝ) / q) ≤ δ} ⊆ Finset.biUnion (Finset.Icc (-⌊δ * q⌋) ⌊δ * q⌋) (fun u => {p ∈ P | (q : ℤ) ∣ (d - u * p)}) := by
    intro p hp; specialize h_witness p; simp_all +decide [ abs_le ] ;
    exact ⟨ h_witness.choose, ⟨ Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ h_witness.choose_spec.1.1, Int.floor_le ( δ * q ), Int.lt_floor_add_one ( δ * q ) ], Int.le_floor.2 <| by linarith [ h_witness.choose_spec.1.2 ] ⟩, h_witness.choose_spec.2 ⟩;
  -- Step 4 (fiber ≤ 1): For each fixed u, the set {p ∈ P : (q:ℤ) ∣ (d - u*p)} has at most 1 element.
  have h_fiber : ∀ u : ℤ, (Finset.filter (fun p : ℕ => (q : ℤ) ∣ (d - u * p)) P).card ≤ 1 := by
    intros u
    have h_fiber : ∀ p p' : ℕ, p ∈ P → p' ∈ P → (q : ℤ) ∣ (d - u * p) → (q : ℤ) ∣ (d - u * p') → p = p' := by
      intros p p' hp hp' hdiv hdiv'
      have h_eq : (q : ℤ) ∣ u * (p - p') := by
        convert dvd_sub hdiv' hdiv using 1 ; ring;
      by_cases hu : ( q : ℤ ) ∣ u <;> simp_all +decide [ dvd_add_right, dvd_add_left, dvd_sub_right, dvd_sub_left, dvd_mul_of_dvd_right, dvd_mul_of_dvd_left, hq.dvd_mul ];
      have := Int.Prime.dvd_mul' hq h_eq; simp_all +decide [ dvd_sub_right, dvd_sub_left ] ;
      obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith [ hP p hp, hP p' hp' ] ] ;
    exact Finset.card_le_one.mpr fun p hp q hq => h_fiber p q ( Finset.mem_filter.mp hp |>.1 ) ( Finset.mem_filter.mp hq |>.1 ) ( Finset.mem_filter.mp hp |>.2 ) ( Finset.mem_filter.mp hq |>.2 );
  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card h_cover ) _;
  refine' le_trans ( Nat.cast_le.mpr <| Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun u hu => h_fiber u ) _ ; norm_num;
  have h_floor : ⌊δ * q⌋ ≤ (P.card : ℝ) / 8 := by
    refine' le_trans ( Int.floor_le _ ) _;
    rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
  rw [ div_add_one, le_div_iff₀ ] at * <;> norm_cast at *;
  linarith [ Int.toNat_of_nonneg ( by linarith [ show ⌊δ * q⌋ ≥ 0 by exact Int.floor_nonneg.mpr ( by positivity ) ] : 0 ≤ ⌊δ * q⌋ + 1 + ⌊δ * q⌋ ) ]

/-
**G2 (cross-block dispersion).**  For `P ⊆ primes ∩ [X, 2X)`, a prime
    `q ∈ [2X, 4X)`, and `d ≠ 0` with `q ∤ d`, the reciprocal-phase energy
    `∑_{p∈P} ‖d·p⁻¹/q‖²` is bounded below by `|P|³/(2¹¹X²)`.

    `pinv p` denotes the inverse of `p` modulo `q` (as an integer in `[0,q)`).

    **Status**: named `sorry` — deterministic, follows the `lemmaD` pattern with
    fiber ≤ 1 (interval length ≤ modulus/2).
-/
theorem crossblock_dispersion (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (d : ℤ) (hd : d ≠ 0) (hqd : ¬ (q : ℤ) ∣ d)
    (pinv : ℕ → ℕ) (hpinv : ∀ p ∈ P, (p * pinv p) % q = 1 % q) :
    (P.card : ℝ) ^ 3 / (2 ^ 11 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ^ 2 := by
  by_cases hP_card : P.card ≤ 11;
  · -- For each p ∈ P, nndist1((d:ℝ)*(pinv p:ℝ)/q) ≥ 1/q.
    have h_term_ge : ∀ p ∈ P, (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ))) ^ 2 ≥ (1 / (q : ℝ)) ^ 2 := by
      intro p hp
      have h_not_div : ¬(q : ℤ) ∣ (d * pinv p) := by
        haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
        intro H; specialize hpinv p hp; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      gcongr;
      convert nndist1_ratio_ge q ( Nat.Prime.pos hq ) ( d * pinv p ) h_not_div using 1 ; push_cast ; ring;
    refine le_trans ?_ ( Finset.sum_le_sum h_term_ge ) ; norm_num;
    field_simp;
    rw [ le_div_iff₀ ] <;> norm_cast <;> try nlinarith only [ hqlb, hqub, hX ] ;
    nlinarith [ Nat.pow_le_pow_left hP_card 2, Nat.pow_le_pow_left hqlb 2, Nat.pow_le_pow_left hqub.le 2, Nat.mul_le_mul_left ( #P ) ( show #P ^ 2 ≤ 121 by nlinarith only [ hP_card ] ) ];
  · -- By crossblock_residue_count, the number of p ∈ P with nndist1(...) ≤ δ is ≤ P.card/4 + 1.
    set δ := (P.card : ℝ) / (32 * X)
    have h_residue_count : ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ δ)).card : ℝ) ≤ P.card / 4 + 1 := by
      convert crossblock_residue_count X hX P hP q hq hqlb hqub d hd hqd pinv hpinv using 1;
    -- For each p ∈ S, term p = nndist1(...)² > δ².
    have h_term_bound : ∀ p ∈ P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ), (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2 ≥ δ^2 := by
      exact fun p hp => pow_le_pow_left₀ ( by positivity ) ( Finset.mem_filter.mp hp |>.2.le ) 2;
    -- Therefore, ∑ p ∈ P term p ≥ ∑ p ∈ S term p ≥ S.card * δ².
    have h_sum_bound : (∑ p ∈ P, (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2) ≥ ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) * δ^2 := by
      have h_sum_bound : (∑ p ∈ P, (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2) ≥ (∑ p ∈ P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ), (nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)))^2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _;
      exact le_trans ( by simpa using Finset.sum_le_sum h_term_bound ) h_sum_bound;
    -- Since $S.card \geq P.card / 2$, we have $S.card * δ^2 \geq (P.card / 2) * δ^2$.
    have h_card_bound : ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) ≥ (P.card : ℝ) / 2 := by
      have h_card_bound : ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) > δ)).card : ℝ) + ((P.filter (fun p => nndist1 ((d : ℝ) * (pinv p : ℝ) / (q : ℝ)) ≤ δ)).card : ℝ) = P.card := by
        rw_mod_cast [ Finset.card_filter, Finset.card_filter ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones P ▸ by congr; ext; split_ifs <;> linarith;
      linarith [ show ( P.card : ℝ ) ≥ 12 by norm_cast; linarith ];
    convert h_sum_bound.trans' ( mul_le_mul_of_nonneg_right h_card_bound <| sq_nonneg _ ) using 1 ; ring

/-! ## G3. Mismatch penalty (note 34 G3)

**Faithfulness finding (the original statement is FALSE).**  The mismatch penalty
as first stated (kept below, commented out) omits the cold-label size hypotheses
`|m_j| ≤ X_j^{7/4}` of note 34 G3.  Without them it is false: take `m :=`
`∏_{p∈P k} p` and `m' := 0`.  Then `m ≠ m'`, while for every `p ∈ P k`,
`(m : ZMod p) = 0` and for every `q ∈ P (k+1)`, `(m' : ZMod q) = 0`, so every
control representative is `Hglob a p q = crtRepr p q 0 0 = 0` (verified) and the
bipartite energy is `0`, strictly below the positive left-hand side.

The corrected statement restores faithful label-size hypotheses (`hm`, `hm'`,
implied by note 34's L3 cold-label bound) plus block-density regularity used by
the dispersion count (`hNk`, `hNk1`, implied by `BS.hdensity` for large `k`).
-/

/-
The nearest-integer distance never exceeds the absolute value (`round` is
    nearest, so `|x - round x| ≤ |x - 0|`).
-/
lemma nndist1_le_abs (x : ℝ) : nndist1 x ≤ |x| := by
  simpa using round_le x 0

/-
`nndist1` is invariant under integer translation.
-/
lemma nndist1_add_intCast (x : ℝ) (n : ℤ) : nndist1 (x + (n : ℝ)) = nndist1 x := by
  unfold nndist1; rw [ round_add_intCast ] ; ring;
  grind +revert

/-
**G3 phase bridge** (modulus `q`).  For distinct primes `p ≠ q`, an inverse
    `pinv` of `p` mod `q`, and `H := crtRepr p q (m mod p) (m' mod q)`, the
    reciprocal phase `‖(m'-m)·p̄/q‖` is controlled by `|H|/(pq) + |m|/(pq)`.

    Proof: `H ≡ m (mod p)` so `v := (H-m)/p ∈ ℤ`; `v·p ≡ m'-m (mod q)` with
    `p·pinv ≡ 1` give `v ≡ (m'-m)·pinv (mod q)`, so
    `nndist1((m'-m)·pinv/q) = nndist1(v/q) ≤ |v|/q = |H-m|/(pq) ≤ (|H|+|m|)/(pq)`.
-/
lemma crossblock_phase_bridge (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m m' : ℤ) (pinv : ℕ) (hpinv : (p * pinv) % q = 1 % q) :
    nndist1 (((m' - m : ℤ) : ℝ) * (pinv : ℝ) / (q : ℝ))
      ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ))
        + |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
  have h_coprime : Nat.Coprime p q := by
    simpa [ hpq ] using Nat.coprime_primes hp hq;
  obtain ⟨v, hv⟩ : ∃ v : ℤ, (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) - m = p * v := by
    have h_cong : (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) ≡ m [ZMOD p] := by
      have := crtRepr_congr_left p q ( m : ZMod p ) ( m' : ZMod q ) h_coprime hp.pos hq.pos; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
    exact h_cong.symm.dvd;
  have h_div : (q : ℤ) ∣ ((m' - m) * pinv - v) := by
    have h_div : (q : ℤ) ∣ (p * v - (m' - m)) := by
      have h_div : (crtRepr p q (m : ZMod p) (m' : ZMod q) : ℤ) ≡ m' [ZMOD q] := by
        convert crtRepr_congr_right p q ( m : ZMod p ) ( m' : ZMod q ) h_coprime hp.pos hq.pos using 1;
        norm_num [ ← ZMod.intCast_eq_intCast_iff ];
      convert h_div.symm.dvd using 1 ; linarith;
    have h_div : (q : ℤ) ∣ (p * pinv - 1) := by
      exact ⟨ p * pinv / q - 1 / q, by linarith [ Nat.mod_add_div ( p * pinv ) q, Nat.mod_add_div 1 q ] ⟩;
    convert dvd_sub ( h_div.mul_right v ) ( ‹ ( q : ℤ ) ∣ p * v - ( m' - m ) ›.mul_right pinv ) using 1 ; ring;
  have h_nndist : nndist1 ((m' - m : ℤ) * pinv / (q : ℝ)) = nndist1 ((v : ℝ) / (q : ℝ)) := by
    obtain ⟨ k, hk ⟩ := h_div;
    convert nndist1_add_intCast ( v / q : ℝ ) k using 1;
    exact congr_arg _ ( by rw [ div_add', div_eq_div_iff ] <;> norm_cast <;> nlinarith [ hq.two_le ] );
  have h_abs : |(v : ℝ) / (q : ℝ)| ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) - m| / (p * q) := by
    rw [ show ( crtRepr p q m m' : ℝ ) - m = p * v by exact_mod_cast hv ] ; norm_num [ abs_div, abs_mul, hp.ne_zero, hq.ne_zero ] ; ring_nf ;
    norm_num [ hp.ne_zero ];
  have h_abs : |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) - m| ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| + |(m : ℝ)| := by
    exact abs_sub _ _;
  exact h_nndist.symm ▸ le_trans ( nndist1_le_abs _ ) ( by convert le_trans ‹_› ( div_le_div_of_nonneg_right h_abs ( by positivity ) ) using 1 ; ring )

/-
**G3 per-vertex bound.**  For a single good prime `q ∈ [2X,4X)` (with
    `q ∤ m'-m`), the cross energy over `P ⊆ primes ∩ [X,2X)` against `q` is at
    least `|P|³/(2¹³X²)`.

    Proof: by `crossblock_residue_count` at least `|P|/2` of the `p` have
    `‖(m'-m)·p̄/q‖ > δ = |P|/(32X)`; for each the phase bridge plus
    `|m| ≤ δ·pq/2` (from `hm`) gives `|H_{pq}|/(pq) ≥ δ/2`, hence the squared
    term `≥ δ²/4`; summing `≥ (|P|/2)(δ²/4) = |P|³/(2¹³X²)`.
-/
lemma mismatch_per_q (X : ℕ) (hX : 0 < X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X) (hNk : 12 ≤ P.card)
    (q : ℕ) (hq : Nat.Prime q) (hqlb : 2 * X ≤ q) (hqub : q < 4 * X)
    (m m' : ℤ) (hd : m' - m ≠ 0) (hqd : ¬ (q : ℤ) ∣ (m' - m))
    (hm : (32 : ℤ) * |m| ≤ (X : ℤ) * P.card) :
    (P.card : ℝ) ^ 3 / (2 ^ 13 * (X : ℝ) ^ 2) ≤
      ∑ p ∈ P, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 := by
  set pinv : ℕ → ℕ := fun p => ((p : ZMod q)⁻¹).val;
  -- By crossblock_residue_count, at least P.card/2 of the p have nndist1((m'-m)·p̄/q) > δ = P.card/(32X).
  have h_residue_count : ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X))).card : ℝ) ≥ (P.card : ℝ) / 2 := by
    have h_residue_count : ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ) ≤ (P.card : ℝ) / 4 + 1 := by
      convert crossblock_residue_count X hX P hP q hq hqlb hqub ( m' - m ) hd hqd pinv _ using 1;
      intro p hp; haveI := Fact.mk hq; simp +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      simp +zetaDelta at *;
      rw [ mul_inv_cancel₀ ] ; exact by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( hP p hp |>.1 ) ) ( by linarith [ hP p hp |>.2 ] ) ;
    have h_residue_count : ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X))).card : ℝ) = (P.card : ℝ) - ((P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ (P.card : ℝ) / (32 * X))).card : ℝ) := by
      rw [ eq_sub_iff_add_eq, ← Nat.cast_add, ← Finset.card_union_of_disjoint ];
      · congr with p ; by_cases hp : nndist1 ( ( m' - m : ℤ ) * ( pinv p : ℝ ) / q ) ≤ ( P.card : ℝ ) / ( 32 * X ) <;> aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith [ show ( P.card : ℝ ) ≥ 12 by norm_cast ];
  -- For each p in the set where nndist1((m'-m)·p̄/q) > δ, we have |H p|/(pq) ≥ δ/2.
  have h_phase_bound : ∀ p ∈ P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X)), |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) ≥ (P.card : ℝ) / (64 * X) := by
    intro p hp
    have h_phase : nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) ≤ |(crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ)| / ((p : ℝ) * (q : ℝ)) + |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) := by
      convert crossblock_phase_bridge p q ( hP p ( Finset.filter_subset _ _ hp ) |>.1 ) hq ( by
        linarith [ hP p ( Finset.filter_subset _ _ hp ) ] ) m m' ( pinv p ) ( by
        haveI := Fact.mk hq; simp +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
        simp +zetaDelta at *;
        rw [ mul_inv_cancel₀ ] ; norm_num [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( hP p hp.1 |>.1 ) ) ( by linarith [ hP p hp.1 |>.2.2 ] ) ) using 1;
    have h_abs_m : |(m : ℝ)| / ((p : ℝ) * (q : ℝ)) ≤ (P.card : ℝ) / (64 * X) := by
      rw [ div_le_div_iff₀ ] <;> norm_cast at * <;> try nlinarith;
      · norm_num at *;
        nlinarith [ abs_nonneg m, show ( p : ℤ ) * q ≥ 2 * X ^ 2 by norm_cast; nlinarith [ hP p hp.1 ] ];
      · exact mul_pos ( Nat.Prime.pos ( hP p ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ) hq.pos;
    norm_num at *;
    ring_nf at *; linarith;
  -- Therefore, $\sum_{p \in P} \left(\frac{H_{pq}}{pq}\right)^2 \geq \sum_{p \in S} \left(\frac{\delta}{2}\right)^2$.
  have h_sum_bound : ∑ p ∈ P, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * (q : ℝ))) ^ 2 ≥ ∑ p ∈ P.filter (fun p => nndist1 ((m' - m : ℤ) * (pinv p : ℝ) / (q : ℝ)) > (P.card : ℝ) / (32 * X)), ((P.card : ℝ) / (64 * X)) ^ 2 := by
    refine' le_trans ( Finset.sum_le_sum fun p hp => pow_le_pow_left₀ ( by positivity ) ( h_phase_bound p hp ) 2 ) _;
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _ ) _;
    norm_num [ div_pow, abs_div, abs_mul, abs_of_nonneg, Nat.cast_nonneg ];
  refine le_trans ?_ h_sum_bound ; norm_num at *;
  convert mul_le_mul_of_nonneg_right h_residue_count ( show ( 0 : ℝ ) ≤ ( #P : ℝ ) ^ 2 / ( 64 * X ) ^ 2 by positivity ) using 1 ; ring;
  rw [ div_pow ]

/-
**G3 (mismatch penalty) — ORIGINAL STATEMENT, FALSE (see finding above).**

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

**G3 (mismatch penalty), corrected.**  Two consecutive blocks with *distinct*
    labels `m ≠ m'` contribute bipartite control energy at least
    `Πₖ = N_{k+1}·Nₖ³/(2¹⁶·Xₖ²)`.

    Faithful hypotheses added relative to the original (false) statement:
    `hm`/`hm'` are the cold-label size bounds of note 34 G3 (L3), and
    `hNk`/`hNk1` are the block-density regularity used by the dispersion count.

    **Status**: named `sorry` — assembled from `mismatch_per_q` summed over the
    `≥ N_{k+1}/2` good vertices `q ∤ m'-m`.
-/
set_option maxHeartbeats 1000000 in
theorem mismatch_penalty (BS : BlockSystem) (a : (p : ℕ) → ZMod p) (k : ℕ)
    (hk1 : BS.k0 ≤ k) (hk2 : k < BS.K)
    (m m' : ℤ) (hmm : m ≠ m')
    (hlabel : (∀ p ∈ BS.P k, (a p : ZMod p) = (m : ZMod p)) ∧
              (∀ q ∈ BS.P (k + 1), (a q : ZMod q) = (m' : ZMod q)))
    (hNk : 12 ≤ (BS.P k).card) (hNk1 : 2 ≤ (BS.P (k + 1)).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    ((BS.P (k + 1)).card : ℝ) * ((BS.P k).card : ℝ) ^ 3 /
        (2 ^ 16 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  -- By definition of $P_k$ and $P_{k+1}$, we know that $P_k \subseteq \{2^k, 2^k + 1, \ldots, 2^{k+1} - 1\}$ and $P_{k+1} \subseteq \{2^{k+1}, 2^{k+1} + 1, \ldots, 2^{k+2} - 1\}$.
  have hP_k_subset : BS.P k ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
    exact fun p hp => Finset.mem_Ico.mpr <| BS.hwindow k p hp
  have hP_k1_subset : BS.P (k + 1) ⊆ Finset.Ico (2 ^ (k + 1)) (2 ^ (k + 2)) := by
    exact fun p hp => Finset.mem_Ico.mpr <| BS.hwindow _ _ hp;
  have h_good_set : ∃ Q : Finset ℕ, Q ⊆ BS.P (k + 1) ∧ Q.card ≥ (BS.P (k + 1)).card / 2 ∧ ∀ q ∈ Q, ¬(q : ℤ) ∣ (m' - m) := by
    have h_bad_set : (Finset.filter (fun q => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card ≤ 1 := by
      have h_bad_set : ∀ q q' : ℕ, q ∈ BS.P (k + 1) → q' ∈ BS.P (k + 1) → q ≠ q' → ¬((q : ℤ) ∣ (m' - m)) ∨ ¬((q' : ℤ) ∣ (m' - m)) := by
        intros q q' hq hq' hneq
        by_contra h_contra
        push_neg at h_contra
        have h_div : (q * q' : ℤ) ∣ (m' - m) := by
          convert Int.coe_lcm_dvd h_contra.1 h_contra.2 using 1;
          exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( BS.hprime ( k + 1 ) q hq ) ( BS.hprime ( k + 1 ) q' hq' ) ; aesop )
        have h_abs : |m' - m| ≥ (q * q' : ℤ) := by
          exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( Ne.symm hmm ) ) ) ( by simpa )
        have h_abs_le : |m' - m| ≤ |m| + |m'| := by
          cases abs_cases ( m' - m ) <;> cases abs_cases m <;> cases abs_cases m' <;> linarith
        have h_abs_le' : |m| + |m'| < (q * q' : ℤ) := by
          have h_abs_le' : (BS.P k).card ≤ 2 ^ k ∧ (BS.P (k + 1)).card ≤ 2 ^ (k + 1) := by
            have := Finset.card_le_card hP_k_subset; have := Finset.card_le_card hP_k1_subset; simp_all +decide [ pow_succ' ] ;
            exact ⟨ by omega, by omega ⟩;
          have h_abs_le' : (q : ℤ) ≥ 2 ^ (k + 1) ∧ (q' : ℤ) ≥ 2 ^ (k + 1) := by
            exact ⟨ mod_cast Finset.mem_Ico.mp ( hP_k1_subset hq ) |>.1, mod_cast Finset.mem_Ico.mp ( hP_k1_subset hq' ) |>.1 ⟩;
          norm_num [ pow_succ' ] at *;
          nlinarith [ pow_pos ( zero_lt_two' ℤ ) k, Int.mul_ediv_add_emod ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) 32, Int.emod_nonneg ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) ( by norm_num : ( 32 : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( 2 ^ k * ↑ ( # ( BS.P k ) ) ) ( by norm_num : ( 32 : ℤ ) > 0 ) ]
        linarith [h_abs, h_abs_le, h_abs_le'];
      contrapose! h_bad_set;
      obtain ⟨ q, hq, q', hq', hne ⟩ := Finset.one_lt_card.mp h_bad_set; use q.natAbs, q'.natAbs; aesop;
    have h_good_set : (Finset.filter (fun q => ¬(q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card = (BS.P (k + 1)).card - (Finset.filter (fun q => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1))).card := by
      rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num;
      rw [ Finset.inter_eq_left.mpr ];
      · convert rfl;
        convert rfl;
        convert Finset.card_image_of_injective _ Nat.cast_injective;
        infer_instance;
      · exact Finset.filter_subset _ _;
    simp_all +decide [ Finset.filter_image ];
    grind +qlia;
  obtain ⟨ Q, hQ₁, hQ₂, hQ₃ ⟩ := h_good_set;
  have h_sum_bound : ∑ pq ∈ bipartitePairs BS k, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 ≥ ∑ q ∈ Q, ∑ p ∈ BS.P k, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 := by
    have h_sum_bound : ∑ pq ∈ bipartitePairs BS k, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 ≥ ∑ pq ∈ (BS.P k) ×ˢ Q, ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.product_subset_product ( Finset.Subset.refl _ ) hQ₁ ) fun _ _ _ => sq_nonneg _;
    convert h_sum_bound using 1;
    rw [ Finset.sum_product, Finset.sum_comm ];
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [ Hglob, hlabel.1 x hx, hlabel.2 y ( hQ₁ hy ) ] ;
  have h_sum_bound : ∑ q ∈ Q, ∑ p ∈ BS.P k, ((crtRepr p q (m : ZMod p) (m' : ZMod q) : ℝ) / ((p : ℝ) * q)) ^ 2 ≥ ∑ q ∈ Q, ((BS.P k).card : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2) := by
    apply Finset.sum_le_sum;
    intro q hq;
    convert mismatch_per_q ( 2 ^ k ) ( by positivity ) ( BS.P k ) ( fun p hp => ?_ ) hNk q ( ?_ ) ( ?_ ) ( ?_ ) m m' ( ?_ ) ( ?_ ) ( ?_ ) using 1;
    all_goals norm_cast;
    any_goals tauto;
    · exact ⟨ BS.hprime k p hp, by linarith [ Finset.mem_Ico.mp ( hP_k_subset hp ) ], by linarith [ Finset.mem_Ico.mp ( hP_k_subset hp ), pow_succ' 2 k ] ⟩;
    · exact BS.hprime _ _ ( hQ₁ hq );
    · have := hP_k1_subset ( hQ₁ hq ) ; norm_num [ pow_succ' ] at * ; linarith;
    · have := hP_k1_subset ( hQ₁ hq ) ; norm_num [ pow_succ' ] at * ; linarith;
    · exact sub_ne_zero_of_ne hmm.symm;
  refine le_trans ?_ ( le_trans h_sum_bound ‹_› );
  norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  field_simp;
  norm_cast ; linarith [ Nat.div_add_mod ( BS.P ( k + 1 ) |> Finset.card ) 2, Nat.mod_lt ( BS.P ( k + 1 ) |> Finset.card ) two_pos ]

/-
**G3 (mismatch penalty) with exceptions** (note 36 §0).  The cold blocks of the
    global level-set argument carry a *bounded* exception set `Eₖ` of vertices
    where the dominant label fails.  Reusing `mismatch_per_q` over the reduced
    sets `Pₖ \ Eₖ` and `Pₖ₊₁ \ Eₖ₊₁` gives the same bipartite penalty with the
    reduced cardinalities.  The no-exception `mismatch_penalty` is the special
    case `Eₖ = Eₖ₊₁ = ∅`.

    Proof: identical to `mismatch_penalty`, with `Pₖ` replaced by `Pₖ \ Eₖ` (the
    dispersion vertex set) and the "good" outer vertices drawn from
    `Pₖ₊₁ \ Eₖ₊₁`; at most one of those divides `m'-m`, so at least
    `(Pₖ₊₁ \ Eₖ₊₁).card - 1` are good.

    (The hypothesis `hEk1 : Eₖ₊₁ ⊆ Pₖ₊₁` is part of note 36's requested
    interface; the finished proof does not actually use it.)
-/
set_option maxHeartbeats 1000000 in
theorem mismatch_penalty_with_exceptions (BS : BlockSystem)
    (a : (p : ℕ) → ZMod p) (k : ℕ)
    (m m' : ℤ) (hmm : m ≠ m')
    (Ek Ek1 : Finset ℕ) (hEk : Ek ⊆ BS.P k) (hEk1 : Ek1 ⊆ BS.P (k + 1))
    (hlabel_k : ∀ p ∈ BS.P k \ Ek, (a p : ZMod p) = (m : ZMod p))
    (hlabel_k1 : ∀ q ∈ BS.P (k + 1) \ Ek1, (a q : ZMod q) = (m' : ZMod q))
    (hNk : 12 ≤ (BS.P k \ Ek).card)
    (hm : (32 : ℤ) * |m| ≤ (2 ^ k : ℤ) * (BS.P k \ Ek).card)
    (hm' : (32 : ℤ) * |m'| ≤ (2 ^ (k + 1) : ℤ) * (BS.P (k + 1)).card) :
    (((BS.P (k + 1) \ Ek1).card : ℝ) - 1) * ((BS.P k \ Ek).card : ℝ) ^ 3 /
        (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤
      ∑ pq ∈ bipartitePairs BS k,
        ((Hglob a pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
  rotate_left;
  exact Finset.biUnion ( BS.P ( k + 1 ) \ Ek1 ) fun q => Finset.image ( fun p => ( p, q ) ) ( BS.P k \ Ek ) |> Finset.filter fun pq => ¬ ( q : ℤ ) ∣ ( m' - m );
  · simp +decide [ Finset.subset_iff, bipartitePairs ];
    grind;
  · exact fun _ _ _ => sq_nonneg _;
  · rw [ Finset.sum_biUnion ];
    · refine' le_trans _ ( Finset.sum_le_sum fun q hq => _ );
      rotate_left;
      use fun q => if ¬ ( q : ℤ ) ∣ m' - m then ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) else 0;
      · split_ifs <;> simp_all +decide [ Finset.sum_image ];
        rw [ ← Finset.sum_sdiff hEk ];
        have := mismatch_per_q ( 2 ^ k ) ( by positivity ) ( BS.P k \ Ek ) ?_ ?_ q ?_ ?_ ?_ m m' ?_ ?_ ?_ <;> norm_num at *;
        any_goals assumption;
        any_goals rw [ sub_eq_zero ] ; tauto;
        · convert this using 2;
          unfold Hglob; aesop;
        · exact fun p hp hp' => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
        · exact BS.hprime _ _ hq.1;
        · have := BS.hwindow ( k + 1 ) q hq.1; norm_num [ pow_succ' ] at *; linarith;
        · have := BS.hwindow ( k + 1 ) q hq.1; norm_num [ pow_succ' ] at *; linarith;
      · have h_card : (Finset.filter (fun q => ¬(q : ℤ) ∣ (m' - m)) (BS.P (k + 1) \ Ek1)).card ≥ (BS.P (k + 1) \ Ek1).card - 1 := by
          have hQ_card : (Finset.filter (fun q => (q : ℤ) ∣ (m' - m)) (BS.P (k + 1) \ Ek1)).card ≤ 1 := by
            have h_good_outer : ∀ q ∈ (BS.P (k + 1)) \ Ek1, ∀ q' ∈ (BS.P (k + 1)) \ Ek1, q ≠ q' → ¬((q : ℤ) ∣ (m' - m) ∧ (q' : ℤ) ∣ (m' - m)) := by
              intros q hq q' hq' hneq hdiv
              have hprod : (q * q' : ℤ) ∣ (m' - m) := by
                convert Int.coe_lcm_dvd hdiv.1 hdiv.2 using 1;
                exact_mod_cast Eq.symm ( Nat.Coprime.lcm_eq_mul <| Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( BS.hprime ( k + 1 ) q <| Finset.mem_sdiff.mp hq |>.1 ) ( BS.hprime ( k + 1 ) q' <| Finset.mem_sdiff.mp hq' |>.1 ) ; aesop );
              have hprod_le : (q * q' : ℤ) ≤ |m' - m| := by
                exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr hmm.symm ) ) ( by simpa );
              have hprod_ge : (q * q' : ℤ) ≥ 2 ^ (2 * k + 2) := by
                have hprod_ge : (q : ℤ) ≥ 2 ^ (k + 1) ∧ (q' : ℤ) ≥ 2 ^ (k + 1) := by
                  exact ⟨ mod_cast BS.hwindow ( k + 1 ) q ( Finset.mem_sdiff.mp hq |>.1 ) |>.1, mod_cast BS.hwindow ( k + 1 ) q' ( Finset.mem_sdiff.mp hq' |>.1 ) |>.1 ⟩;
                exact le_trans ( by ring_nf; norm_num ) ( mul_le_mul hprod_ge.1 hprod_ge.2 ( by positivity ) ( by positivity ) );
              have hprod_le : (BS.P k \ Ek).card ≤ 2 ^ k ∧ (BS.P (k + 1)).card ≤ 2 ^ (k + 1) := by
                have hprod_le : ∀ k, (BS.P k).card ≤ 2 ^ k := by
                  intros k
                  have hprod_le : (BS.P k).card ≤ Finset.card (Finset.Ico (2 ^ k) (2 ^ (k + 1))) := by
                    exact Finset.card_le_card fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx;
                  exact hprod_le.trans ( by norm_num [ pow_succ' ] ; linarith );
                exact ⟨ le_trans ( Finset.card_le_card ( Finset.sdiff_subset ) ) ( hprod_le k ), hprod_le ( k + 1 ) ⟩;
              norm_num [ pow_add, pow_mul' ] at *;
              nlinarith [ abs_sub m' m, pow_pos ( zero_lt_two' ℤ ) k ];
            refine' Finset.card_le_one.mpr _;
            simp +zetaDelta at *;
            exact fun q hq hq' hq'' r hr hr' hr'' => Classical.not_not.1 fun h => h_good_outer q hq hq' r hr hr' h hq'' hr'';
          rw [ Finset.filter_not, Finset.card_sdiff ];
          gcongr;
          · refine' le_of_eq _;
            refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ Finset.mem_sdiff, Finset.mem_image ];
            exact fun p hp hp' => ⟨ hp, hp' ⟩;
          · exact le_trans ( Finset.card_mono <| Finset.inter_subset_left ) hQ_card;
        simp_all +decide [ Finset.sum_ite ];
        convert mul_le_mul_of_nonneg_right ( sub_le_sub_right ( Nat.cast_le.mpr h_card ) 1 ) ( by positivity : 0 ≤ ( ( BS.P k \ Ek ).card : ℝ ) ^ 3 / ( 2 ^ 13 * ( 2 ^ k ) ^ 2 ) ) using 1 ; ring;
        norm_num [ Finset.filter_image ];
        left;
        refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ Finset.mem_sdiff, Finset.mem_image ];
        tauto;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;

/-! ## G5. Global level-set theorem (note 34 G5) -/

/-
**G5 (global level-set).**  For every `ε ∈ (0,1)` there is a starting scale
    `k₀(ε)` and a constant `C_glob` such that for every block system with
    `k₀ ≥ k₀(ε)` and all `R ≥ 1`, the number of global assignments with control
    energy `≤ R` is `≤ C_glob · e^{8εR}·(1 + √R/sigmaCtrl)`.

    **Faithfulness note (notes 36--37).**  The constant cannot be chosen after
    `BS` (that is vacuous), but the paper does allow a uniform base constant per
    block.  Hence the faithful form below has a uniform `A` and the harmless
    factor `exp(A * numBlocks BS)`, under `admissibleGlobalRange BS`.

    The count is encoded by the segment decoder of note 34 G5 (hot set, hot
    data, mismatch boundary, segment labels, cold exceptions), with the
    single-block inputs L1–L5 (`SBEEAssembly.unified_levelset`,
    `SBEEForcing.theorem_A_dominant_count`, …) and the exceptional mismatch
    penalty `mismatch_penalty_with_exceptions`.

    **Status**: named `sorry` — the segment-encoding "Peierls" injective decoder
    of note 34/36 G5.  This is the deep combinatorial core of Phase G and is not
    yet formalized.
-/
/-! ### G5 skeleton (note 39) — setup definitions -/

/-- Per-block internal energy of a global assignment. -/
def blockEnergy (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  QP (BS.P k) (restrict BS a k)

/-- The cold/hot threshold `R_w(k) = c2·2^k/log³(2^k)` (Theorem-B floor). -/
def Rw (c2 : ℝ) (k : ℕ) : ℝ := c2 * 2 ^ k / (Real.log (2 ^ k)) ^ 3

/-- Hot block: internal energy at least the forcing floor. -/
def isHot (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (k : ℕ) : Prop :=
  Rw c2 k ≤ blockEnergy BS a k

instance instDecidableIsHot (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (k : ℕ) : Decidable (isHot BS c2 a k) := Classical.dec _

/-- The hot set: scales in `[k0,K]` whose block is hot. -/
def hotSet (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Icc BS.k0 BS.K).filter (isHot BS c2 a)

/-- The dominant label of a block (0 if none).  Uniqueness is hole 1. -/
def coldLabel (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℤ :=
  if h : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)
  then h.choose else 0

/-- Mismatch boundary: two consecutive cold blocks with distinct labels. -/
def boundarySet (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) : Finset ℕ :=
  (Finset.Ico BS.k0 BS.K).filter (fun k =>
    ¬ isHot BS c2 a k ∧ ¬ isHot BS c2 a (k+1) ∧
    coldLabel BS a k ≠ coldLabel BS a (k+1))

/-- Integer energy shell of each block. -/
def shellVec (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℕ :=
  ⌊blockEnergy BS a k⌋₊

/-- Segment starts determined by the DATA `(H,B)` alone (no `a`):
    cold blocks that open a maximal cold run. -/
def segStarts (BS : BlockSystem) (H B : Finset ℕ) : Finset ℕ :=
  ((Finset.Icc BS.k0 BS.K) \ H).filter
    (fun k => k = BS.k0 ∨ (k - 1) ∈ H ∨ (k - 1) ∈ B)

/-- The start of the segment containing a cold `k` (recursion downward). -/
def segStart (BS : BlockSystem) (H B : Finset ℕ) : ℕ → ℕ
  | k => if k ≤ BS.k0 then BS.k0
         else if (k - 1) ∈ H ∨ (k - 1) ∈ B then k
         else segStart BS H B (k - 1)
  decreasing_by all_goals omega

/-- The exception-reduced boundary penalty floor `Π(k)`. -/
def Pifloor (BS : BlockSystem) (e0 : ℝ) (k : ℕ) : ℝ :=
  (((BS.P (k+1)).card : ℝ) - e0 - 1) * (((BS.P k).card : ℝ) - e0) ^ 3 /
    (2 ^ 13 * ((2:ℝ) ^ k) ^ 2)

/-- Label range at a segment start (L3 + cold threshold; note 38 §3 L3c). -/
def labelRange (c2 : ℝ) (k : ℕ) : ℤ := ⌈(168:ℝ) * Real.sqrt c2 *
    ((2:ℝ) ^ k) ^ (3/2 : ℝ) / Real.sqrt (Real.log (2 ^ k))⌉

/-! ### G5 skeleton (note 39) — holes -/

/-
**Hole 1a (`coldLabel_spec`).**  When a dominant label exists for block `k`,
    `coldLabel` is one such label: it satisfies the size+class property.
-/
lemma coldLabel_spec (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (h : ∃ m : ℤ, |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)) :
    |coldLabel BS a k| ≤ ((2:ℤ) ^ k) ^ 2 / 2 ∧
      (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
        (((BS.P k).attach.filter
          (fun p => restrict BS a k p
            = ((coldLabel BS a k : ℤ) : ZMod (p : ℕ)))).card : ℝ) := by
  convert h.choose_spec; all_goals exact dif_pos h

/-
**Hole 1b (`coldLabel_eq`).**  Uniqueness: the dominant label is unique, so
    any `m` with the size+class property at a cold block equals `coldLabel`.
-/
lemma coldLabel_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K) (hX : 4 ≤ (2:ℕ) ^ k)
    (hN : 4 ≤ (BS.P k).card)
    (m : ℤ) (hm : |m| ≤ ((2:ℤ) ^ k) ^ 2 / 2)
    (hclass : (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (((BS.P k).attach.filter
        (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ)) :
    coldLabel BS a k = m := by
  apply SBEEForcing.dominant_label_unique (2 ^ k) hX (BS.P k) (fun p hp => ⟨BS.hprime k p hp, by
    exact ⟨ by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩⟩) hN (1 / 4) (by positivity) (by norm_num) (restrict BS a k) (coldLabel BS a k) m (by
  convert coldLabel_spec BS a k _ |>.1 using 1;
  use m) (by
  convert hm using 1) (by
  convert coldLabel_spec BS a k _ |>.2 using 1;
  use m) (by
  grind)

/-
**Hole 4a (`segStart_le`).**  For `k ≥ k0` the segment start of `k` is `≤ k`.
    (For `k < k0` the recursion returns `k0 > k`, so the hypothesis is needed.)
-/
lemma segStart_le (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ) (hk : BS.k0 ≤ k) :
    segStart BS H B k ≤ k := by
  induction' k using Nat.strong_induction_on with k ih;
  unfold segStart;
  grind +splitImp

/-
**Hole 4b (`segStart_ge`).**  The segment start of `k` is `≥ k0`.
-/
lemma segStart_ge (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ) :
    BS.k0 ≤ segStart BS H B k := by
  induction' k using Nat.strong_induction_on with k ih;
  unfold segStart;
  grind

/-
**Hole 4c (`segStart_run`).**  Every block strictly inside the run from the
    segment start of `k` up to `k` is cold-by-data and carries no internal
    boundary edge.
-/
lemma segStart_run (BS : BlockSystem) (H B : Finset ℕ) (k : ℕ)
    (j : ℕ) (hj1 : segStart BS H B k ≤ j) (hj2 : j < k) :
    j ∉ H ∧ j ∉ B := by
  induction' k with k ih generalizing j <;> simp_all +decide [ Nat.pow_succ' ];
  grind +locals

/-
**Hole 2 (`cold_isDominant`).**  Contrapositive of
    `theorem_B_nondominant_forcing` at `ρ = 1/4`: with `c2`/`X0` the constants it
    produces, every cold block (`¬ isHot`) is dominant.
-/
lemma cold_isDominant :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        X0 ≤ (2:ℝ) ^ k → BS.k0 ≤ k → k ≤ BS.K →
        ¬ isHot BS c2 a k →
        SBEEForcing.IsDominant (2 ^ k) (BS.P k) (restrict BS a k) (1/4) := by
  obtain ⟨ c2, X0, hc2, hX0, hB ⟩ := SBEEForcing.theorem_B_nondominant_forcing ( 1 / 4 ) ( by norm_num ) ( by norm_num );
  refine' ⟨ c2, X0, hc2, hX0, fun BS a k hk1 hk2 hk3 hk4 => _ ⟩;
  contrapose! hB;
  refine' ⟨ 2 ^ k, _, BS.P k, _, _, _, _ ⟩ <;> norm_num;
  · exact_mod_cast hk1;
  · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime k p hp ) ⟩;
  · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
  · have := BS.hdensity k hk2 hk3; norm_num at *; ring_nf at *; linarith;
  · refine' ⟨ restrict BS a k, blockEnergy BS a k, le_rfl, hB, _ ⟩;
    unfold isHot at hk4; norm_num [ Rw ] at hk4; linarith;

/-
**Hole 5 (`coldLabel_eq_segStart`).**  Along a cold segment the dominant
    label is constant: a cold block's label equals the label of its segment
    start.
-/
lemma coldLabel_eq_segStart (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS)
    (k : ℕ) (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K)
    (hcold : k ∉ hotSet BS c2 a) :
    coldLabel BS a k
      = coldLabel BS a
          (segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k) := by
  have h_run : ∀ t, segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ t ∧ t < k → coldLabel BS a t = coldLabel BS a (t + 1) := by
    intros t ht; by_contra h_neq; simp_all +decide [ hotSet, boundarySet ] ;
    have h_not_hot : ¬isHot BS c2 a t ∧ ¬isHot BS c2 a (t + 1) := by
      have h_not_hot : t ∉ hotSet BS c2 a ∧ t + 1 ∉ hotSet BS c2 a := by
        have h_not_hot : ∀ j, segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ j ∧ j < k → j ∉ hotSet BS c2 a ∧ j ∉ boundarySet BS c2 a := by
          intros j hj; exact (by
          exact segStart_run BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k j hj.1 hj.2);
        by_cases h : t + 1 < k <;> simp_all +decide [ hotSet, boundarySet ]; all_goals grind;
      exact ⟨ fun h => h_not_hot.1 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ segStart_ge BS ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩, h ⟩, fun h => h_not_hot.2 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ segStart_ge BS ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩, h ⟩ ⟩;
    have h_boundary : t ∈ Finset.filter (fun k => ¬isHot BS c2 a k ∧ ¬isHot BS c2 a (k + 1) ∧ coldLabel BS a k ≠ coldLabel BS a (k + 1)) (Finset.Ico BS.k0 BS.K) := by
      simp_all +decide [ Finset.mem_filter, Finset.mem_Ico ];
      exact ⟨ by linarith [ segStart_ge BS ( filter ( isHot BS c2 a ) ( Icc BS.k0 BS.K ) ) ( { k ∈ Ico BS.k0 BS.K | ¬isHot BS c2 a k ∧ ¬isHot BS c2 a ( k + 1 ) ∧ ¬coldLabel BS a k = coldLabel BS a ( k + 1 ) } ) k ], by linarith ⟩;
    have := segStart_run BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k t ht.1 ht.2; simp_all +decide [ hotSet, boundarySet ] ;
  have h_segment : ∀ i j, segStart BS (hotSet BS c2 a) (boundarySet BS c2 a) k ≤ i → i ≤ j → j ≤ k → coldLabel BS a i = coldLabel BS a j := by
    intros i j hi hj hk; induction' hj with j hj ih <;> simp_all +decide [ Nat.succ_eq_add_one, add_assoc ] ;
    rw [ ih ( by linarith ), h_run j ( by linarith ) hk ];
  exact Eq.symm ( h_segment _ _ le_rfl ( segStart_le _ _ _ _ hk1 ) le_rfl )

/-- The number of primes of block `k` on which `restrict BS a k` takes the
    residue `m` (the size of the `m`-class). -/
def classCount (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) (m : ℤ) : ℕ :=
  ((BS.P k).attach.filter
    (fun p => restrict BS a k p = ((m : ℤ) : ZMod (p : ℕ)))).card

/-- **Hole 6 (fiber).**  The data-fiber of `(H,B,v,ℓ)`: assignments whose every
    block energy sits in the shell `v k` and whose cold blocks carry the
    segment-start label `ℓ (segStart …)` on a `(1-ρ)` fraction of primes. -/
def fiber (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ) :
    Finset (GlobalAssignment BS) :=
  Finset.univ.filter (fun a => ∀ k ∈ Finset.Icc BS.k0 BS.K,
    blockEnergy BS a k ≤ (v k : ℝ) + 1 ∧
    (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
      (classCount BS a k (ℓ (segStart BS H B k)) : ℝ)))

/-
**Hole 7 (`fiber_card_le`).**  The fiber injects into the product of the
    per-block counts (Lemma D4, `restrict_filter_card_le`).
-/
lemma fiber_card_le (BS : BlockSystem) (H B : Finset ℕ) (v : ℕ → ℕ) (ℓ : ℕ → ℤ) :
    (fiber BS H B v ℓ).card ≤
      ∏ k ∈ Finset.Icc BS.k0 BS.K,
        (Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
          QP (BS.P k) b ≤ (v k : ℝ) + 1 ∧
          (k ∉ H → (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
            (((BS.P k).attach.filter
              (fun p => b p = ((ℓ (segStart BS H B k) : ℤ) : ZMod (p : ℕ)))).card : ℝ)))).card := by
  unfold fiber; norm_num;
  convert restrict_filter_card_le BS ( fun k b => QP ( BS.P k ) b ≤ v k + 1 ∧ ( k ∉ H → ( 3 / 4 : ℝ ) * ( BS.P k |> Finset.card ) ≤ ( Finset.card ( Finset.filter ( fun p : { x // x ∈ BS.P k } => b p = ℓ ( segStart BS H B k ) ) ( Finset.attach ( BS.P k ) ) ) : ℝ ) ) ) using 2;
  · simp +decide [ blockEnergy, classCount ];
  · convert rfl

/-
**Hole 11 (`trivial_regime`).**  In the trivial regime `R ≥ Rtriv` the total
    number of global assignments is already `≤ exp(εR)`.  Here
    `Rtriv = ε⁻¹·2^{K+2}·(K+1)`.  (Counts `∏ p ≤ exp(∑_k N_k(k+1)log2)`,
    `N_k ≤ 2^k`.)
-/
lemma trivial_regime (eps : ℝ) (heps : 0 < eps) (BS : BlockSystem) (R : ℝ)
    (hR : eps⁻¹ * 2 ^ (BS.K + 2) * ((BS.K : ℝ) + 1) ≤ R) :
    (Fintype.card (GlobalAssignment BS) : ℝ) ≤ Real.exp (eps * R) := by
  -- We can bound each product term $p \leq 2^{k+1}$ for $p \in P_k$ and sum over $k$.
  have h_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (BS.P k).card * Real.log (2 ^ (k + 1)) := by
    have h_log_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, ∑ p ∈ BS.P k, Real.log p := by
      have h_log : Real.log (Fintype.card (GlobalAssignment BS)) = ∑ p ∈ blockSupport BS, Real.log p := by
        have h_card : (Fintype.card (GlobalAssignment BS)) = ∏ p ∈ blockSupport BS, p := by
          unfold GlobalAssignment; simp +decide [ Fintype.card_pi ] ;
          conv_rhs => rw [ ← Finset.prod_attach ] ;
        rw [ h_card, Nat.cast_prod, Real.log_prod ] ; norm_num;
        exact fun h => by obtain ⟨ k, hk, hk' ⟩ := Finset.mem_biUnion.mp h; have := BS.hwindow k 0 hk'; norm_num at this;
      rw [ h_log, blockSupport, Finset.sum_biUnion ];
      exact fun k hk l hl hkl => blocks_disjoint BS hkl;
    refine le_trans h_log_bound <| Finset.sum_le_sum fun k hk => ?_;
    exact le_trans ( Finset.sum_le_sum fun x hx => Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| BS.hprime k x hx ) <| show ( x : ℝ ) ≤ 2 ^ ( k + 1 ) by exact_mod_cast Nat.le_of_lt <| BS.hwindow k x hx |>.2 ) <| by norm_num;
  -- We can bound each term $\log(2^{k+1}) = (k+1)\log(2)$ and use the fact that $(BS.P k).card \leq 2^k$.
  have h_bound' : Real.log (Fintype.card (GlobalAssignment BS)) ≤ ∑ k ∈ Finset.Icc BS.k0 BS.K, (2 ^ k : ℝ) * (k + 1) * Real.log 2 := by
    refine le_trans h_bound <| Finset.sum_le_sum fun k hk => ?_;
    norm_num [ mul_assoc ];
    gcongr;
    exact_mod_cast le_trans ( Finset.card_le_card ( show BS.P k ⊆ Finset.Ico ( 2 ^ k ) ( 2 ^ ( k + 1 ) ) from fun x hx => Finset.mem_Ico.mpr <| BS.hwindow k x hx ) ) ( by norm_num [ pow_succ' ] ; linarith );
  -- We can bound the sum $\sum_{k=k0}^{K} 2^k (k+1)$ by $2^{K+1} (K+1)$.
  have h_sum_bound : ∑ k ∈ Finset.Icc BS.k0 BS.K, (2 ^ k : ℝ) * (k + 1) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) := by
    have h_sum_bound : ∑ k ∈ Finset.range (BS.K + 1), (2 ^ k : ℝ) * (k + 1) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) := by
      exact Nat.recOn BS.K ( by norm_num ) fun n ihn => by norm_num [ Finset.sum_range_succ, pow_succ' ] at * ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) n ] ;
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) fun _ _ _ => by positivity ) h_sum_bound;
  -- We can bound the sum $\sum_{k=k0}^{K} 2^k (k+1)$ by $2^{K+1} (K+1)$ and use the fact that $\log(2) < 1$.
  have h_final_bound : Real.log (Fintype.card (GlobalAssignment BS)) ≤ 2 ^ (BS.K + 1) * (BS.K + 1) * Real.log 2 := by
    exact h_bound'.trans ( by rw [ ← Finset.sum_mul _ _ _ ] ; exact mul_le_mul_of_nonneg_right h_sum_bound <| Real.log_nonneg <| by norm_num );
  rw [ ← Real.log_le_iff_le_exp ( Nat.cast_pos.mpr <| Fintype.card_pos_iff.mpr ⟨ fun _ => 0 ⟩ ) ];
  refine le_trans h_final_bound ?_;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left hR heps.le ) ; ring_nf ; norm_num [ heps.ne' ];
  nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, show ( 0 : ℝ ) ≤ 2 ^ BS.K by positivity, show ( 0 : ℝ ) ≤ BS.K * 2 ^ BS.K by positivity ]

/-
**Hole 9 (`cold_factor`).**  Per-cold-block fixed-label count: for a label
    of size `|m| ≤ N·X/16` the number of block assignments of energy `≤ n+1`
    whose `m`-class covers a `(1-ρ)` fraction is `≤ exp(ε(n+1))`.  Direct wrapper
    of `SBEEForcing.fixed_label_count` at `ρ = 1/4`.
-/
lemma cold_factor (eps : ℝ) (heps : 0 < eps) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (m : ℤ), |(m : ℝ)| ≤ ((BS.P k).card : ℝ) * (2 ^ k) / 16 →
        ∀ (n : ℕ),
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1 ∧
              (1 - (1/4 : ℝ)) * ((BS.P k).card : ℝ) ≤
                (((BS.P k).attach.filter
                  (fun p => b p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ))).card : ℝ)
            ≤ Real.exp (eps * ((n : ℝ) + 1)) := by
  obtain ⟨ X0, hX0, hF ⟩ := SBEEForcing.fixed_label_count eps ( 1 / 4 ) heps ( by norm_num ) ( by norm_num );
  refine' ⟨ ⌈X0⌉₊ + 1, by positivity, fun BS k hk1 hk2 hk3 m hm n ↦ _ ⟩;
  convert hF ( 2 ^ k ) _ ( BS.P k ) _ _ m _ ( n + 1 ) _ using 1 <;> norm_num;
  · linarith [ Nat.le_ceil X0 ];
  · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
  · convert BS.hdensity k hk1 hk2 |> le_trans _ using 1 ; ring;
    norm_num [ Real.log_pow ] ; ring_nf ; norm_num;
  · convert hm using 1

/-
Block-`σ` lower control: `1/sigmaP (BS.P k) ≤ 16·2^k·log(2^k)`, from the
    block-density `card ≥ 2^k/(2 log 2^k)` and `sigmaP_lower`.
-/
lemma inv_sigmaP_bound (BS : BlockSystem) (k : ℕ) (hk1 : BS.k0 ≤ k) (hk2 : k ≤ BS.K) :
    1 / sigmaP (BS.P k) ≤ 16 * (2:ℝ) ^ k * Real.log (2 ^ k) := by
  by_cases hN : 2 ≤ (BS.P k).card;
  · have h_sigmaP_lower : (BS.P k).card / (8 * (2 ^ k : ℝ) ^ 2) ≤ sigmaP (BS.P k) := by
      convert SBEEForcing.sigmaP_lower ( 2 ^ k ) ( one_le_pow₀ ( by norm_num ) ) ( BS.P k ) _ _ using 1 <;> norm_num;
      · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
      · linarith;
    have h_density : (BS.P k).card ≥ (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) := by
      convert BS.hdensity k hk1 hk2 using 1;
    rw [ div_le_iff₀ ] at * <;> norm_num at *;
    · rw [ div_le_iff₀ ] at h_density <;> nlinarith [ show ( 0 : ℝ ) < 2 ^ k by positivity, show ( 0 : ℝ ) < k * Real.log 2 by exact mul_pos ( Nat.cast_pos.mpr <| by linarith [ BS.hk0 ] ) <| Real.log_pos <| by norm_num ];
    · exact lt_of_lt_of_le ( by positivity ) h_sigmaP_lower;
  · interval_cases _ : Finset.card ( BS.P k ) <;> simp_all +decide;
    · have := BS.hdensity k hk1 hk2; norm_num [ ‹BS.P k = ∅› ] at this;
      exact absurd this ( not_le_of_gt ( div_pos ( by positivity ) ( mul_pos zero_lt_two ( mul_pos ( Nat.cast_pos.mpr ( by linarith [ BS.hk0 ] ) ) ( Real.log_pos one_lt_two ) ) ) ) );
    · have := BS.hdensity k hk1 hk2;
      rw [ div_le_iff₀ ] at this <;> norm_num [ Real.log_pow ] at *;
      · rcases k with ( _ | _ | k ) <;> norm_num at *;
        · norm_num [ ‹#(BS.P 1) = 1› ] at this ; linarith [ Real.log_lt_sub_one_of_pos zero_lt_two ( by norm_num ) ];
        · norm_num [ ‹#(BS.P (k + 1 + 1)) = 1› ] at this;
          exact absurd this ( by { exact not_le_of_gt ( by { exact Nat.recOn k ( by norm_num; have := Real.log_two_lt_d9; norm_num1 at *; linarith ) fun n ihn => by norm_num [ pow_succ' ] at * ; nlinarith [ Real.log_nonneg one_le_two ] } ) } );
      · exact mul_pos ( Nat.cast_pos.mpr ( by linarith [ BS.hk0 ] ) ) ( Real.log_pos ( by norm_num ) )

/-
Analytic threshold for the hot-block absorption (helper for `hot_factor`).
    For `X` large the energy floor `c2·X/log³X` dominates the logarithmic
    polynomial factor coming from `unified_levelset`.
-/
lemma hot_threshold (eps c2 C0 : ℝ) (heps : 0 < eps) (hc2 : 0 < c2) :
    ∃ X0 : ℕ, 2 ≤ X0 ∧ ∀ X : ℕ, X0 ≤ X →
      eps * c2 * X / (Real.log X) ^ 3 ≥
        2 * (Real.log C0 + Real.log 34 + Real.log X + Real.log (Real.log X) + 1) ∧
      eps * (c2 * X / (Real.log X) ^ 3) ≥ Real.log (c2 * X / (Real.log X) ^ 3) := by
  obtain ⟨X0₁, hX0₁⟩ : ∃ X0₁ : ℕ, 2 ≤ X0₁ ∧ ∀ X : ℕ, X0₁ ≤ X → eps * c2 * (X : ℝ) / (Real.log X) ^ 3 ≥ 2 * (Real.log C0 + Real.log 34 + Real.log X + Real.log (Real.log X) + 1) := by
    have h_lim : Filter.Tendsto (fun X : ℝ => (Real.log C0 + Real.log 34 + Real.log X + Real.log (Real.log X) + 1) * (Real.log X) ^ 3 / X) Filter.atTop (nhds 0) := by
      -- We'll use the fact that $\frac{\log^k X}{X}$ tends to $0$ as $X$ tends to infinity for any $k$.
      have h_log_pow : ∀ k : ℕ, Filter.Tendsto (fun X : ℝ => (Real.log X) ^ k / X) Filter.atTop (nhds 0) := by
        intro k
        have h_log_pow_div_X_zero : Filter.Tendsto (fun X : ℝ => (Real.log X)^k / X) Filter.atTop (nhds 0) := by
          have h_log_pow_div_X_zero : Filter.Tendsto (fun X : ℝ => X^k / Real.exp X) Filter.atTop (nhds 0) := by
            simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
          have := h_log_pow_div_X_zero.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] )
        exact h_log_pow_div_X_zero;
      -- We'll use the fact that $\frac{\log(\log X)}{X}$ tends to $0$ as $X$ tends to infinity.
      have h_log_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) * (Real.log X) ^ 3 / X) Filter.atTop (nhds 0) := by
        -- We can use the fact that $\frac{\log(\log X)}{\log X}$ tends to $0$ as $X$ tends to infinity.
        have h_log_log_div_log : Filter.Tendsto (fun X : ℝ => Real.log (Real.log X) / Real.log X) Filter.atTop (nhds 0) := by
          have := h_log_pow 1;
          exact this.comp ( Real.tendsto_log_atTop ) |> fun h => h.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos hx ] );
        convert h_log_log_div_log.mul ( h_log_pow 4 ) using 2 <;> ring;
        grind;
      convert Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( h_log_pow 3 |> Filter.Tendsto.const_mul ( Real.log C0 ) ) ( h_log_pow 3 |> Filter.Tendsto.const_mul ( Real.log 34 ) ) ) ( h_log_pow 4 ) ) h_log_log ) ( h_log_pow 3 ) using 2 <;> ring;
    obtain ⟨ X0₁, hX0₁ ⟩ := Metric.tendsto_atTop.mp h_lim ( eps * c2 / 2 ) ( by positivity );
    refine' ⟨ ⌈X0₁⌉₊ + 2, _, _ ⟩ <;> norm_num;
    intro X hX; specialize hX0₁ X ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ dist_eq_norm ] at hX0₁ ; rw [ Real.norm_eq_abs ] at hX0₁ ; rw [ abs_lt ] at hX0₁ ; rw [ le_div_iff₀ ( pow_pos ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) _ ) ] ; nlinarith [ show ( X : ℝ ) ≥ ⌈X0₁⌉₊ + 2 by exact_mod_cast hX, Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith, pow_pos ( Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith ) 3, mul_div_cancel₀ ( ( Real.log C0 + Real.log 34 + Real.log X + Real.log ( Real.log X ) + 1 ) * Real.log X ^ 3 ) ( show ( X : ℝ ) ≠ 0 by norm_cast; linarith ) ] ;
  -- Show that `eps * (c2 * X / (Real.log X) ^ 3) ≥ Real.log (c2 * X / (Real.log X) ^ 3)` for large X.
  have h_log : Filter.Tendsto (fun X : ℝ => Real.log (c2 * X / (Real.log X) ^ 3) / (c2 * X / (Real.log X) ^ 3)) Filter.atTop (nhds 0) := by
    have h_log : Filter.Tendsto (fun t : ℝ => Real.log t / t) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{t}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
      suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun t => 1 / t) Filter.atTop) (nhds 0) by
        exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
    refine h_log.comp ?_;
    -- We can use the change of variables $u = \log X$ to transform the limit expression.
    suffices h_log : Filter.Tendsto (fun u : ℝ => c2 * Real.exp u / u ^ 3) Filter.atTop Filter.atTop by
      have := h_log.comp Real.tendsto_log_atTop;
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
    simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hc2 ( Real.tendsto_exp_div_pow_atTop 3 );
  -- By the definition of limit, there exists an $X0₂$ such that for all $X \geq X0₂$, $\frac{\log(c2 * X / (\log X)^3)}{c2 * X / (\log X)^3} < \epsilon$.
  obtain ⟨X0₂, hX0₂⟩ : ∃ X0₂ : ℕ, ∀ X : ℕ, X0₂ ≤ X → Real.log (c2 * X / (Real.log X) ^ 3) / (c2 * X / (Real.log X) ^ 3) < eps := by
    exact Filter.eventually_atTop.mp ( h_log.eventually ( gt_mem_nhds heps ) ) |> fun ⟨ X0₂, hX0₂ ⟩ => ⟨ ⌈X0₂⌉₊, fun X hX => hX0₂ X <| Nat.le_of_ceil_le hX ⟩;
  refine' ⟨ X0₁ + X0₂ + 2, _, _ ⟩ <;> norm_num at *;
  intro X hX; specialize hX0₂ X ( by linarith ) ; rw [ div_lt_iff₀ ( div_pos ( mul_pos hc2 ( Nat.cast_pos.mpr ( by linarith ) ) ) ( pow_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) 3 ) ) ] at hX0₂; exact ⟨ hX0₁.2 X ( by linarith ), by linarith ⟩ ;

/-- Helper: monotone log bound.  If `1/eps ≤ t0`, `log t0 ≤ eps·t0`, and
    `t0 ≤ t`, then `log t ≤ eps·t`.  (The map `u ↦ eps·u − log u` is
    nondecreasing on `[1/eps,∞)`.) -/
lemma log_le_eps_mul (eps t0 t : ℝ) (heps : 0 < eps) (ht0pos : 0 < t0)
    (ht0 : 1 / eps ≤ t0) (hlog : Real.log t0 ≤ eps * t0) (ht : t0 ≤ t) :
    Real.log t ≤ eps * t := by
  have htpos : 0 < t := lt_of_lt_of_le ht0pos ht
  have hdiv : Real.log (t / t0) ≤ t / t0 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log t = Real.log t0 + Real.log (t / t0) := by
    rw [Real.log_div (ne_of_gt htpos) (ne_of_gt ht0pos)]; ring
  have hepst0 : 1 ≤ eps * t0 := by
    rw [div_le_iff₀ heps] at ht0; linarith
  -- (t - t0)·(eps - 1/t0) ≥ 0
  have hkey : (t - t0) * (eps - 1 / t0) ≥ 0 := by
    apply mul_nonneg (by linarith)
    have : 1 / t0 ≤ eps := by
      rw [div_le_iff₀ ht0pos]; nlinarith
    linarith
  have hexpand : (t - t0) * (eps - 1 / t0) = eps * t - eps * t0 - (t / t0 - 1) := by
    field_simp
  rw [hsplit]
  nlinarith [hdiv, hlog, hkey, hexpand]

/-
Helper: `Rw c2 k → ∞`, so for `X = 2^k` large, `1/eps ≤ Rw c2 k`.
-/
lemma Rw_large (eps c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ (k : ℕ), 1 ≤ k → X0 ≤ (2:ℝ) ^ k → 1 / eps ≤ Rw c2 k := by
  -- Apply the fact that $Rw c2 k$ tends to infinity as $k$ increases.
  have h_Rw_inf : Filter.Tendsto (fun k : ℕ => Rw c2 k) Filter.atTop Filter.atTop := by
    have h_lim : Filter.Tendsto (fun X : ℝ => c2 * X / (Real.log X) ^ 3) Filter.atTop Filter.atTop := by
      have h_lim : Filter.Tendsto (fun u : ℝ => c2 * Real.exp u / u ^ 3) Filter.atTop Filter.atTop := by
        simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop hc2 ( Real.tendsto_exp_div_pow_atTop 3 );
      have := h_lim.comp Real.tendsto_log_atTop;
      exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
    exact h_lim.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) |> Filter.Tendsto.comp <| Filter.tendsto_id;
  obtain ⟨ k, hk ⟩ := Filter.eventually_atTop.mp ( h_Rw_inf.eventually_ge_atTop ( 1 / eps ) );
  exact ⟨ 2 ^ k, by positivity, fun n hn hn' => hk n <| Nat.le_of_not_lt fun h => by linarith [ pow_lt_pow_right₀ ( by norm_num : ( 1 : ℝ ) < 2 ) h ] ⟩

/-
**Hole 8 (`hot_factor`).**  Per-hot-block count: once the block energy floor
    `Rw c2 k ≤ n+1` holds (hot block), the unconstrained level-set count is
    `≤ exp(2ε(n+1))` — the entropy `unified_levelset` bound `C₀ e^{ε(n+1)}(1+√/σ)`
    has its polynomial factor absorbed by the (large) energy floor.  Valid for
    `k0 ≥` a threshold encoded as `X0 ≤ 2^k`.
-/
lemma hot_factor (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (BS : BlockSystem) (k : ℕ), BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k →
        ∀ (n : ℕ), Rw c2 k ≤ (n : ℝ) + 1 →
          ((Finset.univ.filter (fun b : BlockAssignment (BS.P k) =>
              QP (BS.P k) b ≤ (n : ℝ) + 1)).card : ℝ)
            ≤ Real.exp (2 * eps * ((n : ℝ) + 1)) := by
  obtain ⟨ C0, X1, hC0, hX1, h ⟩ := SBEEAssembly.unified_levelset eps heps heps1
  obtain ⟨ X0₈, hX0₈ ⟩ := hot_threshold eps c2 C0 heps hc2
  obtain ⟨ X0r, hX0r, hX0r' ⟩ := Rw_large eps c2 hc2
  set X0 := Nat.ceil X1 + X0₈ + X0r + 16 with hX0_def
  use X0
  simp [hX0_def] at *;
  refine' ⟨ by positivity, fun BS k hk1 hk2 hk3 n hn => _ ⟩;
  refine' le_trans _ ( Real.exp_le_exp.mpr <| show 2 * eps * ( n + 1 ) ≥ eps * ( n + 1 ) + Real.log ( C0 * 17 * 2 ^ k * Real.log ( 2 ^ k ) * Real.sqrt ( n + 1 ) ) from _ );
  · -- Apply the `unified_levelset` bound to the block `BS.P k`, the radius `R = n + 1`, and the window and density conditions from `BS`.
    have h_unified : (Finset.filter (fun b : BlockAssignment (BS.P k) => QP (BS.P k) b ≤ (n : ℝ) + 1) (Finset.univ : Finset (BlockAssignment (BS.P k)))).card ≤ C0 * Real.exp (eps * (n + 1)) * (1 + Real.sqrt (n + 1) / sigmaP (BS.P k)) := by
      convert h ( 2 ^ k ) _ ( BS.P k ) _ _ ( n + 1 ) _ using 1 <;> norm_num at *;
      · linarith [ Nat.le_ceil X1, show ( X0₈ : ℝ ) ≥ 2 by norm_cast; linarith, show ( 2 : ℝ ) ^ k ≥ 0 by positivity ];
      · exact fun p hp => ⟨ Nat.Prime.ne_zero ( BS.hprime k p hp ) ⟩;
      · exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩;
      · convert BS.hdensity k hk1 hk2 using 1;
        norm_num [ Real.log_pow ];
    -- Apply the `inv_sigmaP_bound` to the block `BS.P k`.
    have h_inv_sigmaP : 1 + Real.sqrt (n + 1) / sigmaP (BS.P k) ≤ 17 * 2 ^ k * Real.log (2 ^ k) * Real.sqrt (n + 1) := by
      have h_simplified : 1 / sigmaP (BS.P k) ≤ 16 * (2 : ℝ) ^ k * Real.log (2 ^ k) := by
        exact inv_sigmaP_bound BS k hk1 hk2;
      ring_nf at *;
      nlinarith [ show 1 ≤ Real.sqrt ( 1 + n : ℝ ) by exact Real.le_sqrt_of_sq_le ( by linarith ), show 1 ≤ Real.log ( 2 ^ k ) * 2 ^ k by exact one_le_mul_of_one_le_of_one_le ( Real.le_log_iff_exp_le ( by positivity ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( 2 : ℝ ) ^ k ≥ 2 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) <| show k ≥ 1 by linarith [ BS.hk0 ] ) ] ) ( one_le_pow₀ <| by norm_num ) ];
    refine' le_trans h_unified ( le_trans ( mul_le_mul_of_nonneg_left h_inv_sigmaP <| by positivity ) _ );
    rw [ Real.exp_add, Real.exp_log ( by exact mul_pos ( mul_pos ( mul_pos ( mul_pos hC0 ( by norm_num ) ) ( by positivity ) ) ( Real.log_pos ( one_lt_pow₀ ( by norm_num ) ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X1 ] ) ] ) ) ) ) ( Real.sqrt_pos.mpr ( by positivity ) ) ) ] ; ring_nf ; norm_num [ Real.exp_pos, hC0, heps ] ;
  · -- Apply the logarithmic bound from `log_le_eps_mul`.
    have h_log_bound : Real.log (C0 * 17 * 2 ^ k * Real.log (2 ^ k)) ≤ (eps / 2) * (n + 1) := by
      have h_log_bound : Real.log C0 + Real.log 17 + Real.log (2 ^ k) + Real.log (Real.log (2 ^ k)) ≤ (eps / 2) * (n + 1) := by
        have := hX0₈.2 ( 2 ^ k ) ( by linarith [ Nat.le_ceil X1, show ( 2 : ℕ ) ^ k ≥ X0₈ by exact_mod_cast ( by linarith [ Nat.le_ceil X1 ] : ( X0₈ : ℝ ) ≤ 2 ^ k ) ] ) ; norm_num at *;
        rw [ show ( 34 : ℝ ) = 2 * 17 by norm_num, Real.log_mul ( by positivity ) ( by positivity ) ] at this;
        unfold Rw at hn; norm_num at hn; ring_nf at *; nlinarith [ Real.log_pos one_lt_two ] ;
      convert h_log_bound using 1 ; rw [ Real.log_mul, Real.log_mul, Real.log_mul ] <;> norm_num <;> try positivity;
      linarith [ BS.hk0 ];
    rw [ Real.log_mul ( by exact ne_of_gt <| mul_pos ( mul_pos ( mul_pos hC0 <| by norm_num ) <| by positivity ) <| Real.log_pos <| one_lt_pow₀ one_lt_two <| by linarith [ show k > 0 from Nat.pos_of_ne_zero <| by rintro rfl; linarith [ Nat.le_ceil X1 ] ] ) <| by positivity, Real.log_sqrt <| by positivity ];
    have h_log_bound : Real.log (n + 1) ≤ eps * (n + 1) := by
      apply log_le_eps_mul eps (Rw c2 k) (n + 1) heps (by
      exact div_pos ( mul_pos hc2 ( pow_pos ( by norm_num ) _ ) ) ( pow_pos ( Real.log_pos ( one_lt_pow₀ ( by norm_num ) ( by linarith [ show k > 0 from Nat.pos_of_ne_zero <| by rintro rfl; linarith [ Nat.le_ceil X1 ] ] ) ) ) _ )) (by
      exact hX0r' k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero <| by rintro rfl; linarith [ Nat.le_ceil X1 ] ] ) ( by linarith [ Nat.le_ceil X1 ] ) |> le_trans ( by norm_num )) (by
      convert hX0₈.2 ( 2 ^ k ) ( by linarith [ Nat.le_ceil X1, show ( 2 : ℕ ) ^ k ≥ X0₈ by exact_mod_cast ( by linarith : ( X0₈ : ℝ ) ≤ 2 ^ k ) ] ) |>.2 using 1; all_goals norm_num [ Rw ]) (by
      exact hn);
    linarith

/-! ### G5 assembly (note 40 §2): energy budget lemmas -/

/-- The bipartite cross-energy of block `k` (note 40 §3d-i). -/
def Xen (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : ℝ :=
  ∑ pq ∈ bipartitePairs BS k,
    ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2

/-
**Note 40 §3a (`sum_blockEnergy_le`).**  The per-block internal energies
    sum to at most `R`.
-/
lemma sum_blockEnergy_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Icc BS.k0 BS.K, blockEnergy BS a k ≤ R := by
  refine le_trans ?_ hR;
  refine le_trans ?_ ( energy_splits BS a );
  exact le_add_of_le_of_nonneg ( Finset.sum_le_sum fun _ _ => le_rfl ) ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ )

/-
**Note 40 §3b (`sum_shellVec_le`).**  The shell vector sums to at most `R`.
-/
lemma sum_shellVec_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Icc BS.k0 BS.K, (shellVec BS a k : ℝ) ≤ R := by
  refine' le_trans _ ( sum_blockEnergy_le BS a R hR );
  exact Finset.sum_le_sum fun _ _ => Nat.floor_le <| Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
**Note 40 §3b (`shellVec_le_floorR`).**  Each shell coordinate is at most
    `⌊R⌋₊`.
-/
lemma shellVec_le_floorR (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : Qctrl BS a ≤ R) (k : ℕ) (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    shellVec BS a k ≤ ⌊R⌋₊ := by
  refine Nat.floor_mono ?_;
  exact le_trans ( Finset.single_le_sum ( fun x _ => show 0 ≤ blockEnergy BS a x from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) hk ) ( sum_blockEnergy_le BS a R hR )

/-
**Note 40 §3c (`sum_Rw_hot_le`).**  The hot-floor weights sum to at most `R`.
-/
lemma sum_Rw_hot_le (BS : BlockSystem) (c2 : ℝ) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ hotSet BS c2 a, Rw c2 k ≤ R := by
  refine' le_trans _ ( sum_blockEnergy_le BS a R hR );
  refine' le_trans ( Finset.sum_le_sum fun k hk => _ ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ );
  exact Finset.mem_filter.mp hk |>.2

/-
**Note 40 §3d-i (`sum_bipartite_le`).**  The bipartite cross-energies sum to
    at most `R`.
-/
lemma sum_bipartite_le (BS : BlockSystem) (a : GlobalAssignment BS) (R : ℝ)
    (hR : Qctrl BS a ≤ R) :
    ∑ k ∈ Finset.Ico BS.k0 BS.K, Xen BS a k ≤ R := by
  refine' le_trans _ hR;
  refine' le_trans _ ( energy_splits BS a );
  exact le_add_of_nonneg_of_le ( Finset.sum_nonneg fun _ _ => by exact_mod_cast QP_nonneg _ _ ) ( Finset.sum_le_sum fun _ _ => by rfl )

/-- The exception primes of (cold) block `k`: primes where the assignment
    deviates from the dominant label `coldLabel`. -/
def excSet (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) : Finset ℕ :=
  (BS.P k).filter (fun p => toPlain BS a p ≠ ((coldLabel BS a k : ℤ) : ZMod p))

lemma excSet_subset (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    excSet BS a k ⊆ BS.P k := Finset.filter_subset _ _

/-
For `p ∈ BS.P k` with `k ∈ [k0,K]`, the restriction agrees with the
    extension `toPlain`.
-/
lemma restrict_eq_toPlain (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) (p : {p : ℕ // p ∈ BS.P k}) :
    restrict BS a k p = toPlain BS a (p : ℕ) := by
  unfold restrict toPlain; simp +decide [ *, Finset.mem_biUnion.mpr ] ;

/-
The exception count equals the `attach`-form exception count of
    `cold_exception_bound`.
-/
lemma excSet_card_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    (excSet BS a k).card =
      ((BS.P k).attach.filter
        (fun q => restrict BS a k q ≠ ((coldLabel BS a k : ℤ) : ZMod (q : ℕ)))).card := by
  convert Finset.card_image_iff.mpr _ using 1;
  rotate_left;
  exact ℕ;
  exact fun q => q.val;
  infer_instance;
  · exact fun x hx y hy hxy => Subtype.ext hxy;
  · congr! 1;
    ext; simp [excSet, restrict_eq_toPlain];
    exact ⟨ fun h => ⟨ h.1, by simpa [ restrict_eq_toPlain BS a k hk ] using h.2 ⟩, fun h => ⟨ h.1, by simpa [ restrict_eq_toPlain BS a k hk ] using h.2 ⟩ ⟩

/-
The conforming count `card (P k \ excSet)` equals `classCount` of the
    dominant label.
-/
lemma conform_card_eq (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    (BS.P k \ excSet BS a k).card = classCount BS a k (coldLabel BS a k) := by
  refine' Finset.card_bij _ _ _ _;
  use fun x hx => ⟨ x, Finset.mem_sdiff.mp hx |>.1 ⟩;
  · simp +contextual [ restrict_eq_toPlain BS a k hk, excSet ];
  · aesop;
  · simp +decide [ excSet, restrict_eq_toPlain BS a k hk ];
    tauto

/-
**Note 40 §3d-ii (`cold_exceptions_small`).**  For a cold block (`X = 2^k`
    large) the exception set is small: its cardinality is at most `e0`, hence
    the conforming set `BS.P k \ excSet` has at least `N_k - e0` primes.
-/
set_option maxHeartbeats 1600000 in
lemma cold_exceptions_small :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        ((BS.P k).card : ℝ) - e0 ≤ ((BS.P k \ excSet BS a k).card : ℝ) := by
  obtain ⟨c2, X0d, hc2, hX0d, hDom⟩ := cold_isDominant
  obtain ⟨e0, X0e, he0, hX0e, hExc⟩ := SBEEForcing.cold_exception_bound (1/4) (by norm_num) (by norm_num) c2 hc2
  obtain ⟨X0s, hX0s, hSize⟩ := SBEEForcing.cold_label_size (1/4) (by norm_num) (by norm_num) c2 hc2
  obtain ⟨X0w, _, hRw⟩ := Rw_large 1 c2 hc2
  use c2, e0, max X0d (max X0e (max X0s (max X0w 16)));
  refine' ⟨ hc2, he0, by positivity, fun BS a k hk1 hk2 hk3 hk4 => _ ⟩;
  -- Apply the cold exception bound lemma to get the first part of the conjunction.
  have h_exc : (excSet BS a k).card ≤ e0 := by
    rw [ excSet_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ];
    apply hExc (2 ^ k) (by
    exact le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) ( mod_cast hk3 )) (BS.P k) (by
    exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩) (by
    convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ]) (restrict BS a k) (coldLabel BS a k) (max 1 (blockEnergy BS a k)) (by
    exact le_max_left _ _) (by
    exact le_max_of_le_right ( by rw [ blockEnergy ] )) (by
    simp +zetaDelta at *;
    unfold isHot at hk4; norm_num [ Rw ] at hk4;
    exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk4 ⟩) (by
    apply hSize (2 ^ k) (by
    exact_mod_cast le_trans ( le_max_of_le_right ( le_max_of_le_right ( le_max_left _ _ ) ) ) hk3) (BS.P k) (by
    exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩) (by
    convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ]) (restrict BS a k) (coldLabel BS a k) (max 1 (blockEnergy BS a k)) (by
    exact le_max_left _ _) (by
    convert coldLabel_spec BS a k ( hDom BS a k ( by linarith [ le_max_left X0d ( max X0e ( max X0s ( max X0w 16 ) ) ) ] ) hk1 hk2 hk4 ) |>.1 using 1) (by
    have := coldLabel_spec BS a k ( hDom BS a k ( by linarith [ le_max_left X0d ( max X0e ( max X0s ( max X0w 16 ) ) ) ] ) hk1 hk2 hk4 ) ; norm_num at * ; linarith;) (by
    exact le_max_of_le_right ( by rw [ blockEnergy ] )) (by
    simp +zetaDelta at *;
    unfold isHot at hk4; norm_num [ Rw ] at hk4;
    exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk4 ⟩)) (by
    have := coldLabel_spec BS a k ( hDom BS a k ( by linarith [ le_max_left X0d ( max X0e ( max X0s ( max X0w 16 ) ) ) ] ) hk1 hk2 hk4 ) ; norm_num at * ; linarith;);
  rw [ Finset.card_sdiff ] ; norm_num [ h_exc ];
  rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a k ) ] ; rw [ Nat.cast_sub ( Finset.card_le_card ( excSet_subset BS a k ) ) ] ; linarith;

/-
**Sharper cold-label size bound** (note 40 §3d-iii needs `|m| ≤ N·X/64`,
    a factor `4` stronger than `cold_label_size`).  Proof identical in shape to
    `SBEEForcing.cold_label_size`, with the polynomial threshold widened.
-/
lemma cold_label_size64 (c2 : ℝ) (hc2 : 0 < c2) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1],
          (∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2 * X) →
          (X : ℝ) / (2 * Real.log X) ≤ P.card →
          ∀ (a : BlockAssignment P) (m : ℤ) (R : ℝ), 1 ≤ R →
          |m| ≤ (X : ℤ) ^ 2 / 2 →
          (1 - (1/4:ℝ)) * (P.card : ℝ) ≤ ((P.attach.filter
              (fun p => a p = ((m : ℤ) : ZMod (p : ℕ)))).card : ℝ) →
          QP P a ≤ R → R ≤ c2 * X / (Real.log X) ^ 3 →
            |(m : ℝ)| ≤ (P.card : ℝ) * (X : ℝ) / 64 := by
  obtain ⟨ X0K, hX0K ⟩ :=SBEEForcing.exists_X0_const_logbnd ( 1677721600 * c2 / 9 );
  obtain ⟨ X0d, hX0d ⟩ := SBEEForcing.exists_X0_logbnd ; refine' ⟨ Max.max 16 ( Max.max ⌈X0K⌉₊ ⌈X0d⌉₊ ), _, _ ⟩ <;> norm_num;
  intro X hX₁ hX₂ hX₃ P _ hP hP' a m R hR₁ hR₂ hR₃ hR₄ hR₅; have := hX0K.2 X hX₂; have := hX0d.2 X hX₃; norm_num at *;
  -- By `theoremA_label_range X _ P hP (hN:8≤N) (1/4) _ _ a m R hm hclass hQ`, `|(m:ℝ)| ≤ (20/3)·√R/sigmaP P`.
  have h_bound : |(m : ℝ)| ≤ (20 / 3) * Real.sqrt R / sigmaP P := by
    have h_bound : |(m : ℝ)| ≤ (5 / (1 - 1 / 4)) * Real.sqrt R / sigmaP P := by
      have hN : 8 ≤ P.card := by
        exact_mod_cast ( by nlinarith [ show ( X : ℝ ) ≥ 16 by norm_cast, Real.log_pos ( show ( X : ℝ ) > 1 by norm_cast; linarith ), mul_div_cancel₀ ( X : ℝ ) ( show ( 2 * Real.log X ) ≠ 0 by exact mul_ne_zero two_ne_zero <| ne_of_gt <| Real.log_pos <| show ( X : ℝ ) > 1 by norm_cast; linarith ) ] : ( 8 : ℝ ) ≤ P.card )
      convert SBEEForcing.theoremA_label_range X ( by linarith ) P hP hN ( 1 / 4 ) ( by positivity ) ( by norm_num ) a m R _ _ _ using 1 <;> norm_num at *;
      · grind +revert;
      · convert hR₂ using 1;
      · convert hR₃ using 1;
      · exact hR₄;
    exact h_bound.trans_eq ( by ring );
  -- By `sigmaP_lower X _ P hP (hN2:2≤N)`, `sigmaP P ≥ N/(8X²) > 0`, so `1/sigmaP P ≤ 8X²/N` and `|(m:ℝ)| ≤ (20/3)·√R·8X²/N = (160/3)·√R·X²/N`.
  have h_sigmaP_lower : 1 / sigmaP P ≤ 8 * (X : ℝ) ^ 2 / P.card := by
    have h_sigmaP_lower : sigmaP P ≥ (P.card : ℝ) / (8 * (X : ℝ) ^ 2) := by
      convert SBEEForcing.sigmaP_lower X ( by linarith ) P _ _ using 1;
      · exact fun p => ‹∀ a ∈ P, NeZero a› p p.2;
      · assumption;
      · contrapose! hP';
        interval_cases _ : P.card <;> norm_num at *;
        · exact div_pos ( by positivity ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) );
        · rw [ lt_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( X : ℝ ) > 1 by norm_cast; linarith ), show ( X : ℝ ) ≥ 16 by norm_cast ];
    convert one_div_le_one_div_of_le _ h_sigmaP_lower using 1 ; norm_num;
    exact div_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by rintro rfl; norm_num at hP' ; linarith [ show ( 0 : ℝ ) < X / ( 2 * Real.log X ) by exact div_pos ( by positivity ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ] ) ) ) ) ( by positivity );
  -- So it suffices to show `(160/3)·√R·X²/N ≤ N·X/64`, i.e. `√R ≤ 3·N²/(64·160·X) = 3N²/(10240·X)`, i.e. (squaring, both sides ≥0) `R ≤ 9·N⁴/(10240²·X²) = 9·N⁴/(104857600·X²)`.
  suffices h_suff : R ≤ 9 * (P.card : ℝ) ^ 4 / (104857600 * (X : ℝ) ^ 2) by
    refine le_trans h_bound ?_;
    convert mul_le_mul_of_nonneg_left ( mul_le_mul h_sigmaP_lower ( Real.sqrt_le_sqrt h_suff ) ( by positivity ) ( by positivity ) ) ( by positivity : ( 0 : ℝ ) ≤ 20 / 3 ) using 1 ; ring;
    field_simp;
    rw [ eq_div_iff ] <;> norm_num [ show X ≠ 0 by linarith, show P.card ≠ 0 by exact Nat.ne_of_gt <| Finset.card_pos.mpr <| Finset.nonempty_of_ne_empty <| by rintro rfl; norm_num at * ; linarith [ show ( X : ℝ ) ≥ 16 by norm_cast ] ] ; ring;
    rw [ show ( P.card : ℝ ) ^ 4 = ( P.card ^ 2 ) ^ 2 by ring, Real.sqrt_sq ( by positivity ) ] ; norm_num [ mul_comm, ne_of_gt ( by positivity : 0 < X ) ];
  refine' le_trans hR₅ _;
  rw [ div_le_div_iff₀ ];
  · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) ( show ( P.card : ℝ ) ≥ X / ( 2 * Real.log X ) by exact hP' ) 4 ) ( by positivity ) ) ( by positivity ) ) ; ring_nf at * ; norm_num at *;
    field_simp;
    rw [ le_div_iff₀ ( Real.log_pos ( by norm_cast; linarith ) ) ] ; linarith;
  · exact pow_pos ( Real.log_pos ( by norm_cast; linarith ) ) _;
  · positivity

set_option maxHeartbeats 1600000 in
/-- **Bundled cold-block facts.**  Produces the global cold constants `c2,e0`
    and, for every cold block, (i) a small exception set, (ii) a sharp label
    bound `|coldLabel| ≤ N·X/64`, and (iii) the conforming primes carry the
    label.  This is the per-block input to the boundary penalty. -/
lemma cold_block_facts :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p)) := by
  obtain ⟨c2, X0d, hc2, hX0d, hDom⟩ := cold_isDominant;
  obtain ⟨e0, X0e, he0, hX0e, hExc⟩ := SBEEForcing.cold_exception_bound (1/4) (by norm_num) (by norm_num) c2 hc2;
  obtain ⟨X0s6, hX0s6, hSize6⟩ := cold_label_size64 c2 hc2
  obtain ⟨X0w, _, hRw⟩ := Rw_large 1 c2 hc2;
  refine' ⟨ c2, e0, Max.max X0d ( Max.max X0e ( Max.max X0s6 ( Max.max X0w 16 ) ) ), hc2, he0, _, _ ⟩ <;> norm_num;
  intro BS a k hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8; refine' ⟨ _, _, _ ⟩;
  · convert hExc ( 2 ^ k ) ( mod_cast hk4 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
      exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) ( by
      unfold isHot at hk8; norm_num [ Rw ] at hk8; ring_nf at *;
      norm_num [ Real.log_pow ] at *;
      ring_nf at *;
      refine' ⟨ _, le_of_lt hk8 ⟩;
      convert hRw k ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ) hk6 using 1 ; norm_num [ Rw ] ; ring ) ( by
      convert hSize6 ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
        convert coldLabel_spec BS a k ( hDom BS a k ( by linarith ) hk1 hk2 hk8 ) |>.1 using 1 ) ( by
        convert coldLabel_spec BS a k ( hDom BS a k hk3 hk1 hk2 hk8 ) |>.2 using 1 ) ( by
        exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
      constructor <;> intro h;
      · convert hSize6 ( 2 ^ k ) ( mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
          convert coldLabel_spec BS a k ( hDom BS a k hk3 hk1 hk2 hk8 ) |>.1 using 1 ) ( by
          convert coldLabel_spec BS a k ( hDom BS a k hk3 hk1 hk2 hk8 ) |>.2 using 1 ) ( by
          exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
      · refine' le_trans ( h _ ) _;
        · unfold isHot at hk8; norm_num [ Rw ] at hk8;
          norm_num [ Real.log_pow ] at *;
          exact ⟨ by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith, le_of_lt hk8 ⟩;
        · gcongr ; norm_num ) ( by
      convert coldLabel_spec BS a k ( hDom BS a k hk3 hk1 hk2 hk8 ) |>.2 using 1 ) using 1;
    convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( excSet_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk1, hk2 ⟩ ) ) using 1;
  · convert hSize6 ( 2 ^ k ) ( by exact_mod_cast hk5 ) ( BS.P k ) ( fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, pow_succ' 2 k ] ⟩ ) ( by convert BS.hdensity k hk1 hk2 using 1 ; norm_num [ Real.log_pow ] ) ( restrict BS a k ) ( coldLabel BS a k ) ( Max.max 1 ( blockEnergy BS a k ) ) ( by exact le_max_left _ _ ) ( by
      convert coldLabel_spec BS a k ( hDom BS a k ( by linarith ) hk1 hk2 hk8 ) |>.1 using 1 ) ( by
      convert coldLabel_spec BS a k ( hDom BS a k hk3 hk1 hk2 hk8 ) |>.2 using 1 ) ( by
      exact le_max_of_le_right ( by rw [ blockEnergy ] ) ) using 1;
    norm_num +zetaDelta at *;
    exact ⟨ fun h => fun _ _ => h, fun h => h ( by have := hRw k ( by linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0d ] ) ] ) ( by linarith ) ; unfold Rw at this; norm_num at this; linarith ) ( by unfold isHot at hk8; norm_num [ Rw ] at hk8; linarith ) ⟩;
  · unfold excSet; aesop;

set_option maxHeartbeats 2000000 in
/-- **Note 40 §3d-iii/3d-iv master cold lemma.**  Produces the global cold
    constants and, besides the per-cold-block facts, the boundary penalty floor:
    every mismatch-boundary block contributes bipartite energy `≥ Pifloor`. -/
lemma boundary_penalty_per_k :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p))) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) := by
  obtain ⟨c2, e0, X0cbf, hc2, he0, hX0cbf, hCBF⟩ := cold_block_facts;
  obtain ⟨X0den, hX0den, hden⟩ := SBEEForcing.exists_X0_const_logbnd (4*e0 + 26);
  use c2, e0, max X0cbf (max X0den 16); norm_num;
  refine' ⟨ hc2, he0, _, _ ⟩;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6; specialize hCBF BS a k hk1 hk2 hk3 hk6; aesop;
  · intro BS a k hk1 hk2 hk3 hk4 hk5 hk6
    set Nk := (BS.P k).card
    set Nk1 := (BS.P (k + 1)).card
    set ck := (BS.P k \ excSet BS a k).card
    set ck1 := (BS.P (k + 1) \ excSet BS a (k + 1)).card
    have hNk : 12 ≤ ck := by
      have hNk : Nk ≥ 2 * e0 + 13 := by
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
        have := hden ( 2 ^ k ) ( mod_cast hk4 ) ; norm_num at *;
        rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ) ) ( Real.log_pos one_lt_two ) ] ;
      have hck : (ck : ℝ) ≥ Nk - e0 := by
        have hck : (ck : ℝ) = Nk - (excSet BS a k).card := by
          exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card ( excSet_subset BS a k )
        generalize_proofs at *; (
        linarith [ hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) |>.1 ]);
      exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith )
    have hm : (32 : ℤ) * |coldLabel BS a k| ≤ (2 ^ k : ℤ) * ck := by
      have hck : (ck : ℝ) ≥ Nk - e0 := by
        have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
          exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
        convert add_le_add_left this.1 ck using 1 ; ring;
        · rw_mod_cast [ ← Finset.card_union_of_disjoint ( Finset.disjoint_sdiff ), Finset.union_sdiff_of_subset ( excSet_subset BS a k ) ];
        · ring;
      have hck : (Nk : ℝ) ≥ 2 * e0 + 13 := by
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
        have := hden ( 2 ^ k ) ( by exact_mod_cast hk4 ) ; norm_num at *;
        rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ], Real.log_pos one_lt_two ];
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
        exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
      rw [ ← @Int.cast_le ℝ ] ; norm_num ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k ]
    have hm' : (32 : ℤ) * |coldLabel BS a (k + 1)| ≤ (2 ^ (k + 1) : ℤ) * Nk1 := by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by
        exact le_trans hk3 ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ( by
        unfold boundarySet at hk6; aesop; );
      rw [ ← @Int.cast_le ℝ ] ; push_cast ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k, pow_succ' ( 2 : ℝ ) k ]
    have hck : (ck : ℝ) ≥ Nk / 2 := by
      have hNk_ge : (Nk : ℝ) ≥ 2 * e0 + 13 := by
        have := hden ( 2 ^ k ) ( by simpa using hk4 ) ; norm_num at *;
        have := BS.hdensity k hk1 ( by linarith ) ; norm_num at *;
        rw [ div_le_iff₀ ] at this <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith [ show ( 2 : ℝ ) ^ 0 = 1 by norm_num ] ) ) ) ( Real.log_pos one_lt_two ) ] ;
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) ; norm_num at * ; linarith [ show ( ck : ℝ ) = Nk - ( excSet BS a k |> Finset.card ) by exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card <| excSet_subset BS a k ] ;
    have hck1 : (ck1 : ℝ) ≥ Nk1 - e0 := by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by
        exact le_trans hk3 ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ( by
        exact Finset.mem_filter.mp hk6 |>.2.2.1 );
      simp +zetaDelta at *;
      rw [ Finset.card_sdiff ] ; norm_num [ this ];
      rw [ Nat.cast_sub ];
      · rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a ( k + 1 ) ) ] ; linarith;
      · exact Finset.card_le_card fun x hx => by aesop;
    have hck2 : (ck : ℝ) ≥ Nk - e0 := by
      have := hCBF BS a k hk1 ( by linarith ) hk3 ( by
        exact Finset.mem_filter.mp hk6 |>.2.1 ) ; norm_num at *;
      have hck2 : (ck : ℝ) = Nk - (excSet BS a k).card := by
        exact eq_sub_of_add_eq <| mod_cast Finset.card_sdiff_add_card_eq_card <| Finset.filter_subset _ _;
      linarith
    have hck3 : (ck1 : ℝ) - 1 ≥ Nk1 - e0 - 1 := by
      linarith
    have hck4 : ((ck1 : ℝ) - 1) * (ck : ℝ) ^ 3 / (2 ^ 13 * (2 ^ k : ℝ) ^ 2) ≤ Xen BS a k := by
      apply mismatch_penalty_with_exceptions BS (toPlain BS a) k (coldLabel BS a k) (coldLabel BS a (k + 1)) (by
      unfold boundarySet at hk6; aesop;) (excSet BS a k) (excSet BS a (k + 1)) (excSet_subset BS a k) (excSet_subset BS a (k + 1)) (by
      exact hCBF BS a k hk1 ( by linarith ) hk3 ( by unfold boundarySet at hk6; aesop ) |>.2.2) (by
      have := hCBF BS a ( k + 1 ) ( by linarith ) ( by linarith ) ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : k + 1 ≥ k ) ] ) ( by
        unfold boundarySet at hk6; aesop; ) ; aesop;) hNk hm hm'
    exact (by
    refine le_trans ?_ hck4;
    unfold Pifloor; gcongr;
    · exact pow_nonneg ( sub_nonneg_of_le <| by linarith [ show ( Nk : ℝ ) ≥ 2 * e0 + 13 by
                                                            have := BS.hdensity k hk1 ( by linarith ) ; norm_num at *;
                                                            have := hden ( 2 ^ k ) ( by exact_mod_cast hk4 ) ; norm_num at *;
                                                            rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) * Real.log 2 > 0 by exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; linarith ) ) ) ( Real.log_pos one_lt_two ) ] ] ) _;
    · have := BS.hdensity ( k + 1 ) ( by linarith [ show k + 1 ≥ BS.k0 from by linarith ] ) ( by linarith ) ; norm_num at *;
      refine' Nat.pos_of_ne_zero _;
      intro h; norm_num [ h ] at *;
      have := hden ( 2 ^ ( k + 1 ) ) ( by exact_mod_cast hk4.trans ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_succ _ ) ) ) ; norm_num at *;
      rw [ div_le_iff₀ ] at * <;> nlinarith [ show 0 < ( k + 1 : ℝ ) * Real.log 2 by positivity, show ( 2 : ℝ ) ^ ( k + 1 ) > 0 by positivity ];
    · have := BS.hdensity k hk1 ( by linarith ) ; norm_num [ Real.log_pow ] at this;
      have := hden ( 2 ^ k ) ( mod_cast hk4 ) ; norm_num at *;
      rw [ div_le_iff₀ ] at * <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ], Real.log_pos one_lt_two, mul_pos ( show ( k : ℝ ) > 0 by norm_cast; linarith [ show k > 0 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ Nat.le_ceil X0cbf ] ) ] ) ( Real.log_pos one_lt_two ) ])

/-! ## G7 support. Elementary Gaussian integer-sum bound (note 38 §7) -/

/-
**Gaussian integer-sum lemma (note 38 §7, step II).**  For `0 < A ≤ 1`,
    `∑_{m ∈ ℤ} exp(-A·m²) ≤ 1 + 6/√A`.

    Proof: the `m = 0` term contributes `1`; by symmetry the rest is
    `2·∑_{m ≥ 1} exp(-A·m²)`.  Split that tail at `1/√A`: for `m ≤ 1/√A` use
    `exp ≤ 1` (at most `1/√A + 1` terms — bounded by `2/√A`), and for
    `m > 1/√A` use `m² ≥ m/√A` so `exp(-A·m²) ≤ exp(-√A·m)`, a geometric tail
    summing to `≤ 1/(√A·(1 - e^{-√A})) ≤ 2/(√A·√A)`… ; collecting gives the
    stated `1 + 6/√A`.
-/
lemma gaussian_int_sum_le (A : ℝ) (hA0 : 0 < A) (hA1 : A ≤ 1) :
    ∑' m : ℤ, Real.exp (-A * (m : ℝ) ^ 2) ≤ 1 + 6 / Real.sqrt A := by
  -- Let s := Real.sqrt A, so 0 < s ≤ 1 and s^2 = A (since 0 < A ≤ 1).
  set s := Real.sqrt A with hs_def
  have hs_pos : 0 < s := by
    exact Real.sqrt_pos.mpr hA0
  have hs_le_one : s ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, by linarith ⟩
  have hs_sq_eq_A : s^2 = A := by
    exact Real.sq_sqrt hA0.le;
  -- The sum over ℤ is 1 + 2 * ∑'_{n≥1} exp(-A*n^2).
  have h_sum_decomp : ∑' m : ℤ, Real.exp (-A * m ^ 2) = 1 + 2 * ∑' n : ℕ, Real.exp (-A * (n + 1) ^ 2) := by
    have h_sum_decomp : ∑' m : ℤ, Real.exp (-A * m ^ 2) = ∑' m : ℕ, Real.exp (-A * m ^ 2) + ∑' m : ℕ, Real.exp (-A * (-(m + 1) : ℤ) ^ 2) := by
      rw [ ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
      rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
      · norm_num [ Equiv.intEquivNatSumNat ];
      · have h_summable : Summable (fun n : ℕ => Real.exp (-A * n ^ 2)) := by
          have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hA0 ) );
          exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
        simpa using h_summable;
      · norm_num [ Equiv.intEquivNatSumNat ];
        have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ) );
        exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; nlinarith;
    rw [ h_sum_decomp, Summable.tsum_eq_zero_add ] <;> norm_num ; ring;
    have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hA0 ) );
    exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
  -- For 1 ≤ n ≤ N: exp(-A n^2) ≤ 1; there are ≤ N ≤ 1/s such terms, contributing ≤ 1/s.
  have h_tail_bound : ∑' n : ℕ, Real.exp (-A * (n + 1) ^ 2) ≤ ∑ n ∈ Finset.range (Nat.floor (1 / s)), Real.exp (-A * (n + 1) ^ 2) + ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) := by
    rw [ ← Summable.sum_add_tsum_nat_add ];
    refine' add_le_add le_rfl ( Summable.tsum_le_tsum _ _ _ );
    · intro i; rw [ ← hs_sq_eq_A ] ; ring_nf; norm_num;
      nlinarith only [ show ( 0 : ℝ ) ≤ s * i by positivity, show ( 0 : ℝ ) ≤ s * ⌊s⁻¹⌋₊ by positivity, show ( 0 : ℝ ) ≤ s ^ 2 * i by positivity, show ( 0 : ℝ ) ≤ s ^ 2 * ⌊s⁻¹⌋₊ by positivity, Nat.lt_floor_add_one ( s⁻¹ ), mul_inv_cancel₀ ( ne_of_gt hs_pos ), hs_pos, hs_le_one ];
    · have h_summable : Summable (fun n : ℕ => Real.exp (-A * n ^ 2)) := by
        have := Real.summable_exp_nat_mul_of_ge ( show -A < 0 by linarith ) ( show ∀ n : ℕ, ( n : ℝ ) ≤ n ^ 2 by intros n; norm_cast; nlinarith );
        convert this using 1;
      exact_mod_cast h_summable.comp_injective ( add_left_injective ( ⌊1 / s⌋₊ + 1 ) );
    · have h_geo_series : Summable (fun n : ℕ => (Real.exp (-s)) ^ (n + Nat.floor (1 / s) + 1)) := by
        exact Summable.comp_injective ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ Real.exp_lt_one_iff ] ; linarith ) ) fun a b h => by simpa using h;
      convert h_geo_series using 2 ; norm_num [ ← Real.exp_nat_mul ] ; ring;
    · have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( show -A < 0 by linarith ) );
      exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith ) this;
  -- The tail ∑_{n≥1} exp(-s*n) = exp(-s)/(1-exp(-s)) = 1/(exp s - 1) ≤ 1/s (because exp s - 1 ≥ s for all s).
  have h_tail_sum : ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) ≤ 1 / s := by
    have h_tail_sum : ∑' n : ℕ, Real.exp (-s * (n + Nat.floor (1 / s) + 1)) = Real.exp (-s * (Nat.floor (1 / s) + 1)) / (1 - Real.exp (-s)) := by
      convert HasSum.tsum_eq ( HasSum.mul_left _ <| hasSum_geometric_of_lt_one ( by positivity ) <| show Real.exp ( -s ) < 1 from by rw [ Real.exp_lt_one_iff ] ; linarith ) using 1 ; norm_num [ ← Real.exp_nat_mul ] ; ring;
      exact tsum_congr fun n => by rw [ ← Real.exp_add ] ; ring;
    rw [ h_tail_sum, div_le_div_iff₀ ] <;> norm_num [ Real.exp_neg ];
    · field_simp;
      rw [ mul_comm ];
      gcongr;
      · exact le_mul_of_one_le_right hs_pos.le ( by linarith );
      · linarith [ Real.add_one_le_exp s ];
    · exact inv_lt_one_of_one_lt₀ <| by norm_num; positivity;
    · positivity;
  -- For 1 ≤ n ≤ N: exp(-A n^2) ≤ 1; there are ≤ N ≤ 1/s such terms, contributing ≤ 1/s.
  have h_tail_bound : ∑ n ∈ Finset.range (Nat.floor (1 / s)), Real.exp (-A * (n + 1) ^ 2) ≤ Nat.floor (1 / s) := by
    exact le_trans ( Finset.sum_le_sum fun _ _ => Real.exp_le_one_iff.mpr <| by nlinarith ) <| by norm_num;
  ring_nf at *;
  norm_num [ sub_eq_add_neg, add_comm, add_left_comm, add_assoc ] at * ; nlinarith [ Nat.floor_le ( inv_nonneg.mpr hs_pos.le ), mul_inv_cancel₀ hs_pos.ne' ]

/-! ## G7. Prop 8.1 — global control partition (note 34 G7) -/

/-- The "main arc" set `𝔐_C` (note 34 G6): global assignments that are globally
    diagonal with a small common label `|m| ≤ C/sigmaCtrl`. -/
def mainArc (BS : BlockSystem) (C : ℝ) : Set (GlobalAssignment BS) :=
  {a | ∃ m : ℤ, |(m : ℝ)| ≤ C / sigmaCtrl BS ∧
        ∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (m : ZMod p.1)}

end GlobalControl

end