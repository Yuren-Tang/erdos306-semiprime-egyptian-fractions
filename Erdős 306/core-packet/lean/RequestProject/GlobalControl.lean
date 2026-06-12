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
theorem global_levelset (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (k0min : ℕ) (A : ℝ), 0 < A ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) *
            Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  sorry

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

/-- **G7 (global control partition, Prop 8.1), final useful form.**  With the
    construction fixed (`k₀ ≥ k₀(c,η)`), the Peierls floor beats the
    `exp(A * numBlocks BS)` factor.  Thus the off-main-arc Laplace sum is bounded
    by an arbitrarily small `η/sigmaCtrl` term plus the one-dimensional Gaussian
    tail.

    **Status**: named `sorry` — Laplace/dyadic summation of `global_levelset`
    (via `SBEEAssembly.partfun_series_bound`) plus the G6 main-arc localization
    (note 34 G7).  Depends on the still-open `global_levelset`. -/
theorem global_control_partition (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (η + Ctail * Real.exp (-C ^ 2 * c / 2)) /
          sigmaCtrl BS := by
  sorry

end GlobalControl

end