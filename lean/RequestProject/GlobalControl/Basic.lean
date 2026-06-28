/-
# Global control foundations

Block systems, finite global assignments, the control energy, block restriction,
and comparison of the global and block scales.
-/
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
  intro p hp hp'; cases lt_or_gt_of_ne hkk <;> have := BS.hwindow k p hp <;> have := BS.hwindow k' p hp' <;> simp_all +decide;
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
    rw [Finset.card_pi] at h_card_le
    exact h_card_le
  · grind

/-
The internal-block energy `QP (BS.P k) (restrict BS a k)` equals the
    `internalPairs`-encoded sub-sum of `Qctrl`.
-/
lemma QP_restrict_eq_internal (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ) :
    QP (BS.P k) (restrict BS a k)
      = ∑ pq ∈ internalPairs BS k,
          ((Hglob (toPlain BS a) pq.1 pq.2 : ℝ) / ((pq.1 : ℝ) * pq.2)) ^ 2 := by
  refine' Finset.sum_bij ( fun pq hpq => ( pq.1.1, pq.2.1 ) ) _ _ _ _ <;> simp +decide;
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
      change (BS.P k ×ˢ BS.P (k + 1)).card ≤ 2 ^ k * 2 ^ (k + 1) at h_card_bipartite
      have h_sum_bipartite : ∑ pq ∈ (BS.P k ×ˢ BS.P (k + 1)), (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤ (2 ^ k * 2 ^ (k + 1)) * (1 / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2) := by
        have h_term : ∀ x ∈ BS.P k ×ˢ BS.P (k + 1),
            (1 : ℝ) / ((x.1 : ℝ) * x.2) ^ 2 ≤
              1 / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2 := by
          intro x hx
          exact one_div_le_one_div_of_le (by positivity) <|
            pow_le_pow_left₀ (by positivity)
              (mul_le_mul
                (show (x.1 : ℝ) ≥ 2 ^ k by
                  exact_mod_cast BS.hwindow k x.1 (Finset.mem_product.mp hx).1 |>.1)
                (show (x.2 : ℝ) ≥ 2 ^ (k + 1) by
                  exact_mod_cast BS.hwindow (k + 1) x.2 (Finset.mem_product.mp hx).2 |>.1)
                (by positivity) (by positivity)) 2
        calc
          ∑ pq ∈ (BS.P k ×ˢ BS.P (k + 1)),
              (1 : ℝ) / ((pq.1 : ℝ) * pq.2) ^ 2 ≤
              ∑ _ ∈ (BS.P k ×ˢ BS.P (k + 1)),
                (1 : ℝ) / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2 :=
            Finset.sum_le_sum h_term
          _ =
                ((BS.P k ×ˢ BS.P (k + 1)).card : ℝ) *
                  (1 / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2) := by simp
          _ ≤ (2 ^ k * 2 ^ (k + 1) : ℝ) *
                  (1 / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_bipartite) (by positivity)
      have h_algebra :
          (2 ^ k * 2 ^ (k + 1) : ℝ) *
              (1 / ((2 ^ k : ℝ) * (2 ^ (k + 1) : ℝ)) ^ 2) =
            (1 / 4 : ℝ) ^ k * (1 / 2) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_succ]
        field_simp
        have h_power : ((2 : ℝ) ^ 2) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
          rw [← pow_mul, ← pow_mul, mul_comm]
        rw [div_pow, one_pow, h_power]
        field_simp
      simpa only [bipartitePairs, add_comm] using h_sum_bipartite.trans_eq h_algebra
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
    erw [ geom_sum_Ico ] <;> ring_nf <;> norm_num;
    linarith [ BS.hk ];
  norm_num [ ← Finset.sum_mul _ _ _ ] at *;
  linarith [ pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 4 ) ( by norm_num ) hk0, show ( ∑ x ∈ Ico BS.k0 BS.K, ( 1 / 4 : ℝ ) ^ x ) ≤ ( 4 / 3 ) * ( 1 / 4 ) ^ BS.k0 by exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Ico.mp hx |>.1, Finset.mem_Ico.mp hx |>.2.le ⟩ ) fun _ _ _ => by positivity ) h_geo_sum ]

/-
**Lemma S2' (note 38 §4, geometric form).**  The global control deviation
    is bounded by `4·2^{-k₀}`.
-/
lemma sigmaCtrl_le_geom (BS : BlockSystem) (_hk0 : 2 ≤ BS.k0) :
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
          intro a b ha hb ha' hb'; have := BS.hwindow k a ha; have := BS.hwindow ( k + 1 ) b hb; have := BS.hwindow l a ha'; have := BS.hwindow ( l + 1 ) b hb';
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
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( h_sigmaP_bound BS hBS ) ?_ ) <;> ring_nf <;> norm_num;
  · norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos, show BS.k0 > 0 by linarith ];
  · positivity

end GlobalControl

end
