import RequestProject.GlobalControl

/-!
# G6 — localization dichotomy (`g6_localization`)

This leaf proves the G6 localization dichotomy of note 34 §G6 / note 43:
an off-main-arc global assignment is either above the global energy floor
`globalControlFloor`, or it lies in the diagonal sector `diagSector`.

The decomposition follows note 43 (L1–L5):

* `Rw_mono` (L1) — monotonicity of the forcing floor `Rw`.
* `Rw_le_Pifloor` (L2) — the forcing floor at `k0` is below the boundary penalty
  floor at any later block (density + power-beats-poly-log).
* the Case-D collapse to a globally diagonal label (L3), using
  `cold_no_exceptions`.
* `crtRepr_eq_label_of_small` (L5 core) and `diagonal_Qctrl` (the exact
  quadratic energy identity).

The `globalControlFloor` / `diagSector` definitions are byte-identical to the
ones in `GlobalControlG7.lean` (as required so the G7 assembly can consume this
result).
-/

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-! ## Definitions (byte-identical to `GlobalControlG7.lean`) -/

/-- The G6 energy floor: the smaller of the Theorem-B forcing floor `Rw c2 k0`
and the boundary penalty floor `Π(e0,k0)` at the first block. -/
def globalControlFloor (BS : BlockSystem) (c2 e0 : ℝ) : ℝ :=
  min (Rw c2 BS.k0) (Pifloor BS e0 BS.k0)

/-- The "diagonal sector": globally diagonal with a label outside the main-arc
window and *exact* quadratic control energy `m² σ²`. -/
def diagSector (BS : BlockSystem) (C : ℝ) (a : GlobalAssignment BS) : Prop :=
  ∃ m : ℤ,
    (∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (m : ZMod p.1)) ∧
    C / sigmaCtrl BS < |(m : ℝ)| ∧
    Qctrl BS a = (m : ℝ) ^ 2 * (sigmaCtrl BS) ^ 2

/-! ## Energy bookkeeping: single block / bipartite energies are `≤ Qctrl` -/

/-
The internal energy of a single block is at most the global control energy.
-/
lemma blockEnergy_le_Qctrl (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Icc BS.k0 BS.K) :
    blockEnergy BS a k ≤ Qctrl BS a := by
  refine' le_trans _ ( GlobalControl.energy_splits BS a |> le_trans ( le_add_of_nonneg_right _ ) );
  · exact Finset.single_le_sum ( fun x _ => show 0 ≤ QP ( BS.P x ) ( restrict BS a x ) from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) hk;
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
The bipartite cross-energy at level `k` is at most the global control energy.
-/
lemma Xen_le_Qctrl (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ)
    (hk : k ∈ Finset.Ico BS.k0 BS.K) :
    Xen BS a k ≤ Qctrl BS a := by
  refine' le_trans _ ( GlobalControl.energy_splits BS a |> le_trans ( le_add_of_nonneg_left _ ) );
  · exact Finset.single_le_sum ( fun x hx => Finset.sum_nonneg fun y hy => sq_nonneg _ ) hk |> le_trans ( by rfl );
  · exact Finset.sum_nonneg fun _ _ => QP_nonneg _ _

/-! ## L1 — monotonicity of the forcing floor `Rw` -/

/-- One monotonicity step of `Rw` for `k ≥ 4` (verified, supplied by note 43). -/
lemma Rw_mono_step (c2 : ℝ) (hc2 : 0 < c2) (k : ℕ) (hk : 4 ≤ k) :
    Rw c2 k ≤ Rw c2 (k+1) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (4:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hcube : ((k:ℝ)+1)^3 ≤ 2 * (k:ℝ)^3 := by
    nlinarith [hkR, mul_nonneg (show (0:ℝ) ≤ (k:ℝ)-4 by linarith) (sq_nonneg (k:ℝ)),
      mul_nonneg (show (0:ℝ) ≤ (k:ℝ) by linarith) (show (0:ℝ) ≤ (k:ℝ)-3 by linarith)]
  have hrw : ∀ j:ℕ, 1 ≤ j → Rw c2 j = (c2/(Real.log 2)^3) * ((2:ℝ)^j/(j:ℝ)^3) := by
    intro j hj
    have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hj
    unfold Rw; rw [Real.log_pow, mul_pow]; field_simp
  have key : (2:ℝ)^k / (k:ℝ)^3 ≤ (2:ℝ)^(k+1) / ((k:ℝ)+1)^3 := by
    have hps : (2:ℝ)^(k+1) = 2 * 2^k := by rw [pow_succ]; ring
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (2:ℝ)^k * ((k:ℝ)+1)^3 ≤ 2^k * (2*(k:ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have h2 : (2:ℝ)^k * (2*(k:ℝ)^3) = 2^(k+1)*(k:ℝ)^3 := by rw [hps]; ring
    linarith [h1, h2]
  rw [hrw k (by omega), hrw (k+1) (by omega)]
  push_cast
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- **L1 monotonicity of `Rw`.**  For `c2 > 0` and `4 ≤ k0 ≤ k`,
`Rw c2 k0 ≤ Rw c2 k`. -/
lemma Rw_mono (c2 : ℝ) (hc2 : 0 < c2) {k0 k : ℕ} (hk0 : 4 ≤ k0) (hkk : k0 ≤ k) :
    Rw c2 k0 ≤ Rw c2 k := by
  induction k, hkk using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
      exact le_trans ih (Rw_mono_step c2 hc2 n (le_trans hk0 hn))

/-! ## L5 core — CRT centered-rep equals the label when the label is small -/

/-
**L5 core (`crtRepr_eq_label_of_small`).**  If `ap ≡ m (mod p)`,
`aq ≡ m (mod q)`, and `2·|m| < p·q`, then the centered CRT representative
`crtRepr p q ap aq` equals `m`.
-/
lemma crtRepr_eq_label_of_small (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (m : ℤ) (ap : ZMod p) (aq : ZMod q)
    (hap : ap = (m : ZMod p)) (haq : aq = (m : ZMod q))
    (hsmall : 2 * |m| < (p : ℤ) * (q : ℤ)) :
    crtRepr p q ap aq = m := by
  grind +suggestions

/-! ## L2 — the forcing floor at `k0` is below the boundary penalty floor -/

/-
Exponential eventually dominates any affine function: for any `D`, there is
a threshold past which `D·(k+1) ≤ 2^k`.
-/
lemma exists_pow_ge_affine (D : ℝ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → D * ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
  -- The sequence $\frac{k+1}{2^k}$ tends to $0$ as $k$ tends to infinity.
  have h_seq_zero : Filter.Tendsto (fun k : ℕ => (k + 1 : ℝ) / 2 ^ k) Filter.atTop (nhds 0) := by
    refine' squeeze_zero_norm' _ tendsto_inv_atTop_nhds_zero_nat;
    norm_num;
    exact ⟨ 8, fun n hn => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at * ; nlinarith ⟩;
  rcases Metric.tendsto_atTop.mp h_seq_zero ( 1 / ( Max.max D 1 ) ) ( by positivity ) with ⟨ N, hN ⟩;
  simp +zetaDelta at *;
  exact ⟨ N, fun n hn => by have := hN n hn; rw [ div_lt_iff₀ ( by positivity ) ] at this; rw [ abs_of_nonneg ( by positivity ) ] at this; nlinarith [ le_max_left D 1, le_max_right D 1, inv_mul_cancel₀ ( show ( max D 1 ) ≠ 0 by positivity ), pow_pos ( zero_lt_two' ℝ ) n ] ⟩

/-
**L2 core (`Pifloor_ge_Rw`).**  For `k` large enough (density past the
exception threshold, exponential-beats-linear), the boundary penalty floor at
block `k` dominates the forcing floor at `k`.  Single-index analytic core.
-/
lemma Pifloor_ge_Rw (c2 e0 : ℝ) (he0 : 0 < e0) :
    ∃ k0min : ℕ, 4 ≤ k0min ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 →
        ∀ k, BS.k0 ≤ k → k < BS.K → Rw c2 k ≤ Pifloor BS e0 k := by
  obtain ⟨Na, hNa⟩ := exists_pow_ge_affine (4 * e0 * Real.log 2)
  obtain ⟨Nb, hNb⟩ := exists_pow_ge_affine (2 * (e0 + 1) * Real.log 2)
  obtain ⟨Nc, hNc⟩ := exists_pow_ge_affine (2 ^ 20 * c2 * Real.log 2);
  refine' ⟨ 4 + Na + Nb + Nc, _, _ ⟩;
  · linarith;
  · intro BS hBS k hk hk'; rw [ Rw, Pifloor ] ;
    -- Apply the density bounds from `hdensity`.
    have h_density_k : (BS.P k).card ≥ (2 ^ k : ℝ) / (2 * (k : ℝ) * Real.log 2) := by
      have := BS.hdensity k ( by linarith ) ( by linarith ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    have h_density_k1 : (BS.P (k + 1)).card ≥ (2 * 2 ^ k : ℝ) / (2 * ((k + 1) : ℝ) * Real.log 2) := by
      have := BS.hdensity ( k + 1 ) ( by linarith ) ( by linarith ) ; norm_num [ Real.log_pow ] at * ; ring_nf at * ; aesop;
    -- Apply the bounds from `hNa`, `hNb`, and `hNc`.
    have h_bounds : (2 ^ k : ℝ) / (4 * (k : ℝ) * Real.log 2) ≤ (BS.P k).card - e0 ∧ (2 ^ k : ℝ) / (2 * ((k + 1) : ℝ) * Real.log 2) ≤ (BS.P (k + 1)).card - e0 - 1 := by
      constructor;
      · rw [ ge_iff_le, div_le_iff₀ ] at * <;> try positivity;
        · nlinarith [ hNa k ( by linarith ), Real.log_pos one_lt_two, show ( k : ℝ ) ≥ 4 by norm_cast; linarith ];
        · exact mul_pos ( mul_pos two_pos ( Nat.cast_pos.mpr ( by linarith ) ) ) ( Real.log_pos one_lt_two );
        · exact mul_pos ( mul_pos ( by norm_num ) ( Nat.cast_pos.mpr ( by linarith ) ) ) ( Real.log_pos ( by norm_num ) );
      · rw [ ge_iff_le, div_le_iff₀ ] at * <;> try positivity;
        · nlinarith [ hNb k ( by linarith ), Real.log_pos one_lt_two ];
        · exact mul_pos ( mul_pos two_pos ( Nat.cast_pos.mpr ( by linarith ) ) ) ( Real.log_pos one_lt_two );
    refine' le_trans _ ( div_le_div_of_nonneg_right ( mul_le_mul h_bounds.2 ( pow_le_pow_left₀ _ h_bounds.1 3 ) _ _ ) _ );
    · rw [ div_mul_eq_mul_div, div_div, div_le_div_iff₀ ] <;> norm_num [ Real.log_pow ] <;> ring_nf <;> norm_num [ Real.log_pos ];
      · field_simp;
        rw [ mul_div_cancel_left₀ _ ( by norm_cast; linarith ) ] ; ring_nf at *;
        convert mul_le_mul_of_nonneg_right ( hNc k ( by linarith ) ) ( pow_nonneg ( by positivity : ( 0 : ℝ ) ≤ 2 ) ( k * 3 ) ) using 1 <;> ring;
      · exact pow_pos ( Nat.cast_pos.mpr ( by linarith ) ) _;
      · exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( by norm_num ) ) ) zero_le_two ) ( mul_pos ( Real.log_pos ( by norm_num ) ) zero_lt_two );
    · positivity;
    · positivity;
    · exact le_trans ( by positivity ) h_bounds.2;
    · positivity

/-- **L2 (`Rw_le_Pifloor`).**  For `k0` large enough (density past the
exception threshold, power-beats-poly-log), the forcing floor at `k0` is below
the boundary penalty floor at any block `k0 ≤ k < K`. -/
lemma Rw_le_Pifloor (c2 e0 : ℝ) (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∃ k0min : ℕ, 4 ≤ k0min ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
        ∀ k, BS.k0 ≤ k → k < BS.K → Rw c2 BS.k0 ≤ Pifloor BS e0 k := by
  obtain ⟨k1, hk1, hPR⟩ := Pifloor_ge_Rw c2 e0 he0
  refine ⟨k1, hk1, fun BS hk0 _ k hk0k hkK => ?_⟩
  exact le_trans (Rw_mono c2 hc2 (le_trans hk1 hk0) hk0k) (hPR BS hk0 k hk0k hkK)

/-! ## Control-pair size facts -/

/-
Endpoints of a control pair are distinct.
-/
lemma ctrlPairs_ne (BS : BlockSystem) {pq : ℕ × ℕ} (h : pq ∈ ctrlPairs BS) :
    pq.1 ≠ pq.2 := by
  contrapose! h; simp_all +decide [ ctrlPairs, internalPairs, bipartitePairs ] ;
  intro x hx₁ hx₂ hx₃ hx₄; have := blocks_disjoint BS ( show x ≠ x + 1 from by linarith ) ; simp_all +decide [ Finset.disjoint_left ] ;

/-
For `2 ≤ k0`, every control pair has product strictly larger than
`2^(2·k0)`.
-/
lemma ctrlPairs_prod_lower (BS : BlockSystem) (hk0 : 2 ≤ BS.k0) {pq : ℕ × ℕ}
    (h : pq ∈ ctrlPairs BS) :
    (2 : ℝ) ^ (2 * BS.k0) < (pq.1 : ℝ) * (pq.2 : ℝ) := by
  -- Both endpoints are prime and ≥ 2^k0, hence strictly > 2^k0.
  have h1 : 2 ^ BS.k0 < pq.1 := by
    obtain ⟨k, hk⟩ : ∃ k, pq.1 ∈ BS.P k ∧ BS.k0 ≤ k ∧ k ≤ BS.K := by
      obtain ⟨k, hk⟩ : ∃ k, pq.1 ∈ BS.P k ∧ k ∈ Finset.Icc BS.k0 BS.K := by
        have h_mem : pq.1 ∈ blockSupport BS := by
          exact ctrlPairs_mem_blockSupport BS h |>.1
        unfold blockSupport at h_mem; aesop;
      aesop;
    have := BS.hwindow k pq.1 hk.1;
    by_cases h_eq : pq.1 = 2 ^ BS.k0;
    · have := BS.hprime k pq.1 hk.1; simp_all +decide [ Nat.prime_iff ] ;
    · exact lt_of_le_of_ne ( Nat.le_trans ( pow_le_pow_right₀ ( by decide ) hk.2.1 ) this.1 ) ( Ne.symm h_eq )
  have h2 : 2 ^ BS.k0 < pq.2 := by
    cases' Finset.mem_union.mp ( show pq ∈ ( Finset.biUnion ( Finset.Icc BS.k0 BS.K ) ( internalPairs BS ) ) ∪ ( Finset.biUnion ( Finset.Ico BS.k0 BS.K ) ( bipartitePairs BS ) ) from h );
    · simp_all +decide [ Finset.mem_biUnion, internalPairs ];
      grind;
    · simp_all +decide [ bipartitePairs ];
      obtain ⟨ k, hk, hk₁, hk₂ ⟩ := ‹_›; have := BS.hwindow ( k + 1 ) pq.2 hk₂; simp_all +decide [ pow_succ' ] ;
      linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hk.1 ];
  norm_cast; rw [ pow_mul' ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) BS.k0 ] ;

/-! ## L5 — the diagonal energy identity -/

/-
**L5 (`diagonal_Qctrl`).**  If `a` is globally diagonal with label `m` and
`2·|m| < p·q` for every control pair, then `Qctrl a = m²·σ²`.
-/
lemma diagonal_Qctrl (BS : BlockSystem) (a : GlobalAssignment BS) (m : ℤ)
    (hdiag : ∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (m : ZMod p.1))
    (hsmall : ∀ pq ∈ ctrlPairs BS, 2 * |m| < (pq.1 : ℤ) * (pq.2 : ℤ)) :
    Qctrl BS a = (m : ℝ) ^ 2 * (sigmaCtrl BS) ^ 2 := by
  convert Finset.sum_congr rfl fun pq hpq => ?_ using 1;
  rotate_left;
  use fun pq => ( m : ℝ ) ^ 2 / ( pq.1 * pq.2 ) ^ 2;
  · rw [ Hglob, crtRepr_eq_label_of_small pq.1 pq.2 ( blockSupport_prime BS ( ctrlPairs_mem_blockSupport BS hpq |>.1 ) ) ( blockSupport_prime BS ( ctrlPairs_mem_blockSupport BS hpq |>.2 ) ) ( ctrlPairs_ne BS hpq ) m ];
    · ring;
    · exact if_pos ( ctrlPairs_mem_blockSupport BS hpq |>.1 ) |> fun h => h.trans ( hdiag ⟨ pq.1, ctrlPairs_mem_blockSupport BS hpq |>.1 ⟩ );
    · convert hdiag ⟨ pq.2, ctrlPairs_mem_blockSupport BS hpq |>.2 ⟩ using 1;
      exact dif_pos ( ctrlPairs_mem_blockSupport BS hpq |>.2 );
    · exact hsmall pq hpq;
  · unfold sigmaCtrl; rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => by positivity ] ; simp +decide [ div_eq_mul_inv, mul_comm, Finset.mul_sum _ _ _ ] ;

/-! ## L3 — Case D collapse: the substantive `cold_no_exceptions` step -/

/- **Bundled cold constants + the substantive `cold_no_exceptions` step.**

Produces the cold constants `c2,e0,X0` (a refinement of those produced by
`boundary_penalty_per_k`, with `c2` shrunk to be explicitly small), together with:
* the per-cold-block facts (small exception set, sharp label bound, conformity);
* the boundary penalty floor (`Pifloor ≤ Xen`);
* **`cold_no_exceptions`**: in the no-hot regime every cold block has an empty
  exception set.

The first two components are derived from `boundary_penalty_per_k` by
monotonicity in `c2`.  The third is the genuinely new G6 input (note 34 §G6),
proved in `cold_no_exceptions_core`. -/
/-- Monotonicity of the forcing floor in its constant: a smaller `c2` gives a
smaller `Rw`. -/
lemma Rw_le_of_c2_le {c c' : ℝ} (h : c ≤ c') (k : ℕ) : Rw c k ≤ Rw c' k := by
  have hlog : 0 ≤ Real.log ((2:ℝ) ^ k) :=
    Real.log_nonneg (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have ht : 0 ≤ (2:ℝ) ^ k / (Real.log (2 ^ k)) ^ 3 :=
    div_nonneg (by positivity) (pow_nonneg hlog 3)
  unfold Rw
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_right h ht

/-- A block that is cold for `c'` is cold for any smaller `c ≤ c'`. -/
lemma not_isHot_mono {c c' : ℝ} (h : c ≤ c') (BS : BlockSystem)
    (a : GlobalAssignment BS) (k : ℕ) (hni : ¬ isHot BS c a k) : ¬ isHot BS c' a k := by
  simp only [isHot, not_le] at *
  exact lt_of_lt_of_le hni (Rw_le_of_c2_le h k)

/-
**`cold_no_exceptions` core.**  With an *explicitly small* forcing constant
`c2 ≤ 1/2^21`, a cold block (`¬ isHot`) with a bounded exception set and a sharp
label bound has an *empty* exception set.  Proof: by `exception_count_bound` the
exception count is `≤ 2^15·R·X²/((1-ρ)N³)` with `R = blockEnergy < Rw c2 k`; the
density `N ≥ X/(2 log X)` and `c2 ≤ 1/2^21` make this `< 1`, hence `0`.
-/
lemma cold_no_exceptions_core (c2 e0 : ℝ) (hc2 : 0 < c2) (hc2small : c2 ≤ 1 / 2 ^ 21)
    (he0 : 0 < e0) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
      BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
      ((excSet BS a k).card : ℝ) ≤ e0 →
      |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 →
      excSet BS a k = ∅ := by
  obtain ⟨ X0r, hX0r_pos, hX0r ⟩ := GlobalControl.Rw_large 1 c2 hc2 ; obtain ⟨ X0d, hX0d_pos, hX0d ⟩ := SBEEForcing.exists_X0_const_logbnd ( 8 * e0 + 64 ) ; use max 16 ( max X0r X0d ) ; norm_num at *;
  intro BS a k hk0 hkK hk16 hkX0r hkX0d hnot_hot hexc hlabel
  have hblock : 4 ≤ k := by
    exact le_of_not_gt fun h => by interval_cases k <;> norm_num at hk16;
  have hX : 16 ≤ 2 ^ k := by
    exact_mod_cast hk16
  have hXr : 1 ≤ k := by
    linarith
  have hXd : X0d ≤ (2 ^ k : ℝ) := by
    exact_mod_cast hkX0d
  have hX0r' : X0r ≤ (2 ^ k : ℝ) := by
    exact_mod_cast hkX0r
  have hR : 1 ≤ Rw c2 k := by
    exact hX0r k hXr hX0r'
  have hclass : (1 - 1 / 4 : ℝ) * (BS.P k).card ≤ (classCount BS a k (coldLabel BS a k) : ℝ) := by
    have hclass : (classCount BS a k (coldLabel BS a k) : ℝ) = (BS.P k).card - (excSet BS a k).card := by
      rw [ ← conform_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk0, hkK ⟩ ), Finset.card_sdiff ];
      rw [ Finset.inter_eq_left.mpr ( excSet_subset BS a k ), Nat.cast_sub ( Finset.card_le_card ( excSet_subset BS a k ) ) ]
    generalize_proofs at *;
    have := BS.hdensity k hk0 hkK; norm_num at *; (
    have := hX0d ( 2 ^ k ) ( by simpa using hXd ) ; norm_num at * ; ( rw [ div_le_iff₀ ] at * <;> try positivity ) ;
    nlinarith [ show ( 0 : ℝ ) < k * Real.log 2 by positivity ]);
  generalize_proofs at *;
  have hN : (BS.P k).card ≥ (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) := by
    exact BS.hdensity k hk0 hkK
  have hN32 : 32 ≤ (BS.P k).card := by
    have := hX0d ( 2 ^ k ) ( by exact_mod_cast hXd ) ; norm_num at *;
    rw [ div_le_iff₀ ( by positivity ) ] at hN;
    exact_mod_cast ( by nlinarith [ show ( 0 :ℝ ) < k * Real.log 2 by positivity ] : ( 32 :ℝ ) ≤ # ( BS.P k ) )
  have hNpos : 0 < (BS.P k).card := by
    linarith
  have hN_ge_4e0 : 4 * e0 ≤ (BS.P k).card := by
    have := hX0d ( 2 ^ k ) ( by simpa using hXd ) ; norm_num at *;
    rw [ div_le_iff₀ ( by positivity ) ] at hN ; nlinarith [ Real.log_pos one_lt_two, show ( k : ℝ ) ≥ 4 by norm_cast, show ( 2 : ℝ ) ^ k > 0 by positivity ] ;
  generalize_proofs at *;
  have hmsmall : |(coldLabel BS a k : ℝ)| ≤ (BS.P k).card * (2 ^ k : ℝ) / 16 := by
    exact hlabel.trans ( by gcongr ; norm_num )
  generalize_proofs at *;
  have hcount : (excSet BS a k).card ≤ 2 ^ 15 * Rw c2 k * (2 ^ k : ℝ) ^ 2 / ((1 - 1 / 4) * (BS.P k).card ^ 3) := by
    have hQ : QP (BS.P k) (restrict BS a k) ≤ Rw c2 k := by
      exact le_of_not_ge fun h => hnot_hot <| by unfold isHot; exact h;
    generalize_proofs at *;
    have := SBEEForcing.exception_count_bound ( 2 ^ k ) ( by linarith ) ( BS.P k ) ( by
      exact fun p hp => ⟨ BS.hprime k p hp, by linarith [ BS.hwindow k p hp ], by linarith [ BS.hwindow k p hp, show 2 ^ ( k + 1 ) = 2 * 2 ^ k by ring ] ⟩ ) ( by linarith ) ( 1 / 4 ) ( by linarith ) ( by linarith ) ( restrict BS a k ) ( coldLabel BS a k ) ( Rw c2 k ) ( by linarith ) ( by
      exact hQ ) ( by
      exact_mod_cast hmsmall ) ( by
      convert hclass using 1 )
    generalize_proofs at *;
    convert this using 1 ; norm_num [ excSet_card_eq ];
    · convert excSet_card_eq BS a k ( Finset.mem_Icc.mpr ⟨ hk0, hkK ⟩ ) using 1;
    · norm_cast
  generalize_proofs at *;
  -- Substitute the bounds into the inequality.
  have h_subst : (excSet BS a k).card ≤ 2 ^ 15 * (c2 * (2 ^ k : ℝ) / (Real.log (2 ^ k)) ^ 3) * (2 ^ k : ℝ) ^ 2 / ((1 - 1 / 4) * ((2 ^ k : ℝ) / (2 * Real.log (2 ^ k))) ^ 3) := by
    refine le_trans hcount ?_;
    gcongr;
    · exact mul_pos ( by norm_num ) ( pow_pos ( div_pos ( by positivity ) ( mul_pos zero_lt_two ( Real.log_pos ( by norm_cast; linarith ) ) ) ) _ );
    · exact le_rfl;
    · exact div_nonneg ( by positivity ) ( mul_nonneg zero_le_two ( Real.log_nonneg ( by norm_cast; linarith ) ) )
  generalize_proofs at *;
  -- Simplify the expression to show that it is less than 1.
  have h_simplified : (excSet BS a k).card ≤ 2 ^ 20 * c2 / 3 := by
    convert h_subst using 1 ; ring_nf ; norm_num [ Real.log_pow ] ; ring_nf ; norm_num [ show ( 2 : ℝ ) ^ k ≠ 0 by positivity, show ( Real.log 2 : ℝ ) ≠ 0 by positivity ] ;
    norm_num [ show k ≠ 0 by linarith, show ( 2 : ℝ ) ^ ( k * 3 ) ≠ 0 by positivity ];
    norm_num [ mul_assoc, ← mul_pow ]
  generalize_proofs at *;
  exact Finset.card_eq_zero.mp ( Nat.eq_zero_of_le_zero ( Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith ) ) )

lemma cold_no_exceptions :
    ∃ (c2 e0 X0 : ℝ), 0 < c2 ∧ 0 < e0 ∧ 0 < X0 ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        ((excSet BS a k).card : ℝ) ≤ e0 ∧
        |(coldLabel BS a k : ℝ)| ≤ ((BS.P k).card : ℝ) * ((2:ℝ) ^ k) / 64 ∧
        (∀ p ∈ BS.P k \ excSet BS a k,
          (toPlain BS a p : ZMod p) = ((coldLabel BS a k : ℤ) : ZMod p))) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k < BS.K → X0 ≤ (2:ℝ) ^ k → k ∈ boundarySet BS c2 a →
        Pifloor BS e0 k ≤ Xen BS a k) ∧
      (∀ (BS : BlockSystem) (a : GlobalAssignment BS) (k : ℕ),
        BS.k0 ≤ k → k ≤ BS.K → X0 ≤ (2:ℝ) ^ k → ¬ isHot BS c2 a k →
        excSet BS a k = ∅) := by
  obtain ⟨c2b, e0, X0b, hc2b, he0, hX0b, hcf, hbd⟩ := boundary_penalty_per_k
  obtain ⟨X0c, hX0c, hcore⟩ :=
    cold_no_exceptions_core (min c2b (1 / 2 ^ 21)) e0
      (lt_min hc2b (by positivity)) (min_le_right _ _) he0
  set c2 := min c2b (1 / 2 ^ 21) with hc2def
  have hc2 : 0 < c2 := lt_min hc2b (by positivity)
  have hle : c2 ≤ c2b := min_le_left _ _
  refine ⟨c2, e0, max X0b X0c, hc2, he0, by positivity, ?_, ?_, ?_⟩
  · -- cold facts: reduce to `c2b`
    intro BS a k hk0 hkK hX hcold
    exact hcf BS a k hk0 hkK (le_trans (le_max_left _ _) hX)
      (not_isHot_mono hle BS a k hcold)
  · -- boundary penalty: reduce to `c2b`
    intro BS a k hk0 hkK hX hbdry
    have hbdry' : k ∈ boundarySet BS c2b a := by
      rw [boundarySet, Finset.mem_filter] at hbdry ⊢
      exact ⟨hbdry.1, not_isHot_mono hle BS a k hbdry.2.1,
        not_isHot_mono hle BS a (k + 1) hbdry.2.2.1, hbdry.2.2.2⟩
    exact hbd BS a k hk0 hkK (le_trans (le_max_left _ _) hX) hbdry'
  · -- no exceptions: use the explicitly-small-`c2` core
    intro BS a k hk0 hkK hX hcold
    have hcoldb := not_isHot_mono hle BS a k hcold
    obtain ⟨hexc, hlabel, _⟩ := hcf BS a k hk0 hkK (le_trans (le_max_left _ _) hX) hcoldb
    exact hcore BS a k hk0 hkK (le_trans (le_max_right _ _) hX) hcold hexc hlabel

/-
With empty hot/boundary sets, `segStart` collapses to `k0`.
-/
lemma segStart_empty (BS : BlockSystem) (k : ℕ) :
    segStart BS (∅ : Finset ℕ) (∅ : Finset ℕ) k = BS.k0 := by
  induction' k using Nat.strong_induction_on with k ih;
  unfold segStart;
  grind

/-! ## Main theorem -/

/-
**G6 localization dichotomy** (note 34 §G6).  An off-main-arc assignment is
either above the global energy floor, or lies in the diagonal sector.
-/
set_option maxHeartbeats 1000000 in
theorem g6_localization :
    ∃ (k0loc : ℕ) (c2 e0 : ℝ), 0 < c2 ∧ 0 < e0 ∧
      ∀ (BS : BlockSystem), k0loc ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ a : GlobalAssignment BS, a ∉ mainArc BS C →
        globalControlFloor BS c2 e0 ≤ Qctrl BS a ∨ diagSector BS C a := by
  obtain ⟨c2, e0, X0, hc2, he0, hX0, hcf, hbd, hnoexc⟩ := GlobalControl.cold_no_exceptions;
  obtain ⟨kRwPi, hkRwPi4, hRwPi⟩ := GlobalControl.Rw_le_Pifloor c2 e0 hc2 he0;
  obtain ⟨N, hN⟩ : ∃ N : ℕ, X0 < 2 ^ N := by
    exact pow_unbounded_of_one_lt X0 one_lt_two;
  refine' ⟨ Max.max ( Max.max 4 kRwPi ) N, c2, e0, hc2, he0, fun BS hk0 hadm C hC a ha => _ ⟩;
  by_cases hH : (hotSet BS c2 a).Nonempty;
  · obtain ⟨ k, hk ⟩ := hH;
    refine' Or.inl ( le_trans _ ( blockEnergy_le_Qctrl BS a k _ ) );
    · refine' le_trans ( min_le_left _ _ ) _;
      refine' le_trans _ ( Finset.mem_filter.mp hk |>.2 );
      exact Rw_mono c2 hc2 ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hk |>.1 ), le_max_left ( max 4 kRwPi ) N, le_max_right ( max 4 kRwPi ) N, le_max_left 4 kRwPi, le_max_right 4 kRwPi ] ) ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hk |>.1 ), le_max_left ( max 4 kRwPi ) N, le_max_right ( max 4 kRwPi ) N, le_max_left 4 kRwPi, le_max_right 4 kRwPi ] );
    · exact Finset.mem_filter.mp hk |>.1;
  · by_cases hB : (boundarySet BS c2 a).Nonempty;
    · obtain ⟨ k, hk ⟩ := hB;
      refine' Or.inl ( le_trans _ ( le_trans ( hRwPi BS ( by linarith [ le_max_left ( max 4 kRwPi ) N, le_max_right ( max 4 kRwPi ) N, le_max_left 4 kRwPi, le_max_right 4 kRwPi ] ) hadm k ( by
        exact Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ) |>.1 ) ( by
        exact Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ) |>.2 ) ) ( le_trans ( hbd BS a k ( by
        exact Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ) |>.1 ) ( by
        exact Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ) |>.2 ) ( by
        exact le_trans hN.le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hk |>.1 ), le_max_right ( max 4 kRwPi ) N, le_max_right 4 kRwPi, le_max_left ( max 4 kRwPi ) N, le_max_left 4 kRwPi, le_max_right ( max 4 kRwPi ) N, le_max_right 4 kRwPi, hk0 ] ) ) ) hk ) ( Xen_le_Qctrl BS a k ( by
        exact Finset.mem_filter.mp hk |>.1 ) ) ) ) );
      exact min_le_left _ _;
    · refine Or.inr ⟨ coldLabel BS a BS.k0, ?_, ?_, ?_ ⟩;
      · intro p
        obtain ⟨k, hk0k, hkK, hpk⟩ : ∃ k, BS.k0 ≤ k ∧ k ≤ BS.K ∧ p.val ∈ BS.P k := by
          exact Exists.elim ( Finset.mem_biUnion.mp p.2 ) fun k hk => ⟨ k, by aesop ⟩;
        have hcold : coldLabel BS a k = coldLabel BS a BS.k0 := by
          convert coldLabel_eq_segStart BS c2 a k hk0k hkK _ using 1;
          · rw [ show segStart BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k = BS.k0 from ?_ ];
            rw [ show hotSet BS c2 a = ∅ from Finset.not_nonempty_iff_eq_empty.mp hH, show boundarySet BS c2 a = ∅ from Finset.not_nonempty_iff_eq_empty.mp hB ] ; exact segStart_empty BS k;
          · exact fun h => hH ⟨ k, h ⟩;
        have := hcf BS a k hk0k hkK ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show k ≥ N by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) ] ) ( by
                                                                                                          exact fun h => hH ⟨ k, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk0k, hkK ⟩, h ⟩ ⟩ );
        convert this.2.2 p.val ( Finset.mem_sdiff.mpr ⟨ hpk, ?_ ⟩ ) using 1;
        · unfold toPlain; aesop;
        · rw [ hcold ];
        · exact fun h => by have := hnoexc BS a k hk0k hkK ( by
            exact le_trans hN.le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) ) ) ( by
            exact fun h => hH ⟨ k, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk0k, hkK ⟩, h ⟩ ⟩ ) ; exact Finset.notMem_empty _ ( this ▸ h ) ;
      · contrapose! ha;
        refine' ⟨ coldLabel BS a BS.k0, ha, _ ⟩;
        intro p
        obtain ⟨k, hk0k, hkK, hpk⟩ : ∃ k, BS.k0 ≤ k ∧ k ≤ BS.K ∧ p.val ∈ BS.P k := by
          have := Finset.mem_biUnion.mp p.2; aesop;
        have hck : ¬ isHot BS c2 a k := by
          exact fun h => hH ⟨ k, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk0k, hkK ⟩, h ⟩ ⟩;
        have hck : toPlain BS a p = coldLabel BS a k := by
          apply (hcf BS a k hk0k hkK (by
          exact le_trans hN.le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) )) hck).right.right p (by
          simp [hnoexc BS a k hk0k hkK (by
          exact le_trans hN.le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) )) hck];
          exact hpk);
        have hck : coldLabel BS a k = coldLabel BS a BS.k0 := by
          convert coldLabel_eq_segStart BS c2 a k hk0k hkK _ using 1;
          · rw [ show segStart BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k = BS.k0 from ?_ ];
            rw [ show hotSet BS c2 a = ∅ from Finset.not_nonempty_iff_eq_empty.mp hH, show boundarySet BS c2 a = ∅ from Finset.not_nonempty_iff_eq_empty.mp hB ] ; exact segStart_empty BS k;
          · exact fun h => hH ⟨ k, h ⟩;
        unfold toPlain at *; aesop;
      · apply diagonal_Qctrl;
        · intro p
          obtain ⟨k, hk0k, hkK, hpk⟩ : ∃ k, BS.k0 ≤ k ∧ k ≤ BS.K ∧ p.val ∈ BS.P k := by
            exact Exists.elim ( Finset.mem_biUnion.mp p.2 ) fun k hk => ⟨ k, by aesop ⟩;
          have hck : ¬ isHot BS c2 a k := by
            exact fun h => hH ⟨ k, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hk0k, hkK ⟩, h ⟩ ⟩;
          have hck : coldLabel BS a k = coldLabel BS a BS.k0 := by
            convert coldLabel_eq_segStart BS c2 a k hk0k hkK _ using 1;
            · rw [ show segStart BS ( hotSet BS c2 a ) ( boundarySet BS c2 a ) k = BS.k0 from ?_ ];
              rw [ show hotSet BS c2 a = ∅ from Finset.not_nonempty_iff_eq_empty.mp hH, show boundarySet BS c2 a = ∅ from Finset.not_nonempty_iff_eq_empty.mp hB ] ; exact segStart_empty BS k;
            · exact fun h => hH ⟨ k, h ⟩;
          have := hcf BS a k hk0k hkK ( by
            exact le_trans hN.le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) ) ) ‹_›;
          convert this.2.2 p.val ( Finset.mem_sdiff.mpr ⟨ hpk, by
            exact fun h => by have := hnoexc BS a k hk0k hkK ( by
              exact le_trans ( le_of_lt hN ) ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) ) ) ‹_›; simp_all +decide [ Finset.ext_iff ] ; ⟩ ) using 1;
          · unfold toPlain; aesop;
          · rw [ hck ];
        · intro pq hpq
          have h_label_bound : |(coldLabel BS a BS.k0 : ℝ)| ≤ (2 : ℝ) ^ (2 * BS.k0) / 64 := by
            have h_label_bound : |(coldLabel BS a BS.k0 : ℝ)| ≤ ((BS.P BS.k0).card : ℝ) * (2 : ℝ) ^ BS.k0 / 64 := by
              apply (hcf BS a BS.k0 (by linarith) (by linarith [BS.hk]) (by
              exact le_trans hN.le ( pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Nat.le_max_right ( max 4 kRwPi ) N ] ) )) (by
              exact fun h => hH ⟨ BS.k0, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith [ BS.hk ] ⟩, h ⟩ ⟩)).right.left;
            refine le_trans h_label_bound ?_;
            rw [ pow_mul' ];
            rw [ sq ];
            rw [ mul_comm ] ; gcongr;
            exact_mod_cast GlobalControl.block_card_le BS BS.k0;
          have h_prod_bound : (2 : ℝ) ^ (2 * BS.k0) < (pq.1 : ℝ) * (pq.2 : ℝ) := by
            exact_mod_cast ctrlPairs_prod_lower BS ( by linarith [ le_max_left ( max 4 kRwPi ) N, le_max_right ( max 4 kRwPi ) N, le_max_left 4 kRwPi, le_max_right 4 kRwPi ] ) hpq;
          rw [ ← @Int.cast_lt ℝ ] ; push_cast ; linarith [ abs_nonneg ( coldLabel BS a BS.k0 : ℝ ) ]

end GlobalControl