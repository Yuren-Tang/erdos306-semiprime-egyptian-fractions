import RequestProject.GlobalControl

open Finset BigOperators Classical

noncomputable section

namespace GlobalControl

/-!
# G7 — global control partition (Prop 8.1), route closure (note 34 G7)

This module is downstream-only: it imports `GlobalControl` and assembles the
headline off-main-arc bound `global_control_partition` from

* the G5 level-set theorem `global_levelset` (factor `exp(A · numBlocks BS)`,
  `A` a *fixed* G5 constant — this is the corrected `Cglob` form: because `A` is
  fixed before `k0min` is chosen, the growing Peierls floor `F0(k0)` can absorb
  `A · numBlocks BS`);
* the G6 localization dichotomy (`g6_localization`, the one genuinely-hard
  remaining sorry: off-main ⟹ above the energy floor *or* globally diagonal with
  a large label and exact quadratic energy);
* the sector-I Laplace absorption (`sectorI_absorption`) and sector-II Gaussian
  tail (`sectorII_gaussian`).

The earlier free-`Cglob` route form was *unsound* (a `k0min` independent of an
arbitrary later `Cglob` cannot absorb it): here the level-set hypothesis carries
the explicit `exp(A · numBlocks BS)` factor, so the quantifier order is correct.
-/

/-! ## Generic finite-sum / subtype-tsum bridges -/

/-- For a `Fintype` index and a decidable predicate, the subtype `tsum` is the
filtered finite sum. -/
lemma fintype_subtype_tsum_eq {α : Type*} [Fintype α] (S : α → Prop)
    [DecidablePred S] (f : α → ℝ) :
    ∑' a : {x // S x}, f a.1 = ∑ a ∈ Finset.univ.filter S, f a := by
  classical
  rw [tsum_fintype]
  exact (Finset.sum_subtype (Finset.univ.filter S) (by intro x; simp) f).symm

/-- Subadditivity of subtype-tsums along a disjunctive cover, for a nonnegative
summand on a finite index. -/
lemma fintype_subtype_tsum_le_of_or {α : Type*} [Fintype α]
    (S P Q : α → Prop) [DecidablePred S] [DecidablePred P] [DecidablePred Q]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hor : ∀ a, S a → P a ∨ Q a) :
    ∑' a : {x // S x}, f a.1 ≤
      (∑' a : {x // P x}, f a.1) + ∑' a : {x // Q x}, f a.1 := by
  classical
  rw [fintype_subtype_tsum_eq S f, fintype_subtype_tsum_eq P f,
    fintype_subtype_tsum_eq Q f]
  have hsub : Finset.univ.filter S ⊆
      Finset.univ.filter P ∪ Finset.univ.filter Q := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rcases hor a ha.2 with hP | hQ
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha.1, hP⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha.1, hQ⟩)
  calc ∑ a ∈ Finset.univ.filter S, f a
      ≤ ∑ a ∈ Finset.univ.filter P ∪ Finset.univ.filter Q, f a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hf a)
    _ ≤ (∑ a ∈ Finset.univ.filter P, f a) + ∑ a ∈ Finset.univ.filter Q, f a := by
        have key : (∑ a ∈ Finset.univ.filter P ∪ Finset.univ.filter Q, f a) +
              ∑ a ∈ (Finset.univ.filter P) ∩ (Finset.univ.filter Q), f a =
            (∑ a ∈ Finset.univ.filter P, f a) + ∑ a ∈ Finset.univ.filter Q, f a :=
          Finset.sum_union_inter
        have hnn : 0 ≤ ∑ a ∈ (Finset.univ.filter P) ∩ (Finset.univ.filter Q), f a :=
          Finset.sum_nonneg (fun a _ => hf a)
        linarith

/-! ## G6 localization and the energy floor -/

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

/-- **G6 localization dichotomy** (note 34 G6 / note 38 §6).  An off-main-arc
assignment is either above the global energy floor, or lies in the diagonal
sector.

`sorry` reason: this is the genuinely-hard remaining G6 math — the main-arc
localization "no structure ⟹ global diagonal", built from the assembled
exception-floor monotonicity, global cold-segment collapse, and the
all-control-pair CRT identity.  It is the single bundled open step of G7. -/
theorem g6_localization :
    ∃ (k0loc : ℕ) (c2 e0 : ℝ), 0 < c2 ∧ 0 < e0 ∧
      ∀ (BS : BlockSystem), k0loc ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ a : GlobalAssignment BS, a ∉ mainArc BS C →
        globalControlFloor BS c2 e0 ≤ Qctrl BS a ∨ diagSector BS C a := by
  sorry

/-! ## Sector I — Laplace absorption above the energy floor -/

/-- Convert the explicit G5 route hypothesis (`Set.ncard` form) to the
`Finset.univ.filter` form required by `SBEEAssembly.partfun_series_bound`. -/
lemma global_levelset_finset_bound
    (Cglob eps : ℝ) (BS : BlockSystem)
    (hlevel : ∀ R : ℝ, 1 ≤ R →
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS)) :
    ∀ R : ℝ, 1 ≤ R →
      ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) ≤
        Cglob * Real.exp (8 * eps * R) * (1 + Real.sqrt R / sigmaCtrl BS) := by
  intro R hR
  classical
  have hcard :
      (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) =
        ((Finset.univ.filter (fun a : GlobalAssignment BS => Qctrl BS a ≤ R)).card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset_setOf]
  simpa [hcard] using hlevel R hR

/-- **Sector-I absorption.**  With the explicit `exp(A · numBlocks BS)`
level-set hypothesis, the Laplace sum restricted to assignments above the energy
floor is `≤ η / sigmaCtrl BS`, provided `k0` is large enough that the floor
beats `A · numBlocks BS`.

`sorry` reason: needs the floor growth lower bound
`globalControlFloor BS c2 e0 ≥ const · 2^k0 / k0³` (via `Rw_large` for the `Rw`
part and the density-driven growth of `Pifloor`), then the tail-shift Laplace
estimate `∑_{Q ≥ floor} e^{-cQ} ≤ e^{-(c/2)·floor}·∑_all e^{-(c/2)Q}`. -/
theorem sectorI_absorption (c : ℝ) (hc : 0 < c) (eps A c2 e0 : ℝ)
    (heps : 0 < eps) (hepsc : 8 * eps < c) (hA : 0 < A)
    (hc2 : 0 < c2) (he0 : 0 < e0) :
    ∀ η : ℝ, 0 < η →
    ∃ k0min : ℕ,
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      0 < sigmaCtrl BS →
      (∀ R : ℝ, 1 ≤ R →
        (Set.ncard {a : GlobalAssignment BS | Qctrl BS a ≤ R} : ℝ) ≤
          Real.exp (A * (numBlocks BS : ℝ)) * Real.exp (8 * eps * R) *
            (1 + Real.sqrt R / sigmaCtrl BS)) →
      ∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1) ≤ η / sigmaCtrl BS := by
  sorry

/-! ## Sector II — diagonal Gaussian tail -/

/-- **Sector-II Gaussian tail.**  The diagonal sector is bounded by a Gaussian
tail in the label window `|m| > C / σ`.  A diagonal assignment is determined by
its common label, so the sum injects into `∑_{|m| > C/σ} e^{-c m² σ²}`, which is
`≤ Ctail · e^{-C² c / 2} / σ`.

`sorry` reason: needs the label-injection (a diagonal `a` is determined by its
label mod every prime), the substitution `Qctrl = m² σ²`, and the elementary
Gaussian tail split using the verified `gaussian_int_sum_le` (requires
`c σ² / 2 ≤ 1`, ensured for `k0` large via `sigmaCtrl_le_geom`). -/
theorem sectorII_gaussian (c : ℝ) (hc : 0 < c) :
    ∃ (Ctail : ℝ) (k0II : ℕ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0II ≤ BS.k0 → 0 < sigmaCtrl BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∑' a : {a : GlobalAssignment BS // diagSector BS C a},
          Real.exp (-c * Qctrl BS a.1) ≤
        Ctail * Real.exp (-C ^ 2 * c / 2) / sigmaCtrl BS := by
  sorry

/-! ## sigmaCtrl positivity -/

private lemma two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
  calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
    _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk

/-- A block whose density bound applies is nonempty (the density lower bound is
strictly positive, so the cardinality is positive). -/
private lemma block_nonempty (BS : BlockSystem) {k : ℕ} (hk1 : BS.k0 ≤ k)
    (hk2 : k ≤ BS.K) : (BS.P k).Nonempty := by
  rw [← Finset.card_pos]
  have hk : 1 ≤ k := le_trans BS.hk0 hk1
  have hlog : 0 < Real.log ((2 : ℝ) ^ k) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) (two_le_two_pow hk))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k / (2 * Real.log ((2 : ℝ) ^ k)) := by positivity
  have hd := BS.hdensity k hk1 hk2
  have : (0 : ℝ) < ((BS.P k).card : ℝ) := lt_of_lt_of_le hpos hd
  exact_mod_cast this

/-- `sigmaCtrl BS > 0`: there is at least one (bipartite) control pair, whose
reciprocal-square weight is positive. -/
lemma sigmaCtrl_pos (BS : BlockSystem) (hadm : admissibleGlobalRange BS) :
    0 < sigmaCtrl BS := by
  have hk0 : 1 ≤ BS.k0 := BS.hk0
  have hKge : BS.k0 + 1 ≤ BS.K := le_trans (by omega) hadm.1
  obtain ⟨p, hp⟩ := block_nonempty BS le_rfl (by omega)
  obtain ⟨q, hq⟩ := block_nonempty BS (by omega) hKge
  have hpair : (p, q) ∈ ctrlPairs BS := by
    rw [ctrlPairs]
    refine Finset.mem_union_right _ ?_
    rw [Finset.mem_biUnion]
    refine ⟨BS.k0, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
    rw [bipartitePairs]
    exact Finset.mem_product.mpr ⟨hp, hq⟩
  rw [sigmaCtrl, Real.sqrt_pos]
  refine Finset.sum_pos' (fun pq _ => by positivity) ⟨(p, q), hpair, ?_⟩
  have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (BS.hprime BS.k0 p hp).pos
  have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (BS.hprime (BS.k0 + 1) q hq).pos
  positivity

/-! ## G7 assembly -/

/-- **G7 (global control partition, Prop 8.1).**  Off-main-arc Laplace sum,
bounded by an arbitrarily small `η / σ` plus the one-dimensional Gaussian tail.

This is the route-closed form of `GlobalControl.global_control_partition`,
assembled from `global_levelset` (G5) + `g6_localization` (G6) + the two sector
estimates.  The `Cglob` factor is the *fixed* `exp(A · numBlocks BS)`, so the
quantifier order is sound. -/
theorem global_control_partition_final (c : ℝ) (hc : 0 < c)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (η + Ctail * Real.exp (-C ^ 2 * c / 2)) / sigmaCtrl BS := by
  intro η hη
  classical
  -- Pick an internal level-set exponent eps0 ∈ (0,1) with 8·eps0 < c.
  set eps0 : ℝ := min (c / 16) (1 / 2) with heps0_def
  have heps0_pos : 0 < eps0 := lt_min (by positivity) (by norm_num)
  have heps0_lt1 : eps0 < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heps0_c : 8 * eps0 < c := by
    have : eps0 ≤ c / 16 := min_le_left _ _
    nlinarith
  -- G5 level-set theorem: a fixed constant A and a base scale k0minG5.
  obtain ⟨k0minG5, A, hA, hlevel⟩ := global_levelset eps0 heps0_pos heps0_lt1
  -- G6 localization dichotomy: fixed floor constants c2, e0.
  obtain ⟨k0loc, c2, e0, hc2, he0, hloc⟩ := g6_localization
  -- Sector I: η-absorption above the floor, depending on A, c2, e0.
  obtain ⟨k0minI, hI⟩ := sectorI_absorption c hc eps0 A c2 e0 heps0_pos heps0_c hA hc2 he0 η hη
  -- Sector II: the Gaussian tail constant.
  obtain ⟨Ctail, k0II, hCtail, hII⟩ := sectorII_gaussian c hc
  refine ⟨max k0minG5 (max k0loc (max k0minI k0II)), Ctail, hCtail, ?_⟩
  intro BS hk0 hadm C hC
  -- Unpack the scale thresholds.
  have hk0G5 : k0minG5 ≤ BS.k0 := le_trans (le_max_left _ _) hk0
  have hk0loc : k0loc ≤ BS.k0 := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk0
  have hk0I : k0minI ≤ BS.k0 :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hk0
  have hk0II : k0II ≤ BS.k0 :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hk0
  -- sigmaCtrl positivity (there is at least one control pair).
  have hσpos : 0 < sigmaCtrl BS := sigmaCtrl_pos BS hadm
  -- The explicit level-set bound for this BS.
  have hlevelBS := hlevel BS hk0G5 hadm
  -- Localization dichotomy for this BS, C.
  have hlocBS := hloc BS hk0loc hadm C hC
  -- Split the off-main-arc sum into the floor sector and the diagonal sector.
  have hsplit :
      ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1) ≤
        (∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
          Real.exp (-c * Qctrl BS a.1)) +
        ∑' a : {a : GlobalAssignment BS // diagSector BS C a},
          Real.exp (-c * Qctrl BS a.1) :=
    fintype_subtype_tsum_le_of_or
      (fun a => a ∉ mainArc BS C)
      (fun a => globalControlFloor BS c2 e0 ≤ Qctrl BS a)
      (fun a => diagSector BS C a)
      (fun a => Real.exp (-c * Qctrl BS a))
      (fun a => (Real.exp_pos _).le)
      (fun a ha => hlocBS a ha)
  -- Bound each sector.
  have hsI := hI BS hk0I hadm hσpos hlevelBS
  have hsII := hII BS hk0II hσpos C hC
  calc ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-c * Qctrl BS a.1)
      ≤ (∑' a : {a : GlobalAssignment BS // globalControlFloor BS c2 e0 ≤ Qctrl BS a},
            Real.exp (-c * Qctrl BS a.1)) +
        ∑' a : {a : GlobalAssignment BS // diagSector BS C a},
            Real.exp (-c * Qctrl BS a.1) := hsplit
    _ ≤ η / sigmaCtrl BS + Ctail * Real.exp (-C ^ 2 * c / 2) / sigmaCtrl BS :=
        add_le_add hsI hsII
    _ = (η + Ctail * Real.exp (-C ^ 2 * c / 2)) / sigmaCtrl BS := by ring

end GlobalControl

end
