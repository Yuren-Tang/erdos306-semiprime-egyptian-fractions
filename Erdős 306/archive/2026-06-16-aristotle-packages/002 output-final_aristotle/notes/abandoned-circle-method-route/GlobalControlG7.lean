import RequestProject.GlobalControl
import RequestProject.GlobalControlG6
import RequestProject.GlobalControlSectorI
import RequestProject.GlobalControlG5Assembly

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


/-! ## Sector II — diagonal Gaussian tail -/

/-- Summability of the one-dimensional integer Gaussian (comparison to the
geometric series `(e^{-A})^n` via `n² ≥ n`). -/
private lemma summable_int_gaussian (A : ℝ) (hA : 0 < A) :
    Summable (fun m : ℤ => Real.exp (-A * (m : ℝ) ^ 2)) := by
  have hg : Summable (fun n : ℕ => Real.exp (-A) ^ n) :=
    summable_geometric_of_lt_one (by positivity)
      (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hA))
  have key : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) ^ 2 := fun n => by
    exact_mod_cast Nat.le_self_pow (by norm_num) n
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩ <;>
  · refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    nlinarith [key n, mul_le_mul_of_nonneg_left (key n) hA.le]

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
  classical
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 * Real.sqrt c) (by norm_num : (1 : ℝ) < 2)
  refine ⟨1 + 6 * Real.sqrt 2 / Real.sqrt c, max 2 n, by positivity, ?_⟩
  intro BS hk0II hσ0 C hC
  set σ := sigmaCtrl BS with hσ_def
  have hk0_2 : 2 ≤ BS.k0 := le_trans (le_max_left _ _) hk0II
  have hk0_n : n ≤ BS.k0 := le_trans (le_max_right _ _) hk0II
  have hσ1 : σ ≤ 1 := sigmaCtrl_le_one BS hk0_2
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  -- σ < 1/√c via the geometric bound and 2^k0 > 4√c.
  have hσ_small : σ < 1 / Real.sqrt c := by
    have hgeom : σ ≤ 4 / 2 ^ BS.k0 := sigmaCtrl_le_geom BS hk0_2
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ BS.k0 := pow_le_pow_right₀ (by norm_num) hk0_n
    have hbig : 4 * Real.sqrt c < (2 : ℝ) ^ BS.k0 := lt_of_lt_of_le hn hpow
    have hstep : (4 : ℝ) / 2 ^ BS.k0 < 4 / (4 * Real.sqrt c) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hbig, hsc]
    have hcollapse : (4 : ℝ) / (4 * Real.sqrt c) = 1 / Real.sqrt c := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    calc σ ≤ 4 / 2 ^ BS.k0 := hgeom
      _ < 4 / (4 * Real.sqrt c) := hstep
      _ = 1 / Real.sqrt c := hcollapse
  -- σ² < 1/c, hence A := c σ²/2 ∈ (0,1].
  have hσsq : σ ^ 2 < 1 / c := by
    have hsc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
    have hpos_inv : (0 : ℝ) < 1 / Real.sqrt c := by positivity
    have hlt : σ ^ 2 < (1 / Real.sqrt c) ^ 2 :=
      sq_lt_sq' (by linarith [hσ0, hpos_inv]) hσ_small
    rwa [div_pow, one_pow, hsc2] at hlt
  have hApos : 0 < c * σ ^ 2 / 2 := by positivity
  have hcσ : c * σ ^ 2 < 1 := by
    have h := mul_lt_mul_of_pos_left hσsq hc
    rwa [mul_one_div, div_self hc.ne'] at h
  have hAle1 : c * σ ^ 2 / 2 ≤ 1 := by linarith [hcσ]
  -- Convert the diagonal-sector tsum to a finite filter sum.
  rw [fintype_subtype_tsum_eq (fun a => diagSector BS C a)
    (fun a => Real.exp (-c * Qctrl BS a))]
  set F := Finset.univ.filter (fun a : GlobalAssignment BS => diagSector BS C a) with hF_def
  -- Label map: pick the diagonal witness for each diagonal assignment.
  set lab : GlobalAssignment BS → ℤ :=
    fun a => if h : diagSector BS C a then h.choose else 0 with hlab_def
  have labspec : ∀ a, diagSector BS C a →
      (∀ p : {p : ℕ // p ∈ blockSupport BS}, (a p : ZMod p.1) = (lab a : ZMod p.1)) ∧
      C / σ < |(lab a : ℝ)| ∧ Qctrl BS a = (lab a : ℝ) ^ 2 * σ ^ 2 := by
    intro a ha
    have hch : lab a = ha.choose := by rw [hlab_def]; exact dif_pos ha
    rw [hch]; exact ha.choose_spec
  -- Injectivity of `lab` on `F` (a diagonal assignment is recovered from its label).
  have hinj : ∀ a ∈ F, ∀ b ∈ F, lab a = lab b → a = b := by
    intro a haF b hbF hab
    have ha := (Finset.mem_filter.mp haF).2
    have hb := (Finset.mem_filter.mp hbF).2
    funext p
    have h1 := (labspec a ha).1 p
    have h2 := (labspec b hb).1 p
    rw [h1, h2, hab]
  -- The main chain.
  calc ∑ a ∈ F, Real.exp (-c * Qctrl BS a)
      = ∑ a ∈ F, Real.exp (-c * ((lab a : ℝ) ^ 2 * σ ^ 2)) := by
        refine Finset.sum_congr rfl (fun a haF => ?_)
        rw [(labspec a (Finset.mem_filter.mp haF).2).2.2]
    _ ≤ ∑ a ∈ F, Real.exp (-C ^ 2 * c / 2) * Real.exp (-(c * σ ^ 2 / 2) * (lab a : ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun a haF => ?_)
        have ha := (Finset.mem_filter.mp haF).2
        have hwin := (labspec a ha).2.1
        have hCσ : C < σ * |(lab a : ℝ)| := by
          rw [div_lt_iff₀ hσ0] at hwin; nlinarith [hwin]
        have hsm : C ^ 2 ≤ σ ^ 2 * (lab a : ℝ) ^ 2 := by
          have h1 : C ^ 2 ≤ (σ * |(lab a : ℝ)|) ^ 2 := by nlinarith [hCσ, hC0]
          calc C ^ 2 ≤ (σ * |(lab a : ℝ)|) ^ 2 := h1
            _ = σ ^ 2 * (lab a : ℝ) ^ 2 := by rw [mul_pow, sq_abs]
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hsm, hc, sq_nonneg (lab a : ℝ), hσ0]
    _ = Real.exp (-C ^ 2 * c / 2) *
          ∑ a ∈ F, Real.exp (-(c * σ ^ 2 / 2) * (lab a : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ = Real.exp (-C ^ 2 * c / 2) *
          ∑ m ∈ F.image lab, Real.exp (-(c * σ ^ 2 / 2) * (m : ℝ) ^ 2) := by
        rw [Finset.sum_image hinj]
    _ ≤ Real.exp (-C ^ 2 * c / 2) *
          ∑' m : ℤ, Real.exp (-(c * σ ^ 2 / 2) * (m : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact (summable_int_gaussian _ hApos).sum_le_tsum _
          (fun i _ => (Real.exp_pos _).le)
    _ ≤ Real.exp (-C ^ 2 * c / 2) * (1 + 6 / Real.sqrt (c * σ ^ 2 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact gaussian_int_sum_le _ hApos hAle1
    _ ≤ (1 + 6 * Real.sqrt 2 / Real.sqrt c) * Real.exp (-C ^ 2 * c / 2) / σ := by
        have hfin : 1 + 6 / Real.sqrt (c * σ ^ 2 / 2) ≤
            (1 + 6 * Real.sqrt 2 / Real.sqrt c) / σ := by
          have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
          have hkey : Real.sqrt 2 * Real.sqrt (c * σ ^ 2 / 2) = Real.sqrt c * σ := by
            rw [← Real.sqrt_mul (by norm_num),
              show (2 : ℝ) * (c * σ ^ 2 / 2) = c * σ ^ 2 by ring,
              Real.sqrt_mul hc.le, Real.sqrt_sq hσ0.le]
          have heq : 6 / Real.sqrt (c * σ ^ 2 / 2)
              = 6 * Real.sqrt 2 / (Real.sqrt c * σ) := by rw [← hkey]; field_simp
          rw [heq]
          have hsplit : (1 + 6 * Real.sqrt 2 / Real.sqrt c) / σ
              = 1 / σ + 6 * Real.sqrt 2 / (Real.sqrt c * σ) := by field_simp
          rw [hsplit]
          have h1 : (1 : ℝ) ≤ 1 / σ := by rw [le_div_iff₀ hσ0]; linarith
          linarith
        have hexp : 0 < Real.exp (-C ^ 2 * c / 2) := Real.exp_pos _
        calc Real.exp (-C ^ 2 * c / 2) * (1 + 6 / Real.sqrt (c * σ ^ 2 / 2))
            ≤ Real.exp (-C ^ 2 * c / 2) * ((1 + 6 * Real.sqrt 2 / Real.sqrt c) / σ) :=
              mul_le_mul_of_nonneg_left hfin hexp.le
          _ = (1 + 6 * Real.sqrt 2 / Real.sqrt c) * Real.exp (-C ^ 2 * c / 2) / σ := by ring

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
  obtain ⟨k0minG5, A, hA, hlevel⟩ := global_levelset_final eps0 heps0_pos heps0_lt1
  -- G6 localization dichotomy: fixed floor constants c2, e0.
  obtain ⟨k0loc, c2, e0, hc2, he0, hloc⟩ := g6_localization
  -- Sector I: η-absorption above the floor, depending on A, c2, e0.
  obtain ⟨k0minI, hI⟩ := sectorI_absorption' c hc eps0 A c2 e0 heps0_pos heps0_c hA hc2 he0 η hη
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
