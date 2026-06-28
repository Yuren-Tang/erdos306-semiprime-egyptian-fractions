import RequestProject.ArcConstructionExtra

open Finset BigOperators Classical Real

noncomputable section

namespace CircleMethod

open GlobalControl

/-!
# Extra-energy minor arc interface (note 46)

`minor_arc_bound_mult` uses a raw fiber cardinality `M`.  When mass/gadget edges
introduce primes outside `blockSupport BS`, the right object is the **extra-edge
energy** `Qextra` retained inside each fiber, with a fiber-tail bound
`∑_{fiber} exp(-c·Qextra) ≤ K` replacing the cardinality bound.  This file proves the
fiber-tail analogues of `minor_energy_sum_le_mult` / `minor_arc_bound_mult`.
-/

set_option maxHeartbeats 4000000 in
/-- **Fiber-tail minor energy reindex.**  If `QE ≥ Qctrl + Qextra` and the
extra-energy fiber tails are bounded by `K`, the energy sum is `≤ K` times the
off-main-arc control sum. -/
lemma minor_energy_sum_le_fiber_tail
    (BS : BlockSystem) (E : Finset ℕ) (c C K : ℝ) (Sm : Finset ℕ)
    (Qextra : ℕ → ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hQE : ∀ h ∈ Sm,
      Qctrl BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE E h)
    (hnotmain : ∀ h ∈ Sm,
      (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C)
    (hfiber : ∀ a : GlobalAssignment BS,
      ∑ h ∈ Sm.filter
        (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) = a),
        Real.exp (-c * Qextra h) ≤ K) :
    ∑ h ∈ Sm, Real.exp (-c * QE E h) ≤
      K * ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
        Real.exp (-c * Qctrl BS a.1) := by
  classical
  set af : ℕ → GlobalAssignment BS := fun h => (fun p => ((h : ZMod p.1))) with haf
  rw [fintype_subtype_tsum_eq (fun a => a ∉ mainArc BS C)
    (fun a => Real.exp (-c * Qctrl BS a))]
  have step1 : ∑ h ∈ Sm, Real.exp (-c * QE E h)
      ≤ ∑ h ∈ Sm, Real.exp (-c * Qctrl BS (af h)) * Real.exp (-c * Qextra h) := by
    refine Finset.sum_le_sum (fun h hh => ?_)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hQE h hh) hc]
  refine le_trans step1 ?_
  have hmaps : ∀ h ∈ Sm, af h ∈ Sm.image af := fun h hh => Finset.mem_image_of_mem af hh
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun h => Real.exp (-c * Qctrl BS (af h)) * Real.exp (-c * Qextra h))]
  calc ∑ j ∈ Sm.image af, ∑ h ∈ Sm.filter (fun h => af h = j),
          Real.exp (-c * Qctrl BS (af h)) * Real.exp (-c * Qextra h)
      ≤ ∑ j ∈ Sm.image af, K * Real.exp (-c * Qctrl BS j) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        have hfib : ∀ h ∈ Sm.filter (fun h => af h = j),
            Real.exp (-c * Qctrl BS (af h)) * Real.exp (-c * Qextra h)
              = Real.exp (-c * Qctrl BS j) * Real.exp (-c * Qextra h) :=
          fun h hh => by rw [(Finset.mem_filter.mp hh).2]
        rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum, mul_comm]
        exact mul_le_mul_of_nonneg_right (hfiber j) (Real.exp_nonneg _)
    _ = K * ∑ j ∈ Sm.image af, Real.exp (-c * Qctrl BS j) := by rw [Finset.mul_sum]
    _ ≤ K * ∑ j ∈ Finset.univ.filter (fun a => a ∉ mainArc BS C),
          Real.exp (-c * Qctrl BS j) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => Real.exp_nonneg _)
        intro a ha
        rw [Finset.mem_image] at ha
        obtain ⟨h, hh, rfl⟩ := ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotmain h hh⟩

set_option maxHeartbeats 4000000 in
/-- **Fiber-tail minor-arc bound.**  The Fourier wrapper of
`minor_energy_sum_le_fiber_tail`. -/
theorem minor_arc_bound_fiber_tail (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (Sm : Finset ℕ) (K : ℝ) (Qextra : ℕ → ℝ),
      0 ≤ K →
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ theta e) → (∀ e ∈ E, theta e ≤ 2 / 3) →
      (∀ e ∈ E, e ∣ L) → (∀ e ∈ E, 0 < e) → 0 < L →
      (∀ h ∈ Sm, Qctrl BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE E h) →
      (∀ h ∈ Sm, (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C) →
      (∀ a : GlobalAssignment BS,
        ∑ h ∈ Sm.filter
          (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) = a),
          Real.exp (-(16 / 9 : ℝ) * Qextra h) ≤ K) →
      ‖∑ h ∈ Sm,
          (∏ e ∈ E, ((theta e : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
              + (1 - theta e)))
          * Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖
        ≤ K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS := by
  intro η hη
  obtain ⟨k0min, Ctail, hCtail, hgcp⟩ :=
    global_control_partition (16 / 9) (by norm_num) eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro BS hk0 hadm C hC E theta b L Sm K Qextra hK hlb hub heL he0 hL hQE hnotmain hfiber
  have hconst : (8 * (1 / 3 : ℝ) * (1 - 1 / 3)) = 16 / 9 := by norm_num
  calc ‖∑ h ∈ Sm,
          (∏ e ∈ E, ((theta e : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
              + (1 - theta e)))
          * Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖
      ≤ ∑ h ∈ Sm, Real.exp (-(8 * (1 / 3 : ℝ) * (1 - 1 / 3)) * QE E h) :=
        minor_arc_norm_le (1 / 3) (by norm_num) (by norm_num) E theta b L
          hlb (by intro e he; have := hub e he; linarith) heL he0 hL Sm
    _ = ∑ h ∈ Sm, Real.exp (-(16 / 9 : ℝ) * QE E h) := by rw [hconst]
    _ ≤ K * ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-(16 / 9 : ℝ) * Qctrl BS a.1) :=
        minor_energy_sum_le_fiber_tail BS E (16 / 9) C K Sm Qextra (by norm_num) hK
          hQE hnotmain hfiber
    _ ≤ K * ((η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS) :=
        mul_le_mul_of_nonneg_left (hgcp BS hk0 hadm C hC) hK
    _ = K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS := by ring

end CircleMethod

end
