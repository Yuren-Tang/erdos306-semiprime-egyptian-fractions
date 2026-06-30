import RequestProject.CircleMethodArcs
import RequestProject.CircleMethodMainTerm
import RequestProject.BlockSystemConstruction
import RequestProject.Core.Semiprime

open Finset BigOperators GlobalControl

noncomputable section

namespace CircleMethod

/-!
# R2: edge construction foundation

Control edges `ctrlEdges BS = {p·q : (p,q) ∈ ctrlPairs BS}` (squarefree semiprimes),
and the key minor-arc input `QE_ge_Qctrl`: any edge set containing the control edges
has `QE E h ≥ Qctrl BS (a(h))` (the `hQE` hypothesis of `minor_arc_bound`), via the
verified `Qctrl_freq_eq`.
-/

/-- The control edges: products `p·q` of the control pairs. -/
def ctrlEdges (BS : BlockSystem) : Finset ℕ :=
  (ctrlPairs BS).image (fun pq => pq.1 * pq.2)

/-- Control pairs are strictly ordered (`pq.1 < pq.2`). -/
lemma ctrlPairs_lt (BS : BlockSystem) {pq : ℕ × ℕ} (hpq : pq ∈ ctrlPairs BS) :
    pq.1 < pq.2 := by
  simp only [ctrlPairs, Finset.mem_union, Finset.mem_biUnion, internalPairs,
    bipartitePairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Ico] at hpq
  rcases hpq with ⟨k, _, ⟨_, _⟩, hlt⟩ | ⟨k, _, hp1, hp2⟩
  · exact hlt
  · exact lt_of_lt_of_le (BS.hwindow k pq.1 hp1).2 (BS.hwindow (k + 1) pq.2 hp2).1

/-- Each control edge is a squarefree semiprime. -/
lemma ctrlEdges_semiprime (BS : BlockSystem) {e : ℕ} (he : e ∈ ctrlEdges BS) :
    IsSemiprime e := by
  rw [ctrlEdges, Finset.mem_image] at he
  obtain ⟨pq, hpq, rfl⟩ := he
  obtain ⟨hp1, hp2, _⟩ := ctrlPairs_distinct_primes BS hpq
  exact ⟨pq.1, pq.2, hp1, hp2, ctrlPairs_lt BS hpq, rfl⟩

/-- The product map `(p,q) ↦ p·q` is injective on control pairs (unique factorization
of a semiprime into its two ordered prime factors). -/
lemma ctrlPairs_prod_injOn (BS : BlockSystem) :
    Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) (ctrlPairs BS) := by
  intro a ha b hb hab
  simp only at hab
  obtain ⟨ha1, ha2, _⟩ := ctrlPairs_distinct_primes BS ha
  obtain ⟨hb1, hb2, _⟩ := ctrlPairs_distinct_primes BS hb
  have halt := ctrlPairs_lt BS ha
  have hblt := ctrlPairs_lt BS hb
  -- a.1 ∣ b.1 * b.2, a.1 prime ⇒ a.1 = b.1 or a.1 = b.2
  have hdvd : a.1 ∣ b.1 * b.2 := ⟨a.2, by rw [← hab]⟩
  have h1 : a.1 = b.1 := by
    rcases (Nat.Prime.dvd_mul ha1).mp hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq ha1 hb1).mp h
    · -- a.1 = b.2 forces contradiction with orderings
      have heq : a.1 = b.2 := (Nat.prime_dvd_prime_iff_eq ha1 hb2).mp h
      have hb2pos : 0 < b.2 := hb2.pos
      have ha2eq : a.2 = b.1 := by
        have h2 : b.2 * a.2 = b.2 * b.1 := by
          calc b.2 * a.2 = a.1 * a.2 := by rw [heq]
            _ = b.1 * b.2 := hab
            _ = b.2 * b.1 := by ring
        exact Nat.eq_of_mul_eq_mul_left hb2pos h2
      omega
  have h2 : a.2 = b.2 := by
    have ha1pos : 0 < a.1 := ha1.pos
    rw [h1] at hab
    exact Nat.eq_of_mul_eq_mul_left (h1 ▸ ha1pos) hab
  exact Prod.ext h1 h2

/-- **`hQE` (the minor-arc energy input).**  If `E` contains all control edges, then
the CRT energy `Qctrl BS (a(h))` is dominated by `QE E h` — exactly the hypothesis
`minor_arc_bound` needs.  Proved from the verified `Qctrl_freq_eq`. -/
lemma QE_ge_Qctrl (BS : BlockSystem) (E : Finset ℕ) (hsub : ctrlEdges BS ⊆ E) (h : ℕ) :
    Qctrl BS (fun p => ((h : ZMod p.1))) ≤ QE E h := by
  rw [Qctrl_freq_eq]
  calc ∑ pq ∈ ctrlPairs BS,
          ((norm ∘ ((↑) : ℝ → UnitAddCircle)) ((h : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))) ^ 2
      = ∑ e ∈ ctrlEdges BS, ((norm ∘ ((↑) : ℝ → UnitAddCircle)) ((h : ℝ) / (e : ℝ))) ^ 2 := by
        rw [ctrlEdges, Finset.sum_image
          (fun a ha b hb hab => ctrlPairs_prod_injOn BS ha hb hab)]
        refine Finset.sum_congr rfl (fun pq _ => ?_)
        norm_num [Nat.cast_mul]
    _ ≤ QE E h := by
        unfold QE
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => by positivity)

set_option maxHeartbeats 4000000 in
/-- **Bounded-multiplicity minor energy reindex.**  Generalizes
`minor_energy_sum_le`: if the frequency-to-assignment map `h ↦ (h mod p)_p` is at
most `M`-to-1 on `Sm` (instead of injective), the energy sum is bounded by `M` times
the off-main-arc control sum.  This is needed because the construction's period
`L = ∏ P_E` makes the map over `blockSupport` exactly `b`-to-1 (the `b`-primes and
gadget primes are not in the blocks). -/
lemma minor_energy_sum_le_mult (BS : BlockSystem) (E : Finset ℕ) (c C : ℝ) (Sm : Finset ℕ)
    (M : ℕ) (hc : 0 ≤ c)
    (hQE : ∀ h ∈ Sm, Qctrl BS (fun p => ((h : ZMod p.1))) ≤ QE E h)
    (hnotmain : ∀ h ∈ Sm,
      (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C)
    (hmult : ∀ a : GlobalAssignment BS,
      ((Sm.filter (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) = a)).card : ℝ)
        ≤ (M : ℝ)) :
    ∑ h ∈ Sm, Real.exp (-c * QE E h) ≤
      (M : ℝ) * ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
        Real.exp (-c * Qctrl BS a.1) := by
  classical
  set af : ℕ → GlobalAssignment BS := fun h => (fun p => ((h : ZMod p.1))) with haf
  rw [fintype_subtype_tsum_eq (fun a => a ∉ mainArc BS C)
    (fun a => Real.exp (-c * Qctrl BS a))]
  have step1 : ∑ h ∈ Sm, Real.exp (-c * QE E h)
      ≤ ∑ h ∈ Sm, Real.exp (-c * Qctrl BS (af h)) :=
    Finset.sum_le_sum (fun h hh => Real.exp_le_exp.mpr (by nlinarith [hQE h hh, hc]))
  refine le_trans step1 ?_
  have hmaps : ∀ h ∈ Sm, af h ∈ Sm.image af := fun h hh => Finset.mem_image_of_mem af hh
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps (fun a => Real.exp (-c * Qctrl BS a))]
  calc ∑ j ∈ Sm.image af, ∑ _h ∈ Sm.filter (fun h => af h = j),
          Real.exp (-c * Qctrl BS j)
      ≤ ∑ j ∈ Sm.image af, (M : ℝ) * Real.exp (-c * Qctrl BS j) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hmult j) (Real.exp_nonneg _)
    _ = (M : ℝ) * ∑ j ∈ Sm.image af, Real.exp (-c * Qctrl BS j) := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * ∑ j ∈ Finset.univ.filter (fun a => a ∉ mainArc BS C),
          Real.exp (-c * Qctrl BS j) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => Real.exp_nonneg _)
        intro a ha
        rw [Finset.mem_image] at ha
        obtain ⟨h, hh, rfl⟩ := ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotmain h hh⟩

set_option maxHeartbeats 4000000 in
/-- **Bounded-multiplicity minor-arc bound.**  Like `minor_arc_bound`, but the
frequency map need only be `≤ M`-to-1 (hypothesis `hmult`); the bound then carries a
factor `M`.  This is the version the block-aligned construction can satisfy. -/
theorem minor_arc_bound_mult (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (Sm : Finset ℕ) (M : ℕ),
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ theta e) → (∀ e ∈ E, theta e ≤ 2 / 3) →
      (∀ e ∈ E, e ∣ L) → (∀ e ∈ E, 0 < e) → 0 < L →
      (∀ h ∈ Sm, Qctrl BS (fun p => ((h : ZMod p.1))) ≤ QE E h) →
      (∀ h ∈ Sm, (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C) →
      (∀ a : GlobalAssignment BS,
        ((Sm.filter (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) = a)).card : ℝ)
          ≤ (M : ℝ)) →
      ‖∑ h ∈ Sm,
          (∏ e ∈ E, ((theta e : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
              + (1 - theta e)))
          * Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖
        ≤ (M : ℝ) * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS := by
  intro η hη
  obtain ⟨k0min, Ctail, hCtail, hgcp⟩ :=
    global_control_partition (16 / 9) (by norm_num) eps heps η hη
  refine ⟨k0min, Ctail, hCtail, ?_⟩
  intro BS hk0 hadm C hC E theta b L Sm M hlb hub heL he0 hL hQE hnotmain hmult
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
    _ ≤ (M : ℝ) * ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
          Real.exp (-(16 / 9 : ℝ) * Qctrl BS a.1) :=
        minor_energy_sum_le_mult BS E (16 / 9) C Sm M (by norm_num) hQE hnotmain hmult
    _ ≤ (M : ℝ) * ((η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS) :=
        mul_le_mul_of_nonneg_left (hgcp BS hk0 hadm C hC) (by positivity)
    _ = (M : ℝ) * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS := by
        ring

/-! ## Periodicity for the main-arc term identity (`hterm` core) -/

/-- The Bernoulli factor is `1`-periodic: shifting the frequency by an integer
leaves it unchanged. -/
lemma bernoulliCharFun_int_add (θ t : ℝ) (n : ℤ) :
    bernoulliCharFun θ (t + (n : ℝ)) = bernoulliCharFun θ t := by
  unfold bernoulliCharFun
  congr 2
  rw [Complex.ofReal_add, Complex.ofReal_intCast,
    show (2 * (Real.pi : ℂ) * ((t : ℂ) + (n : ℂ)) * Complex.I)
        = 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      from by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- If `e ∣ (h − m)` then the Bernoulli factor at `h/e` equals that at `m/e`
(`1`-periodicity, since `(h−m)/e ∈ ℤ`). -/
lemma bernoulliCharFun_cong (θ : ℝ) (h : ℕ) (m : ℤ) (e : ℕ) (he : 0 < e)
    (hdvd : (e : ℤ) ∣ ((h : ℤ) - m)) :
    bernoulliCharFun θ ((h : ℝ) / (e : ℝ)) = bernoulliCharFun θ ((m : ℝ) / (e : ℝ)) := by
  obtain ⟨k, hk⟩ := hdvd
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hsplit : (h : ℝ) / (e : ℝ) = (m : ℝ) / (e : ℝ) + (k : ℝ) := by
    have : (h : ℝ) - (m : ℝ) = (e : ℝ) * (k : ℝ) := by exact_mod_cast hk
    field_simp
    linarith [this]
  rw [hsplit, bernoulliCharFun_int_add]

/-- **`hterm` core (CRT main-arc term identity).**  If the frequency `h` is congruent
to the integer label `m` modulo every edge value and modulo `b`, then the Fourier term
at `h` equals the diagonal label term at `m`.  (The construction's main arc consists
of exactly such diagonal frequencies.) -/
lemma fourierTerm_eq_term_label_of_cong
    (E : Finset ℕ) (θ : ℕ → ℝ) (b L : ℕ) (h : ℕ) (m : ℤ)
    (hb : 0 < b) (hbL : b ∣ L) (hL : 0 < L)
    (he0 : ∀ e ∈ E, 0 < e) (heL : ∀ e ∈ E, e ∣ L)
    (hcong : ∀ e ∈ E, (e : ℤ) ∣ ((h : ℤ) - m)) (hcongb : (b : ℤ) ∣ ((h : ℤ) - m)) :
    fourierTerm E θ b L h = term_label E θ b m := by
  unfold fourierTerm term_label
  congr 1
  · refine Finset.prod_congr rfl (fun e he => ?_)
    rw [charfactor_eq (θ e) h e L (he0 e he) (heL e he) hL]
    exact bernoulliCharFun_cong (θ e) h m e (he0 e he) (hcong e he)
  · -- phase equality (b-periodicity): both equal exp(-2πi h/b) = exp(-2πi m/b)
    obtain ⟨kk, hkk⟩ := hcongb  -- (h:ℤ) - m = b * kk
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hLb : ((L / b : ℕ) : ℂ) = (L : ℂ) / (b : ℂ) := by
      rw [Nat.cast_div hbL hbC]
    have hc : (h : ℂ) - (m : ℂ) = (b : ℂ) * (kk : ℂ) := by exact_mod_cast hkk
    have hm_eq : (m : ℂ) = (h : ℂ) - (b : ℂ) * (kk : ℂ) := by linear_combination -hc
    have hphase : -(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ))
        = 2 * Real.pi * (-((m : ℝ) / (b : ℝ))) * Complex.I
          + ((-kk : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hLb]
      push_cast
      rw [hm_eq]
      field_simp
      ring
    rw [hphase, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **`hterm` from a single mod-`L` congruence.**  Since every edge value and `b`
divide the period `L`, it suffices that `h ≡ m (mod L)`: then `fourierTerm` at `h`
equals the label term at `m`.  (The main-arc frequencies are `h ≡ m (mod L)`.) -/
lemma fourierTerm_eq_term_label_of_modL
    (E : Finset ℕ) (θ : ℕ → ℝ) (b L : ℕ) (h : ℕ) (m : ℤ)
    (hb : 0 < b) (hbL : b ∣ L) (hL : 0 < L)
    (he0 : ∀ e ∈ E, 0 < e) (heL : ∀ e ∈ E, e ∣ L)
    (hmodL : (L : ℤ) ∣ ((h : ℤ) - m)) :
    fourierTerm E θ b L h = term_label E θ b m :=
  fourierTerm_eq_term_label_of_cong E θ b L h m hb hbL hL he0 heL
    (fun e he => dvd_trans (Int.natCast_dvd_natCast.mpr (heL e he)) hmodL)
    (dvd_trans (Int.natCast_dvd_natCast.mpr hbL) hmodL)

/-- **Main-arc frequency/label bijection.**  For a period `L ≥ 2N+1`, the labels
`[-N, N]` correspond bijectively to frequencies `(m mod L) ∈ range L`, with each
frequency `h` congruent to its label `lbl h` modulo `L` (so `hterm` applies). -/
lemma exists_mainArc_bijection (L : ℕ) (N : ℤ) (hN : 0 ≤ N) (hNL : 2 * N + 1 ≤ (L : ℤ)) :
    ∃ (SM : Finset ℕ) (lbl : ℕ → ℤ),
      SM ⊆ Finset.range L ∧
      (∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N) ∧
      (∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂) ∧
      (∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m) ∧
      (∀ h ∈ SM, (L : ℤ) ∣ ((h : ℤ) - lbl h)) := by
  classical
  have hLZ : (0 : ℤ) < (L : ℤ) := by linarith
  have key : ∀ m : ℤ, -N ≤ m → m ≤ N →
      (m % (L : ℤ)).toNat < L ∧
      (if 2 * ((m % (L : ℤ)).toNat : ℤ) < (L : ℤ) then ((m % (L : ℤ)).toNat : ℤ)
        else ((m % (L : ℤ)).toNat : ℤ) - (L : ℤ)) = m ∧
      (L : ℤ) ∣ (((m % (L : ℤ)).toNat : ℤ) - m) := by
    intro m hm1 hm2
    have he1 : 0 ≤ m % (L : ℤ) := Int.emod_nonneg m hLZ.ne'
    have he2 : m % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos m hLZ
    have hfZ : ((m % (L : ℤ)).toNat : ℤ) = m % (L : ℤ) := Int.toNat_of_nonneg he1
    refine ⟨?_, ?_, ?_⟩
    · have : ((m % (L : ℤ)).toNat : ℤ) < (L : ℤ) := by rw [hfZ]; exact he2
      exact_mod_cast this
    · rw [hfZ]
      by_cases hm0 : 0 ≤ m
      · have hmm : m % (L : ℤ) = m := Int.emod_eq_of_lt hm0 (by linarith)
        rw [hmm, if_pos (by linarith)]
      · have hm0' : m < 0 := not_le.mp hm0
        have hmm : m % (L : ℤ) = m + (L : ℤ) := by
          rw [← Int.add_emod_right m (L : ℤ), Int.emod_eq_of_lt (by linarith) (by linarith)]
        rw [hmm, if_neg (by linarith)]; ring
    · rw [hfZ]
      exact ⟨-(m / (L : ℤ)), by linear_combination Int.ediv_add_emod m (L : ℤ)⟩
  refine ⟨(Finset.Icc (-N) N).image (fun m => (m % (L : ℤ)).toNat),
    fun h => if 2 * (h : ℤ) < (L : ℤ) then (h : ℤ) else (h : ℤ) - (L : ℤ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rw [Finset.mem_image] at hh
    obtain ⟨m, hm, rfl⟩ := hh
    rw [Finset.mem_Icc] at hm
    exact Finset.mem_range.mpr (key m hm.1 hm.2).1
  · intro h hh
    rw [Finset.mem_image] at hh
    obtain ⟨m, hm, rfl⟩ := hh
    rw [Finset.mem_Icc] at hm ⊢
    simp only []
    rw [(key m hm.1 hm.2).2.1]
    exact hm
  · intro h1 hh1 h2 hh2 heq
    rw [Finset.mem_image] at hh1 hh2
    obtain ⟨m1, hm1, rfl⟩ := hh1
    obtain ⟨m2, hm2, rfl⟩ := hh2
    rw [Finset.mem_Icc] at hm1 hm2
    have e1 := (key m1 hm1.1 hm1.2).2.1
    have e2 := (key m2 hm2.1 hm2.2).2.1
    have hm12 : m1 = m2 := e1.symm.trans (heq.trans e2)
    rw [hm12]
  · intro m hm
    rw [Finset.mem_Icc] at hm
    exact ⟨(m % (L : ℤ)).toNat,
      Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr hm), (key m hm.1 hm.2).2.1⟩
  · intro h hh
    rw [Finset.mem_image] at hh
    obtain ⟨m, hm, rfl⟩ := hh
    rw [Finset.mem_Icc] at hm
    simp only []
    rw [(key m hm.1 hm.2).2.1]
    exact (key m hm.1 hm.2).2.2

end CircleMethod

end
