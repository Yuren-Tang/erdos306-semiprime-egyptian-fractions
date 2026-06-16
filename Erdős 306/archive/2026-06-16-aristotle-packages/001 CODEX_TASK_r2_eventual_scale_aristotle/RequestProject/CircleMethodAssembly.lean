import RequestProject.CircleMethod
import RequestProject.CircleMethodMainTerm

open Complex Finset BigOperators Real

noncomputable section

namespace CircleMethod

/-!
# Phase C — R3 assembly glue (note 35 C5 / note 44 R3)

Pure arc-separation positivity: given the Fourier identity split
`range L = SM ⊎ Sm`, a real lower bound on the main-arc real part, a norm bound on
the minor-arc sum, and an imaginary-part bound on the main-arc sum (all supplied by
`main_sum_re_lower` and `minor_arc_bound`), `Wcount > 0` follows from
`positivity_from_arcs`.  No `BlockSystem`; everything BlockSystem-specific enters
only through the hypotheses.
-/

/-- **R3 separation glue.**  The Fourier sum splits into a main-arc part with
positive real part and a minor part of small norm; folding the main-arc imaginary
part into the minor remainder, `positivity_from_arcs` gives `Wcount > 0`. -/
lemma wcount_pos_of_split
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (hb : 2 ≤ b) (hL : 0 < L) (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L)
    (he0 : ∀ e ∈ E, 0 < e) (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (SM Sm : Finset ℕ)
    (hpart : Finset.range L = SM ∪ Sm) (hdisj : Disjoint SM Sm)
    (mainPos Bm Bi : ℝ)
    (hmainPos : 0 < mainPos)
    (hmain_re : mainPos ≤ (∑ h ∈ SM, fourierTerm E theta b L h).re)
    (hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm)
    (hmain_im : |(∑ h ∈ SM, fourierTerm E theta b L h).im| ≤ Bi)
    (hbeat : Bm + Bi < mainPos) :
    0 < Wcount E theta b := by
  set SMsum : ℂ := ∑ h ∈ SM, fourierTerm E theta b L h with hSM
  set Smsum : ℂ := ∑ h ∈ Sm, fourierTerm E theta b L h with hSm
  -- Fourier identity: (L:ℂ)·Wcount = ∑_{range L} fourierTerm = SMsum + Smsum
  have hsplit : (∑ h ∈ Finset.range L, fourierTerm E theta b L h) = SMsum + Smsum := by
    rw [hSM, hSm, ← Finset.sum_union hdisj, ← hpart]
  have hident0 : (L : ℂ) * (Wcount E theta b : ℂ)
      = ∑ h ∈ Finset.range L, fourierTerm E theta b L h := by
    rw [wcount_fourier_identity E theta b L hb hL hbL heL he0 hbound]
    rfl
  -- main := Re SMsum, minorSum := Smsum + (SMsum − Re SMsum) = Smsum + i·Im SMsum
  set main : ℝ := SMsum.re with hmaindef
  set minorSum : ℂ := Smsum + (SMsum - (SMsum.re : ℂ)) with hminordef
  have hident : (L : ℂ) * (Wcount E theta b : ℂ) = (main : ℂ) + minorSum := by
    rw [hident0, hsplit, hminordef, hmaindef]; ring
  -- main is large; minorSum is small
  have hmainpos' : 0 < main := lt_of_lt_of_le hmainPos hmain_re
  have himeq : SMsum - (SMsum.re : ℂ) = (SMsum.im : ℂ) * Complex.I := by
    have := Complex.re_add_im SMsum
    linear_combination -this
  have hminorbnd : ‖minorSum‖ ≤ Bm + Bi := by
    rw [hminordef]
    refine le_trans (norm_add_le _ _) ?_
    rw [himeq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add hminor hmain_im
  have hbeat' : Bm + Bi < main := lt_of_lt_of_le hbeat hmain_re
  exact positivity_from_arcs L hL (Wcount E theta b) main (Bm + Bi) minorSum
    hident hmainpos' hminorbnd hbeat'

/-- **C5 full assembly (b ≥ 2).**  From a circle-method construction — semiprime
edges `E` avoiding `T` with weights `θ ∈ [1/3,2/3]`, exact mass `∑θ_e/e = 1/b`, a
common period `L`, the main-arc label bijection (CRT/periodicity), the main-arc
smallness conditions, and a minor-arc bound `Bm` beaten by the Gaussian main term
`c₃/σ_E` — the deterministic weighted count is strictly positive.  This is the
verified circle-method core: main arc (`main_sum_re_lower`, real by
`main_sum_im_zero`) beats minor arc, via `wcount_pos_of_split`. -/
theorem exists_pos_weighted_of_construction
    (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b)
    (E : Finset ℕ) (theta : ℕ → ℝ) (L : ℕ) (N : ℤ) (SM Sm : Finset ℕ) (lbl : ℕ → ℤ)
    (Bm : ℝ)
    (hsemi : ∀ e ∈ E, IsSemiprime e) (havoid : ∀ e ∈ E, e ∉ T)
    (hne : E.Nonempty) (hL : 0 < L) (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L)
    (he0 : ∀ e ∈ E, 0 < e) (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (hlb : ∀ e ∈ E, 1/3 ≤ theta e) (hub : ∀ e ∈ E, theta e ≤ 2/3)
    (hmass : (∑ e ∈ E, theta e / (e : ℝ)) = 1 / (b : ℝ))
    (hpart : Finset.range L = SM ∪ Sm) (hdisj : Disjoint SM Sm)
    (hN : (1:ℝ) / Real.sqrt (sigmaE2 E theta) ≤ (N:ℝ))
    (htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10)
    (hsmall : ∀ m ∈ Finset.Icc (-N) N, (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10)
    (hmaps : ∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N)
    (hinj : ∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂)
    (hsurj : ∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m)
    (hterm : ∀ h ∈ SM, fourierTerm E theta b L h = term_label E theta b (lbl h))
    (hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm)
    (hbeat : Bm < 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)) :
    0 < Wcount E theta b := by
  have hσ2pos : 0 < sigmaE2 E theta := sigmaE2_pos E theta hne he0 hlb hub
  have hσpos : 0 < Real.sqrt (sigmaE2 E theta) := Real.sqrt_pos.mpr hσ2pos
  set mainPos : ℝ := 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)
    with hmainPosDef
  have hmainPos : 0 < mainPos := by
    rw [hmainPosDef]; positivity
  have hmain_re : mainPos ≤ (∑ h ∈ SM, fourierTerm E theta b L h).re :=
    main_sum_re_lower E theta b L N SM lbl hne he0 hlb hub hmass hN htw hsmall
      hmaps hinj hsurj hterm
  have hmain_im : |(∑ h ∈ SM, fourierTerm E theta b L h).im| ≤ 0 := by
    rw [main_sum_im_zero E theta b L N SM lbl hmaps hinj hsurj hterm, abs_zero]
  exact wcount_pos_of_split E theta b L hb hL hbL heL he0 hbound SM Sm hpart hdisj
    mainPos Bm 0 hmainPos hmain_re hminor hmain_im (by linarith [hbeat])

/-- **R2 construction interface (note 35 C1 / note 44 R3).**  The data of a
block-aligned circle-method construction for `1/b`: semiprime edges `E` avoiding
`T` with weights in `[1/3,2/3]` and exact mass, a common period `L`, a main-arc
frequency set `SM` bijecting (via `lbl`) to the label window `[-N,N]` with the
CRT/periodicity identity `fourierTerm = term_label`, the main-arc smallness
conditions, and a minor-arc bound `Bm` strictly beaten by the Gaussian main term
`c₃/σ_E`.  Exactly the hypotheses consumed by `exists_pos_weighted_of_construction`. -/
structure ArcConstruction (T : Finset ℕ) (b : ℕ) where
  E : Finset ℕ
  theta : ℕ → ℝ
  L : ℕ
  N : ℤ
  SM : Finset ℕ
  Sm : Finset ℕ
  lbl : ℕ → ℤ
  Bm : ℝ
  hsemi : ∀ e ∈ E, IsSemiprime e
  havoid : ∀ e ∈ E, e ∉ T
  hne : E.Nonempty
  hL : 0 < L
  hbL : b ∣ L
  heL : ∀ e ∈ E, e ∣ L
  he0 : ∀ e ∈ E, 0 < e
  hbound : (∑ e ∈ E, (L / e : ℕ)) < L
  hlb : ∀ e ∈ E, 1/3 ≤ theta e
  hub : ∀ e ∈ E, theta e ≤ 2/3
  hmass : (∑ e ∈ E, theta e / (e : ℝ)) = 1 / (b : ℝ)
  hpart : Finset.range L = SM ∪ Sm
  hdisj : Disjoint SM Sm
  hN : (1:ℝ) / Real.sqrt (sigmaE2 E theta) ≤ (N:ℝ)
  htw : ∀ m ∈ Finset.Icc (-N) N, ∀ e ∈ E, |(m : ℝ) / (e : ℝ)| ≤ 1/10
  hsmall : ∀ m ∈ Finset.Icc (-N) N, (∑ e ∈ E, 100000 * |(m:ℝ)/(e:ℝ)|^3) ≤ 1/10
  hmaps : ∀ h ∈ SM, lbl h ∈ Finset.Icc (-N) N
  hinj : ∀ h₁ ∈ SM, ∀ h₂ ∈ SM, lbl h₁ = lbl h₂ → h₁ = h₂
  hsurj : ∀ m ∈ Finset.Icc (-N) N, ∃ h ∈ SM, lbl h = m
  hterm : ∀ h ∈ SM, fourierTerm E theta b L h = term_label E theta b (lbl h)
  hminor : ‖∑ h ∈ Sm, fourierTerm E theta b L h‖ ≤ Bm
  hbeat : Bm < 0.8 * (Real.exp (-(Real.pi^2/2)) / 2) / Real.sqrt (sigmaE2 E theta)

/-- **THE SINGLE REMAINING GAP of the unconditional proof** (the block-aligned
circle-method construction, `R2`).

**Status: open `sorry`.**  This is the *only* `sorry` reachable from the target
theorem `erdos_306` (see `Erdos306Unconditional.lean`); the surrounding
circle-method analytic core `exists_pos_weighted_of_construction` is fully
verified.  The `R2*` files reduce this statement (sorry-free) to explicit
number-theoretic supply estimates, but the reduction is not yet grounded in a
concrete block system, and its minor-arc input rests on the still-unfinished
Phase-G global control (`GlobalControl.lean`).  Closing it requires constructing
a concrete admissible block system and discharging the Phase-G minor-arc
estimates.  It is kept as an explicit, documented `sorry` (adding a cited
`axiom` is disallowed in this packet).

For squarefree `b ≥ 3`
there is a block-aligned construction whose minor arc is beaten by the main term.
This packages the C1 edge construction aligned to a block system (`E`-primes ⊆
`blockSupport`, `ctrlEdges ⊆ E`), the CRT main-arc bijection, and the
`σ_E ≍ σ_ctrl` / large-`k0,C` separation.  (`b = 2` is handled separately by the
`1/2 = 1/3 + 1/6` reduction; see note 50 §3 — block-aligned mass cannot reach the
common-θ window for `b = 2`.) -/
theorem exists_arcConstruction (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b)
    (hbsf : Squarefree b) : Nonempty (ArcConstruction T b) := by
  sorry

/-- **C5 (b ≥ 3)**, assembled from the R2 construction via the verified analytic
core `exists_pos_weighted_of_construction`. -/
theorem exists_pos_weighted_ge3 (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b)
    (hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (theta : ℕ → ℝ),
      (∀ e ∈ E, IsSemiprime e) ∧ (∀ e ∈ E, e ∉ T) ∧ 0 < Wcount E theta b := by
  obtain ⟨c⟩ := exists_arcConstruction T b hb hbsf
  exact ⟨c.E, c.theta, c.hsemi, c.havoid,
    exists_pos_weighted_of_construction T b (le_trans (by norm_num) hb)
      c.E c.theta c.L c.N c.SM c.Sm c.lbl c.Bm
      c.hsemi c.havoid c.hne c.hL c.hbL c.heL c.he0 c.hbound c.hlb c.hub c.hmass
      c.hpart c.hdisj c.hN c.htw c.hsmall c.hmaps c.hinj c.hsurj c.hterm c.hminor c.hbeat⟩

/-- A semiprime Egyptian representation of `1/b` avoiding `T`, for squarefree
`b ≥ 3` (positivity ⟹ extraction). -/
theorem egyptian_rep_ge3 (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1:ℚ) / (b:ℚ)) := by
  obtain ⟨E, theta, hsemi, hdisj, hW⟩ := exists_pos_weighted_ge3 T b hb hbsf
  exact Wcount_pos_imp_repr T E theta b hsemi hdisj hW

/-- **The `b = 2` reduction (note 50 §3).**  `1/2 = 1/3 + 1/6`; both `3` and `6`
are squarefree `≥ 3`, so they get circle-method representations on cumulative
obstruction sets, disjoint-unioned. -/
theorem egyptian_rep_eq2 (T : Finset ℕ) :
    HasEgyptianSemiprimeReprAvoiding T ((1:ℚ) / (2:ℚ)) := by
  have sf6 : Squarefree 6 := by
    show Squarefree (2 * 3)
    rw [Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  obtain ⟨S3, hs3semi, hs3disj, hs3sum⟩ :=
    egyptian_rep_ge3 T 3 (by norm_num) Nat.prime_three.squarefree
  obtain ⟨S6, hs6semi, hs6disj, hs6sum⟩ :=
    egyptian_rep_ge3 (T ∪ S3) 6 (by norm_num) sf6
  obtain ⟨hs6T, hs6S3⟩ := Finset.disjoint_union_right.mp hs6disj
  refine ⟨S3 ∪ S6, ?_, Finset.disjoint_union_left.mpr ⟨hs3disj, hs6T⟩, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hs3semi e h
    · exact hs6semi e h
  · rw [Finset.sum_union hs6S3.symm, hs3sum, hs6sum]; norm_num

/-- A semiprime Egyptian representation of `1/b` avoiding `T`, for squarefree
`b ≥ 2`: `b = 2` via the `1/3 + 1/6` reduction, `b ≥ 3` via the circle method. -/
theorem egyptian_rep_ge2 (T : Finset ℕ) (b : ℕ) (hb : 2 ≤ b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1:ℚ) / (b:ℚ)) := by
  rcases Nat.eq_or_lt_of_le hb with hb2 | hb3
  · rw [← hb2]; exact egyptian_rep_eq2 T
  · exact egyptian_rep_ge3 T b hb3 hbsf

/-- **The `b = 1` input, PROVED via `1 = 1/2 + 1/3 + 1/6`.**  Each `1/bᵢ`
(`bᵢ ∈ {2,3,6}`, all squarefree `≥ 2`) gets a semiprime representation avoiding the
cumulative obstruction set, so their disjoint union is a distinct-semiprime set
avoiding `T` with reciprocal sum exactly `1`.  This folds the `b = 1` case into the
`b ≥ 2` circle method (no separate construction). -/
theorem exists_semiprime_egyptian_one (T : Finset ℕ) :
    ∃ G : Finset ℕ, (∀ e ∈ G, IsSemiprime e) ∧ (∀ e ∈ G, e ∉ T) ∧
      (∑ e ∈ G, (1:ℚ) / (e:ℚ)) = 1 := by
  have sf6 : Squarefree 6 := by
    show Squarefree (2 * 3)
    rw [Nat.squarefree_mul_iff]
    exact ⟨by norm_num, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
  obtain ⟨S2, hs2semi, hs2disj, hs2sum⟩ :=
    egyptian_rep_ge2 T 2 (by norm_num) Nat.prime_two.squarefree
  obtain ⟨S3, hs3semi, hs3disj, hs3sum⟩ :=
    egyptian_rep_ge2 (T ∪ S2) 3 (by norm_num) Nat.prime_three.squarefree
  obtain ⟨S6, hs6semi, hs6disj, hs6sum⟩ :=
    egyptian_rep_ge2 (T ∪ S2 ∪ S3) 6 (by norm_num) sf6
  obtain ⟨hs3T, hs3S2⟩ := Finset.disjoint_union_right.mp hs3disj
  obtain ⟨hs6TS2, hs6S3⟩ := Finset.disjoint_union_right.mp hs6disj
  obtain ⟨hs6T, hs6S2⟩ := Finset.disjoint_union_right.mp hs6TS2
  have hd23 : Disjoint S2 S3 := hs3S2.symm
  have hd26 : Disjoint S2 S6 := hs6S2.symm
  have hd36 : Disjoint S3 S6 := hs6S3.symm
  refine ⟨S2 ∪ S3 ∪ S6, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h6
    · rcases Finset.mem_union.mp h with h2 | h3
      · exact hs2semi e h2
      · exact hs3semi e h3
    · exact hs6semi e h6
  · intro e he
    rcases Finset.mem_union.mp he with h | h6
    · rcases Finset.mem_union.mp h with h2 | h3
      · exact Finset.disjoint_left.mp hs2disj h2
      · exact Finset.disjoint_left.mp hs3T h3
    · exact Finset.disjoint_left.mp hs6T h6
  · have hd_23_6 : Disjoint (S2 ∪ S3) S6 := Finset.disjoint_union_left.mpr ⟨hd26, hd36⟩
    rw [Finset.sum_union hd_23_6, Finset.sum_union hd23, hs2sum, hs3sum, hs6sum]
    norm_num

/-- **The `b = 1` case** (target `1/1 = 1`).  With the uniform weight `θ ≡ 1/2`, the
full set `G` from `exists_semiprime_egyptian_one` is itself a reciprocal-`1` subset,
contributing `(1/2)^{|G|} > 0` to `Wcount`, and every term is nonnegative. -/
theorem exists_positive_weighted_construction_one (T : Finset ℕ) :
    ∃ (E : Finset ℕ) (theta : ℕ → ℝ),
      (∀ e ∈ E, IsSemiprime e) ∧ (∀ e ∈ E, e ∉ T) ∧ 0 < Wcount E theta 1 := by
  obtain ⟨G, hsemi, havoid, hsum⟩ := exists_semiprime_egyptian_one T
  refine ⟨G, fun _ => 1/2, hsemi, havoid, ?_⟩
  unfold Wcount
  have hmem : G ∈ G.powerset := Finset.mem_powerset.mpr (le_refl G)
  set g : Finset ℕ → ℝ := fun S =>
    if (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / ((1:ℕ) : ℚ) then
      (∏ e ∈ S, (1/2 : ℝ)) * (∏ e ∈ G \ S, (1 - 1/2 : ℝ)) else 0 with hg
  have hGterm : 0 < g G := by
    rw [hg]; dsimp only
    rw [if_pos (by rw [hsum]; norm_num), Finset.sdiff_self]
    simp only [Finset.prod_empty, mul_one]
    positivity
  have hnonneg : ∀ S ∈ G.powerset, 0 ≤ g S := by
    intro S _; rw [hg]; dsimp only; split
    · positivity
    · exact le_refl 0
  exact lt_of_lt_of_le hGterm (Finset.single_le_sum hnonneg hmem)

/-- **C5 (positivity ⟹ representation).**  For squarefree `b > 0` and finite `T`,
`1/b` has a distinct-semiprime Egyptian representation avoiding `T`.  Dispatched by
size: `b = 1` via the explicit `1 = 1/2 + 1/3 + 1/6` weighted construction; `b ≥ 2`
via `egyptian_rep_ge2` (`b = 2` is the `1/3 + 1/6` reduction, `b ≥ 3` is the circle
method on the R2 construction). -/
theorem circle_method_positivity
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  rcases Nat.lt_or_ge b 2 with hb1 | hb2
  · have hb1' : b = 1 := by omega
    subst hb1'
    obtain ⟨E, theta, hsemi, hdisj, hW⟩ := exists_positive_weighted_construction_one T
    exact Wcount_pos_imp_repr T E theta 1 hsemi hdisj hW
  · exact egyptian_rep_ge2 T b hb2 hbsf

end CircleMethod

end
