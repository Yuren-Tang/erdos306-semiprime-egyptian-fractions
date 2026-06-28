import RequestProject.Spectral.Selection
import RequestProject.CircleMethodMainTerm

/-!
# Cannon bridge — deriving the circle-method existence step from `spectral_existence`

This file replaces the project's bespoke "C0/C5" collector stack (the finite
Fourier identity `wcount_fourier_identity`, the arc-separation positivity
`positivity_from_arcs` / `wcount_pos_of_split`, the `Wcount` real intermediary,
and the extraction `exists_subset_of_Wcount_pos`) with a single application of
the abstract **`spectral_existence`** cannon (`SpectralCannon.lean`).

The cannon is instantiated over:
* index set `J = {e // e ∈ E}` (the semiprime edges) with `A j = Bool` (each edge
  chosen or not);
* the additive group `X = ℤ` with the integer target `t = L/b` and
  `S a = ∑_{e chosen} L/e` (no wraparound thanks to `∑_E L/e < L`);
* frequency set `Ω = Fin L` and the additive characters `cannonChar`;
* local spectral factors `cannonB`, so that `cannonF = fourierTerm`.
-/

open Complex Finset BigOperators Real

set_option maxHeartbeats 2000000

noncomputable section

namespace CircleMethod

/-- The additive character `n ↦ exp(2πi·ω·n/L)` on `ℤ`, indexed by `ω : Fin L`. -/
def cannonChar (L : ℕ) (ω : Fin L) (n : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ) * (n : ℂ) / (L : ℂ))

/-- The local spectral factor of edge `j` at frequency `ω`:
`(1-θ_e) + θ_e·exp(2πi·ω·(L/e)/L)`, written as the Bernoulli expectation
`∑_{a∈Bool} p(a)·char(x(a))`. -/
def cannonB (E : Finset ℕ) (theta : ℕ → ℝ) (L : ℕ)
    (j : {e // e ∈ E}) (ω : Fin L) : ℂ :=
  ∑ a : Bool, ((if a then theta j.1 else 1 - theta j.1 : ℝ) : ℂ)
      * cannonChar L ω (if a then ((L / j.1 : ℕ) : ℤ) else 0)

/-- The spectral term at frequency `ω`: the product of the local factors times
the conjugate target phase.  Equal to `fourierTerm` (`cannonF_eq_fourierTerm`). -/
def cannonF (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (ω : Fin L) : ℂ :=
  (∏ j : {e // e ∈ E}, cannonB E theta L j ω)
    * (starRingEnd ℂ) (cannonChar L ω ((L / b : ℕ) : ℤ))

/-- `cannonChar` has unit norm. -/
lemma norm_cannonChar (L : ℕ) (ω : Fin L) (n : ℤ) : ‖cannonChar L ω n‖ = 1 := by
  unfold cannonChar; norm_num [ Complex.norm_exp ]

/-- The local factor equals the Bernoulli factor used in `fourierTerm`. -/
lemma cannonB_eq (E : Finset ℕ) (theta : ℕ → ℝ) (L : ℕ)
    (j : {e // e ∈ E}) (ω : Fin L) :
    cannonB E theta L j ω
      = (theta j.1 : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ) * ((L / j.1 : ℕ) : ℂ) / (L : ℂ))
        + (1 - theta j.1) := by
  unfold cannonB; simp +decide [ Fintype.sum_bool ];
  unfold cannonChar; norm_num;
  norm_cast ; aesop

/-- The norm of the local factor is `≤ 1` when `0 ≤ θ ≤ 1`. -/
lemma norm_cannonB_le_one (E : Finset ℕ) (theta : ℕ → ℝ) (L : ℕ)
    (j : {e // e ∈ E}) (ω : Fin L)
    (h0 : 0 ≤ theta j.1) (h1 : theta j.1 ≤ 1) :
    ‖cannonB E theta L j ω‖ ≤ 1 := by
  rw [ cannonB_eq ];
  convert norm_add_le ( ( theta j : ℂ ) * Complex.exp ( 2 * Real.pi * Complex.I * ( ω : ℂ ) * ( L / j : ℕ ) / L ) ) ( 1 - ( theta j : ℂ ) ) using 2 ; norm_num [ Complex.norm_exp ];
  norm_cast ; rw [ abs_of_nonneg h0 ] ; rw [ Real.norm_of_nonneg ] <;> linarith

/-- **Key correspondence.**  The cannon's spectral term equals the project's
`fourierTerm` at the underlying natural-number frequency. -/
lemma cannonF_eq_fourierTerm (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (ω : Fin L) :
    cannonF E theta b L ω = fourierTerm E theta b L (ω : ℕ) := by
  unfold cannonF fourierTerm;
  congr! 1;
  · refine' Finset.prod_bij ( fun j _ => j.val ) _ _ _ _ <;> simp +decide [ cannonB_eq ];
  · unfold cannonChar; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
    norm_cast ; ring ; norm_num

/-- **Character orthogonality on `Fin L`.**  Recast of `fourier_orthogonality`
over the finite type `Fin L`. -/
lemma charsum_orth (L : ℕ) (hL : 0 < L) (n : ℤ) :
    (∑ ω : Fin L, Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ) * (n : ℂ) / (L : ℂ)))
      = if (L : ℤ) ∣ n then (L : ℂ) else 0 := by
  split_ifs with h;
  · obtain ⟨ k, rfl ⟩ := h;
    convert Finset.sum_const ( 1 : ℂ );
    · exact Complex.exp_eq_one_iff.mpr ⟨ k * ‹Fin L›, by push_cast; rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hL.ne' ) ] ; ring ⟩;
    · norm_num;
  · set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * n / L);
    have hz_ne_one : z ≠ 1 := by
      rw [ Ne.eq_def, Complex.exp_eq_one_iff ];
      field_simp;
      exact fun ⟨ k, hk ⟩ => h <| by exact ⟨ k, by rw [ ← @Int.cast_inj ℂ ] ; push_cast; rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hL.ne' ) ] at hk; linear_combination hk ⟩ ;
    have h_geo_series : ∑ ω : Fin L, z ^ (ω : ℕ) = (z ^ L - 1) / (z - 1) := by
      erw [ ← Finset.sum_range ];
      rw [ geom_sum_eq hz_ne_one ];
    convert h_geo_series using 2;
    · rw [ ← Complex.exp_nat_mul ] ; ring;
    · rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff.mpr ⟨ n, by ring_nf; norm_num [ hL.ne' ] ⟩ ] ; norm_num

/-- For a finite count `m` and a positive slack `d`, some nonnegative exponential
decay makes `m·exp(-K)` fit within `d`. -/
lemma exists_K_tail (m : ℕ) (d : ℝ) (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ (m : ℝ) * Real.exp (-K) ≤ d := by
  refine ⟨ Real.log ( m / d + 1 ), Real.log_nonneg (by linarith [div_nonneg (Nat.cast_nonneg m) hd.le]), ?_ ⟩
  rw [ Real.exp_neg, Real.exp_log ( by positivity ) ]
  rw [ mul_inv_le_iff₀ ( by positivity ) ]
  nlinarith [ Real.log_le_sub_one_of_pos ( by positivity : 0 < ( m : ℝ ) / d + 1 ), mul_div_cancel₀ ( m : ℝ ) hd.ne' ]

/-
**Additive characters turn sums into products** (over any `Fintype` index).
-/
lemma cannonChar_sum_eq_prod (L : ℕ) (ω : Fin L) {ι : Type*} [Fintype ι] (g : ι → ℤ) :
    cannonChar L ω (∑ i, g i) = ∏ i, cannonChar L ω (g i) := by
  unfold cannonChar; simp +decide [ ← Complex.exp_int_mul, ← Complex.exp_sum ] ; ring;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ]

/-
Reindexing a sum over `s.attachFin` back to a sum over `s` (the summand only
depends on the underlying natural number).
-/
lemma sum_attachFin {β : Type*} [AddCommMonoid β] (L : ℕ) (SS : Finset ℕ)
    (h : ∀ m ∈ SS, m < L) (g : ℕ → β) :
    ∑ ω ∈ SS.attachFin h, g (ω : ℕ) = ∑ m ∈ SS, g m := by
  refine' Finset.sum_bij ( fun ω _ => ω ) _ _ _ _ <;> simp +decide [ Finset.mem_attachFin ];
  · exact fun a₁ ha₁ a₂ ha₂ h => Fin.ext h;
  · exact fun m hm => ⟨ ⟨ m, h m hm ⟩, hm, rfl ⟩

/-- `cannonF` summed over `SS.attachFin` equals `fourierTerm` summed over `SS`. -/
lemma cannonF_attachFin_sum (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (SS : Finset ℕ) (h : ∀ m ∈ SS, m < L) :
    ∑ ω ∈ SS.attachFin h, cannonF E theta b L ω
      = ∑ m ∈ SS, fourierTerm E theta b L m := by
  rw [Finset.sum_congr rfl (fun ω _ => cannonF_eq_fourierTerm E theta b L ω)]
  exact sum_attachFin L SS h (fun m => fourierTerm E theta b L m)

/-
**Pointwise tail bound.**  With `Δ ω j = -log‖cannonB‖` (and a nonnegative
fallback `Ktail` at the zeros), `exp(-∑_j Δ ω j)` is bounded by the norm of the
spectral term plus `exp(-Ktail)`.
-/
lemma cannon_tail_pointwise (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
    (hthlb : ∀ e ∈ E, 0 ≤ theta e) (hthub : ∀ e ∈ E, theta e ≤ 1)
    (Ktail : ℝ) (hK0 : 0 ≤ Ktail) (ω : Fin L) :
    Real.exp (-(∑ j : {e // e ∈ E},
        (if ‖cannonB E theta L j ω‖ = 0 then Ktail
         else - Real.log ‖cannonB E theta L j ω‖)))
      ≤ ‖fourierTerm E theta b L (ω : ℕ)‖ + Real.exp (-Ktail) := by
  by_cases h : ∃ j : { e // e ∈ E }, ‖cannonB E theta L j ω‖ = 0;
  · obtain ⟨ j, hj ⟩ := h; simp_all +decide [ Finset.prod_eq_zero ( Finset.mem_univ j ) ] ;
    refine' le_trans _ ( le_add_of_nonneg_left <| norm_nonneg _ );
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_attach _ j ) ];
    simp [hj];
    exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun x _ => by split_ifs <;> first | positivity | exact neg_nonneg_of_nonpos <| Real.log_nonpos ( norm_nonneg _ ) <| by exact le_trans ( norm_cannonB_le_one E theta L x ω ( hthlb _ <| x.2 ) ( hthub _ <| x.2 ) ) <| by norm_num ) <| Finset.mem_attach _ j );
  · simp_all +decide [ Finset.sum_ite ];
    rw [ Real.exp_sum, Finset.prod_congr rfl fun x hx => Real.exp_log ( norm_pos_iff.mpr ( h _ x.2 ) ) ];
    rw [ show fourierTerm E theta b L ω = cannonF E theta b L ω by rw [ cannonF_eq_fourierTerm ] ];
    unfold cannonF;
    norm_num [ norm_mul, norm_cannonChar ];
    positivity

/-
**Decode.**  A hitting configuration `a` decodes to a subset of `E` with the
exact reciprocal identity.
-/
lemma decode_subset_sum (E : Finset ℕ) (b L : ℕ) (hb : 2 ≤ b) (hL : 0 < L)
    (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L) (he0 : ∀ e ∈ E, 0 < e)
    (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (a : {e // e ∈ E} → Bool)
    (ha : (∑ j : {e // e ∈ E}, (if a j then ((L / j.1 : ℕ) : ℤ) else 0))
            = ((L / b : ℕ) : ℤ)) :
    (∑ e ∈ (Finset.univ.filter (fun j : {e // e ∈ E} => a j)).image Subtype.val,
        (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / (b : ℚ) := by
  rw [ Finset.sum_image ];
  · convert congr_arg ( fun x : ℤ => x / ( L : ℚ ) ) ha using 1;
    · push_cast [ Finset.sum_filter ];
      rw [ Finset.sum_div _ _ _ ] ; congr ; ext ; split_ifs <;> simp +decide [ *, Nat.cast_div ];
      rw [ eq_div_iff ( by positivity ) ] ; ring;
    · rw [ div_eq_div_iff ] <;> norm_cast <;> nlinarith [ Nat.div_mul_cancel hbL ];
  · exact fun x hx y hy hxy => Subtype.ext hxy

/-- **Cannon bridge (existence of a hitting subset).**  From the finite-Fourier
data of a circle-method construction — the no-wraparound divisibility hypotheses,
a frequency partition `range L = SM ∪ Sm`, a low-frequency real-part lower bound
`M`, and a (summed-norm) high-frequency tail bound `Bm < M` — the abstract
`spectral_existence` cannon yields a subset `S ⊆ E` whose reciprocal sum is `1/b`.

This single theorem subsumes `wcount_fourier_identity`, `positivity_from_arcs`,
`wcount_pos_of_split` and `exists_subset_of_Wcount_pos`. -/
theorem exists_subset_of_fourier_arcs
    (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ) (SM Sm : Finset ℕ) (Bm M : ℝ)
    (hb : 2 ≤ b) (hL : 0 < L) (hbL : b ∣ L) (heL : ∀ e ∈ E, e ∣ L)
    (he0 : ∀ e ∈ E, 0 < e) (hbound : (∑ e ∈ E, (L / e : ℕ)) < L)
    (hthlb : ∀ e ∈ E, 0 ≤ theta e) (hthub : ∀ e ∈ E, theta e ≤ 1)
    (hpart : Finset.range L = SM ∪ Sm) (hdisj : Disjoint SM Sm)
    (hmain : M ≤ (∑ h ∈ SM, fourierTerm E theta b L h).re)
    (hminorSum : (∑ h ∈ Sm, ‖fourierTerm E theta b L h‖) ≤ Bm)
    (hbeat : Bm < M) :
    ∃ S ⊆ E, (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / (b : ℚ) := by
  classical
  have hSML : ∀ m ∈ SM, m < L := by
    intro m hm; exact Finset.mem_range.mp (hpart ▸ Finset.mem_union_left _ hm)
  have hSmL : ∀ m ∈ Sm, m < L := by
    intro m hm; exact Finset.mem_range.mp (hpart ▸ Finset.mem_union_right _ hm)
  obtain ⟨Ktail, hK0, hKtail⟩ := exists_K_tail Sm.card ((M - Bm) / 2) (by linarith)
  obtain ⟨a, ha⟩ := spectral_existence
      (J := {e // e ∈ E}) (Ω := Fin L) (X := ℤ) (A := fun _ => Bool)
      (p := fun j a => if a then theta j.1 else 1 - theta j.1)
      (t := ((L / b : ℕ) : ℤ))
      (S := fun a => ∑ j : {e // e ∈ E}, (if a j then ((L / j.1 : ℕ) : ℤ) else 0))
      (N := (L : ℝ)) (hN := by exact_mod_cast hL)
      (k := fun ω n => cannonChar L ω n)
      (hspec := by
        intro a;
        have h_no_wraparound : |(∑ j : {e // e ∈ E}, (if a j then ((L / j.1 : ℕ) : ℤ) else 0)) - ((L / b : ℕ) : ℤ)| < L := by
          refine' abs_sub_lt_iff.mpr ⟨ _, _ ⟩;
          · refine' lt_of_le_of_lt ( sub_le_self _ <| Nat.cast_nonneg _ ) _;
            refine' lt_of_le_of_lt _ ( Nat.cast_lt.mpr hbound );
            norm_num [ Finset.sum_ite ];
            refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) _;
            exact Finset.attach E;
            · exact Finset.filter_subset _ _;
            · exact fun _ _ _ => Nat.cast_nonneg _;
            · refine' le_of_eq _;
              refine' Finset.sum_bij ( fun x hx => x.val ) _ _ _ _ <;> aesop;
          · refine' lt_of_le_of_lt ( sub_le_self _ <| Finset.sum_nonneg fun _ _ => by positivity ) _;
            exact_mod_cast Nat.div_lt_self hL ( by linarith );
        have h_charsum : ∑ ω : Fin L, Complex.exp (2 * Real.pi * Complex.I * (ω : ℂ) * ((∑ j : {e // e ∈ E}, (if a j then ((L / j.1 : ℕ) : ℤ) else 0) - ((L / b : ℕ) : ℤ)) : ℂ) / (L : ℂ)) = if (L : ℤ) ∣ ((∑ j : {e // e ∈ E}, (if a j then ((L / j.1 : ℕ) : ℤ) else 0)) - ((L / b : ℕ) : ℤ)) then (L : ℂ) else 0 := by
          convert charsum_orth L hL _ using 1;
          grind;
        convert congr_arg ( fun x : ℂ => ( 1 / L : ℂ ) * x ) h_charsum.symm using 1;
        · split_ifs <;> norm_num [ hL.ne' ];
          · aesop;
          · exact ‹¬_› ( by obtain ⟨ k, hk ⟩ := ‹_›; nlinarith [ show k = 0 by nlinarith [ abs_lt.mp h_no_wraparound ] ] );
        · norm_num [ cannonChar, Complex.exp_sub ];
          norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_sub, sub_div ];
          norm_cast ; norm_num [ Real.cos_sub, Real.sin_sub ];
          exact Or.inl ( by rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by ring ))
      (x := fun j a => if a then ((L / j.1 : ℕ) : ℤ) else 0)
      (b := fun j ω => cannonB E theta L j ω)
      (hb_def := by intro j ω; rfl)
      (hfact := fun a ω =>
        cannonChar_sum_eq_prod L ω (fun j => if a j then ((L / j.1 : ℕ) : ℤ) else 0))
      (F := fun ω => cannonF E theta b L ω)
      (hF_def := by intro ω; rfl)
      (L := SM.attachFin hSML) (H := Sm.attachFin hSmL)
      (hdisj := by
        rw [Finset.disjoint_left]
        intro ω hω hω'
        exact Finset.disjoint_left.mp hdisj
          ((Finset.mem_attachFin hSML).mp hω) ((Finset.mem_attachFin hSmL).mp hω'))
      (hcover := by
        ext ω
        simp only [Finset.mem_union, Finset.mem_attachFin, Finset.mem_univ, iff_true]
        have hmem : (ω : ℕ) ∈ Finset.range L := Finset.mem_range.mpr ω.is_lt
        rw [hpart] at hmem
        exact Finset.mem_union.mp hmem)
      (M := M) (R := Bm + (M - Bm) / 2)
      (hM := by
        show M ≤ (∑ ω ∈ SM.attachFin hSML, cannonF E theta b L ω).re
        rw [cannonF_attachFin_sum E theta b L SM hSML]; exact hmain)
      (Δ := fun ω j => if ‖cannonB E theta L j ω‖ = 0 then Ktail
                       else - Real.log ‖cannonB E theta L j ω‖)
      (C := fun _ => 1)
      (hb := by
        intro ω _ j
        show ‖cannonB E theta L j ω‖ ≤ Real.exp (-(if ‖cannonB E theta L j ω‖ = 0
          then Ktail else -Real.log ‖cannonB E theta L j ω‖))
        rcases eq_or_ne ‖cannonB E theta L j ω‖ 0 with hz | hz
        · rw [if_pos hz, hz]; exact (Real.exp_pos _).le
        · apply le_of_eq
          rw [if_neg hz, neg_neg,
            Real.exp_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))])
      (hk := fun ω _ => le_of_eq (norm_cannonChar L ω _))
      (hR := by
        have hre : (∑ ω ∈ Sm.attachFin hSmL, ‖fourierTerm E theta b L (ω : ℕ)‖)
            = ∑ m ∈ Sm, ‖fourierTerm E theta b L m‖ :=
          sum_attachFin L Sm hSmL (fun m => ‖fourierTerm E theta b L m‖)
        have hstep : (∑ ω ∈ Sm.attachFin hSmL,
              (‖fourierTerm E theta b L (ω : ℕ)‖ + Real.exp (-Ktail)))
            ≤ Bm + (M - Bm) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_attachFin, nsmul_eq_mul, hre]
          linarith [hminorSum, hKtail]
        refine le_trans (Finset.sum_le_sum (fun ω _ => ?_)) hstep
        show (1 : ℝ) * Real.exp (-(∑ j : {e // e ∈ E},
            if ‖cannonB E theta L j ω‖ = 0 then Ktail
            else -Real.log ‖cannonB E theta L j ω‖)) ≤ _
        rw [one_mul]
        exact cannon_tail_pointwise E theta b L hthlb hthub Ktail hK0 ω)
      (hMR := by linarith)
  -- Decode `∃ a, S a = t` into the subset and the reciprocal identity.
  refine ⟨(Finset.univ.filter (fun j : {e // e ∈ E} => a j)).image Subtype.val, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨j, _, rfl⟩ := he
    exact j.2
  · exact decode_subset_sum E b L hb hL hbL heL he0 hbound a ha

/-- **Representation from a hitting subset.**  Bundles a subset `S ⊆ E` with the
reciprocal identity into an Egyptian semiprime representation avoiding `T`. -/
theorem repr_of_subset (T E : Finset ℕ) (b : ℕ)
    (hsemi : ∀ e ∈ E, IsSemiprime e) (hdisj : ∀ e ∈ E, e ∉ T)
    (S : Finset ℕ) (hSE : S ⊆ E)
    (hSsum : (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / (b : ℚ)) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  refine ⟨S, fun n hn => hsemi n (hSE hn), ?_, hSsum⟩
  rw [Finset.disjoint_left]
  exact fun a haS haT => hdisj a (hSE haS) haT

end CircleMethod

end
