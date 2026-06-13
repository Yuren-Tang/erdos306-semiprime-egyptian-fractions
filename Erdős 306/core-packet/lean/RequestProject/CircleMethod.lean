/-
# Circle Method — translation of note `35` (Translation-Ready Spec)

This file translates the final layer of the Erdős 306 proof: from the global
control theorem (note `34`, Phase G — see `GlobalControl.lean`) to
`fourier_positivity_unconditional`.  It follows the section structure of note
`35`:

* **C0** — the deterministic weighted count `Wcount` and the extraction
  principle `Wcount_pos_imp_repr` (the "`W > 0 ⟹ subset extraction ⟹
  representation`" step).  **Proved.**
* **C0 (Fourier identity)** — the finite orthogonality identity on `ZMod L`
  (`fourier_orthogonality`).  **Proved** (pure finite algebra).
* **C1–C4** — the edge construction and the analytic main-arc / minor-arc
  estimates.  These are bundled into the single existence statement
  `exists_positive_weighted_construction` (the analytic heart of the circle
  method).  **Named `sorry`** — this is the residual that the Phase-G global
  control (`GlobalControl.lean`) and the main-arc Taylor estimate
  (`BernoulliFourier.main_arc_positive`) are designed to discharge.
* **C5** — positivity ⟹ closing `fourier_positivity_unconditional`.  Assembled
  in `FourierPositivity.lean` from the two pieces above.

The decomposition is faithful: `Wcount_pos_imp_repr` is the genuine extraction
content (CP 01 §7 / note 35 C5), and the analytic positivity is isolated as one
precisely-named existence statement.
-/
import Mathlib
import RequestProject.Defs

open scoped BigOperators Classical
open Finset

noncomputable section

namespace CircleMethod

/-! ## C0. The deterministic weighted count -/

/-- The deterministic weighted count of note `35` C0, written over subsets
    `S ⊆ E` directly (no probability space).  For each subset `S` whose
    reciprocal sum hits the target `1/b`, we add the Bernoulli weight
    `(∏_{e∈S} θ_e)·(∏_{e∈E∖S} (1-θ_e))`; otherwise the term is `0`.

    `Wcount E θ b > 0` is *equivalent* to the existence of a subset
    `S ⊆ E` with `∑_{e∈S} 1/e = 1/b`; the analytic part of the circle method
    proves the left side, this file proves the right side gives a
    representation. -/
def Wcount (E : Finset ℕ) (theta : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ S ∈ E.powerset,
    (if (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / (b : ℚ) then
      (∏ e ∈ S, theta e) * (∏ e ∈ E \ S, (1 - theta e)) else 0)

/-- **C0 / C5 (extraction).**  If the deterministic weighted count is positive,
    then there is a subset `S ⊆ E` whose reciprocal sum equals `1/b`.

    The proof is elementary: every term whose indicator is false is exactly `0`,
    so a positive total sum forces at least one subset to satisfy the reciprocal
    identity. -/
theorem exists_subset_of_Wcount_pos (E : Finset ℕ) (theta : ℕ → ℝ) (b : ℕ)
    (hW : 0 < Wcount E theta b) :
    ∃ S ⊆ E, (∑ e ∈ S, (1 : ℚ) / (e : ℚ)) = (1 : ℚ) / (b : ℚ) := by
  by_contra hcon
  push_neg at hcon
  have hzero : Wcount E theta b = 0 := by
    unfold Wcount
    apply Finset.sum_eq_zero
    intro S hS
    rw [if_neg]
    exact hcon S (Finset.mem_powerset.mp hS)
  rw [hzero] at hW
  exact lt_irrefl 0 hW

/-- **C0 / C5 (representation).**  If the deterministic weighted count is
    positive and every edge value is a squarefree semiprime avoiding the
    obstruction set `T`, then `1/b` has an Egyptian semiprime representation
    avoiding `T`. -/
theorem Wcount_pos_imp_repr (T E : Finset ℕ) (theta : ℕ → ℝ) (b : ℕ)
    (hsemi : ∀ e ∈ E, IsSemiprime e) (hdisj : ∀ e ∈ E, e ∉ T)
    (hW : 0 < Wcount E theta b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  obtain ⟨S, hSE, hSsum⟩ := exists_subset_of_Wcount_pos E theta b hW
  refine ⟨S, ?_, ?_, hSsum⟩
  · exact fun n hn => hsemi n (hSE hn)
  · rw [Finset.disjoint_left]
    exact fun a haS haT => hdisj a (hSE haS) haT

/-! ## C0. Finite Fourier orthogonality on `ZMod L`

The orthogonality relation `(1/L) ∑_{h} e(h·n/L) = 𝟙[L ∣ n]` underlies the
Fourier identity of note 35 C0.  We record it in the additive-character form
used there. -/

/-
**C0 (orthogonality).**  Finite orthogonality of additive characters on
    `ZMod L`: the average of `e(h·n/L) = exp(2πi h n / L)` over `h` is `1` if
    `L ∣ n` and `0` otherwise.
-/
theorem fourier_orthogonality (L : ℕ) (hL : 0 < L) (n : ℤ) :
    (∑ h ∈ Finset.range L,
        Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (n : ℂ) / (L : ℂ)))
      = if (L : ℤ) ∣ n then (L : ℂ) else 0 := by
  split_ifs with h;
  · obtain ⟨ k, rfl ⟩ := h; norm_num; ring;
    exact Eq.trans ( Finset.sum_congr rfl fun _ _ => by rw [ Complex.exp_eq_one_iff ] ; use k * ‹ℕ›; simpa [ hL.ne', mul_assoc, mul_comm, mul_left_comm ] ) ( by norm_num );
  · -- Let ζ = exp(2 * π * i * n / L). Then each summand exp(2 * π * i * h * n / L) = ζ^h.
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * n / L)
    have hζ : ∀ h : ℕ, Complex.exp (2 * Real.pi * Complex.I * h * n / L) = ζ ^ h := by
      exact fun x => by rw [ ← Complex.exp_nat_mul ] ; ring;
    rw [ Finset.sum_congr rfl fun _ _ => hζ _, geom_sum_eq ];
    · rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff.mpr ⟨ n, by ring_nf; norm_num [ hL.ne' ] ⟩ ] ; norm_num;
    · rw [ Ne.eq_def, Complex.exp_eq_one_iff ];
      field_simp;
      exact fun ⟨ k, hk ⟩ => h <| by exact ⟨ k, by rw [ ← @Int.cast_inj ℂ ] ; push_cast; rw [ div_eq_iff ( Nat.cast_ne_zero.mpr hL.ne' ) ] at hk; linear_combination hk ⟩ ;

/-! ## C5. Arc separation (positivity core) -/

/-- **C5 positivity core (note 35 C5).**  If `L·W` equals a real main term plus a
    minor complex remainder whose norm is strictly beaten by the main term, then
    `W > 0`.  This is the arc-separation step of the circle method, isolated from
    the specific main-arc / minor-arc estimates (which enter only through the
    hypotheses `hmainpos`, `hminor`, `hbeat`).  Pure analysis; no dependence on
    Phase G. -/
theorem positivity_from_arcs (L : ℕ) (hL : 0 < L) (W main minorBound : ℝ)
    (minorSum : ℂ)
    (hident : (L : ℂ) * (W : ℂ) = (main : ℂ) + minorSum)
    (hmainpos : 0 < main) (hminor : ‖minorSum‖ ≤ minorBound)
    (hbeat : minorBound < main) :
    0 < W := by
  have hre : (L : ℝ) * W = main + minorSum.re := by
    have h := congrArg Complex.re hident
    simpa using h
  have hbound : -minorBound ≤ minorSum.re := by
    have h1 : |minorSum.re| ≤ ‖minorSum‖ := Complex.abs_re_le_norm minorSum
    have h2 : |minorSum.re| ≤ minorBound := le_trans h1 hminor
    linarith [(abs_le.mp h2).1]
  have hpos : 0 < (L : ℝ) * W := by rw [hre]; linarith
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  exact (mul_pos_iff_of_pos_left hLpos).mp hpos

end CircleMethod

/-! ## C1–C4 (analytic heart) + C5 assembly

The analytic content of the circle method — edge construction (C1; note 35 C1,
needs the block density input), the pointwise Fourier bound (C2), the main-arc
Taylor estimate (C3), and the minor-arc bound via the Phase-G global control
(C4) — is bundled into the following single existence statement.  Its proof is
the subject of `GlobalControl.lean` (note 34) together with `BernoulliFourier`.
-/

namespace CircleMethod

/-- **C1–C4 (analytic heart).**  For every squarefree `b > 0` and finite
    obstruction set `T`, there is a finite edge set `E` of squarefree semiprimes
    avoiding `T`, together with Bernoulli weights `θ`, such that the deterministic
    weighted count `Wcount E θ b` is strictly positive.

    This bundles the edge construction (note 35 C1), the pointwise Fourier bound
    (C2), the main-arc lower bound (C3) and the minor-arc upper bound (C4 via
    Phase-G global control).  It is the sole analytic residual of the circle
    method. -/
theorem exists_positive_weighted_construction
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    ∃ (E : Finset ℕ) (theta : ℕ → ℝ),
      (∀ e ∈ E, IsSemiprime e) ∧ (∀ e ∈ E, e ∉ T) ∧
      0 < Wcount E theta b := by
  sorry

/-- **Phase-C route closure.**  Reduces the analytic heart
    `exists_positive_weighted_construction` to: a concrete construction `(E, θ)`
    of semiprime edges avoiding `T`, together with the Fourier identity
    `L·Wcount = main + minorSum` and the arc separation `‖minorSum‖ < main`.
    The positivity then follows from `positivity_from_arcs`.  This isolates the
    remaining Phase-C content to the edge construction (C1), the Fourier identity
    (C0), and the main/minor arc estimates (C3/C4 via G7). -/
theorem exists_pos_construction_of_arcs (T : Finset ℕ) (b : ℕ)
    (E : Finset ℕ) (theta : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (main minorBound : ℝ) (minorSum : ℂ)
    (hsemi : ∀ e ∈ E, IsSemiprime e) (havoid : ∀ e ∈ E, e ∉ T)
    (hident : (L : ℂ) * (Wcount E theta b : ℂ) = (main : ℂ) + minorSum)
    (hmainpos : 0 < main) (hminor : ‖minorSum‖ ≤ minorBound) (hbeat : minorBound < main) :
    ∃ (E' : Finset ℕ) (theta' : ℕ → ℝ),
      (∀ e ∈ E', IsSemiprime e) ∧ (∀ e ∈ E', e ∉ T) ∧
      0 < Wcount E' theta' b :=
  ⟨E, theta, hsemi, havoid,
    positivity_from_arcs L hL (Wcount E theta b) main minorBound minorSum
      hident hmainpos hminor hbeat⟩

/-- **C5 (positivity ⟹ representation).**  Assembles the analytic positivity
    `exists_positive_weighted_construction` with the extraction principle
    `Wcount_pos_imp_repr` to produce an Egyptian semiprime representation of
    `1/b` avoiding `T`. -/
theorem circle_method_positivity
    (T : Finset ℕ) (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / (b : ℚ)) := by
  obtain ⟨E, theta, hsemi, hdisj, hW⟩ :=
    exists_positive_weighted_construction T b hb hbsf
  exact Wcount_pos_imp_repr T E theta b hsemi hdisj hW

end CircleMethod

end