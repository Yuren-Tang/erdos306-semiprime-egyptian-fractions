/-
# SBEE Forcing: Theorem A (dominant), Lemma E (cross-label energy), Theorem B

This file formalizes **P2** of the SBEE single-block counting proof, following
`29 SBEE Master …md` §3 (Theorem A), §5 (Lemma E), §6 (Theorem B).

It is stated against the faithful CRT energy encoding (`QP`, `sigmaP`,
`BlockAssignment`) of `BlockCRTEnergy.lean`.

## Status overview (the deliverable is the pattern of sorries)

* `IsDominant` — dominance predicate (a label class covers `≥ (1-ρ)·N` primes).
* `theorem_A_dominant_count` — Theorem A.  `sorry`: combines label uniqueness
  (A1), label range (A2), per-exception energy via Lemma D (A3), the count (A4).
* `lemma_E_cross_label_energy` — Lemma E.  `sorry`: the cross-label energy lower
  bound via Lemma D.
* `theorem_B_nondominant_forcing` — Theorem B.  `sorry`: the covering construction
  (`29 §4`) + Lemma E + mass accounting force `R ≫ X/log³X`.

All four reduce, mathematically, to `SBEEDispersion.lemmaD` (proved) plus the
covering/entropy bookkeeping; the gaps are exactly the analytic estimates the task
asks us to surface.
-/
import Mathlib
import RequestProject.BlockCRTEnergy
import RequestProject.SBEEDispersion

open Finset

namespace SBEEForcing

open scoped Classical

/-! ## Dominance -/

/-- `a` is **`m`-dominant** (parameter `ρ`) if the residue label `m` agrees with
    `a_p (mod p)` on at least a `(1-ρ)` fraction of the primes `p ∈ P`, with
    `|m| ≤ X²/2` (so that the in-class CRT representatives equal `m` exactly).
    (`29 §3`.) -/
def IsDominant (X : ℕ) (P : Finset ℕ) (a : BlockAssignment P) (ρ : ℝ) : Prop :=
  ∃ m : ℤ, |m| ≤ (X:ℤ)^2 / 2 ∧
    (1 - ρ) * (P.card : ℝ) ≤
      ((P.attach.filter (fun p => a p = ((m : ℤ) : ZMod (p:ℕ)))).card : ℝ)

/-! ## Theorem A — the dominant case (`29 §3`) -/

/-- **Theorem A** (`29 §3`).  For `ε > 0`, `ρ ∈ (0, 1/4]`, and `X` large, the
    number of *dominant* low-energy assignments is at most
    `exp(ε R) · (1 + (10/(1-ρ))·√R/σ_P)`.

    Proof ingredients (all in `29 §3`): (A1) the dominant label is unique; (A2) the
    label range `|m| ≤ (5/(1-ρ))·√R/σ_P`; (A3) each exception carries energy
    `≥ N³/2¹⁵X²` via `SBEEDispersion.lemmaD`; (A4) the exception entropy
    `3e log X ≤ εR`.

    **Status**: `sorry` — the entropy bookkeeping (A4) and the per-exception energy
    accounting (A3) over the concrete CRT energy `QP`. -/
theorem theorem_A_dominant_count
    (eps : ℝ) (hε : 0 < eps) (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ X0 : ℝ, 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R →
            ((Finset.univ.filter
                (fun a : BlockAssignment P => QP P a ≤ R ∧ IsDominant X P a ρ)).card : ℝ)
              ≤ Real.exp (eps * R) *
                  (1 + (10/(1-ρ)) * Real.sqrt R / sigmaP P) := by
  sorry

/-! ## Lemma E — cross-label energy (`29 §5`) -/

/-- **Lemma E** (`29 §5`).  For distinct integer labels `n ≠ n'` with
    `|n|, |n'| ≤ B ≤ X²/4`, and disjoint prime sets `C, C' ⊆ [X,2X]` on which `a`
    has constant residues `n`, `n'` respectively, with `|C| ≥ 32(B/X+1)` and
    `|C'| ≥ 8`:
    `∑_{p∈C, q∈C'} (H_{pq}/pq)² ≥ c·|C|³|C'|/X²` for an absolute `c > 0`.

    Proof (`29 §5`): reduce to `SBEEDispersion.lemmaD` with `w = n'-n`; at most `2`
    primes divide `d = n'-n`; for the rest, `≤ 8δX+4B/X+2` cross pairs are close,
    so `≥ |C||C'|/2` pairs carry energy `≥ δ²`.

    **Status**: `sorry` — the choice of `δ`, the discard of `≤2` prime divisors,
    and the energy accounting over the concrete CRT representatives. -/
theorem lemma_E_cross_label_energy :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
        (a : BlockAssignment P) (n n' : ℤ) (B : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ B → |(n':ℝ)| ≤ B → B ≤ (X:ℝ)^2/4 →
        ∀ (C C' : Finset P),
          Disjoint C C' →
          (32 * (B/X + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, a p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', a q = ((n' : ℤ) : ZMod (q:ℕ))) →
          c * (C.card : ℝ)^3 * C'.card / (X:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (a p) (a q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2 := by
  sorry

/-! ## Theorem B — non-dominant forcing (`29 §6`) -/

/-- **Theorem B** (`29 §6`).  For `ρ ∈ (0,1/4]` and `X` large: any low-energy
    assignment that is **not** dominant forces `R ≫ X/log³X`.  Concretely there is
    `c₂ > 0` with: if `QP P a ≤ R` and `a` is not `ρ`-dominant then
    `R ≥ c₂ · X / (Real.log X)^3`.

    Proof (`29 §6`): the covering construction (`29 §4`) produces `≥ 2` substantial
    classes; Lemma E across them, with the mass accounting (`M₂ ≥ ρN/2`), forces
    `R² ≫ N⁴/(X²log²X)`, i.e. `R ≫ N²/(X log X) ≫ X/log³X`.

    **Status**: `sorry` — the covering bookkeeping and tiny-mass accounting
    (the soft spot flagged in the task), on top of `lemma_E_cross_label_energy`. -/
theorem theorem_B_nondominant_forcing
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (a : BlockAssignment P) (R : ℝ),
          QP P a ≤ R → ¬ IsDominant X P a ρ →
            c2 * (X:ℝ) / (Real.log X)^3 ≤ R := by
  sorry

/-! ## Corollary — SBEE below the window (`29 §7`)

Combining Theorem B (every `R ≤ c'X/log³X` low-energy assignment is dominant) with
Theorem A gives the level-set bound for all `R ≤ c'X/log³X`.  Stated as
`corollary_SBEE_below_window`; `sorry` — it is the direct A+B combination. -/

/-
**Corollary** (`29 §7`).  For `ε > 0` there are `c', X₀` so that for `X ≥ X₀`
    and all `R ≤ c'·X/log³X`,
    `#{a : QP P a ≤ R} ≤ exp(εR)·(1 + 20√R/σ_P)`.

    **Status**: `sorry` — direct combination of `theorem_B_nondominant_forcing`
    (all such assignments are dominant) and `theorem_A_dominant_count`.
-/
theorem corollary_SBEE_below_window
    (eps : ℝ) (hε : 0 < eps) (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (cp X0 : ℝ), 0 < cp ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (R : ℝ), 1 ≤ R → R ≤ cp * (X:ℝ) / (Real.log X)^3 →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ Real.exp (eps * R) * (1 + 20 * Real.sqrt R / sigmaP P) := by
  obtain ⟨X0A, hX0A, HA⟩ := theorem_A_dominant_count eps hε ρ hρ hρ4
  obtain ⟨c2, X0B, hc2, hX0B, HB⟩ := theorem_B_nondominant_forcing ρ hρ hρ4
  use c2 / 2, max X0A X0B;
  refine' ⟨ by positivity, by positivity, fun X hX P hP hN R hR₁ hR₂ => _ ⟩;
  intro hR₃
  have h_dom : ∀ a : BlockAssignment P, QP P a ≤ hR₁ → IsDominant X P a ρ := by
    intro a ha;
    contrapose! HB;
    refine' ⟨ X, _, P, hP, hN, R, a, hR₁, ha, HB, _ ⟩;
    · exact le_trans ( le_max_right _ _ ) hX;
    · grind;
  refine' le_trans _ ( le_trans ( HA X ( le_trans ( le_max_left _ _ ) hX ) P hN R hR₁ hR₂ ) _ );
  · exact_mod_cast Finset.card_le_card fun x hx => by aesop;
  · gcongr;
    · exact Real.sqrt_nonneg _;
    · rw [ div_le_iff₀ ] <;> linarith

end SBEEForcing