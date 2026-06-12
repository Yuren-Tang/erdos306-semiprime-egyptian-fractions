/-
# SBEE Dispersion: Lemma D, the dispersion corollary, and Theorem C

This file formalizes the **P1 crux** of the SBEE single-block counting proof,
following the paper proofs in `29 SBEE Master …md` (§2, Lemma D) and
`30 Theorem C …md` (§1, the dispersion corollary and the fingerprint count).

## Status overview (the deliverable is the pattern of sorries)

* `lemmaD_fiber`, `lemmaD` — **Lemma D, fully proved, no sorry.**
  This is the deterministic dispersion engine: a residue class mod `q` meets the
  interval `[X,2X]` in `≤ 2` points, and a nonzero `u` with `|u| < X ≤ q` is
  invertible mod the prime `q`.
* `dispersion_residue_count`, `dispersion_energy_bound` — the dispersion corollary
  of `30 §1`. Stated; proof isolated as `sorry` (requires the fractional-norm
  `‖·‖` / modular-inverse layer, see docstrings).
* `fingerprint_count` — Theorem C. Stated; isolated as `sorry` (the
  cold-rigidity + entropy bookkeeping, see docstring).
-/
import Mathlib
import RequestProject.BlockCRTEnergy

open Finset

namespace SBEEDispersion

/-! ## Lemma D (deterministic dispersion) — `29 §2` -/

/-- The counting set of **Lemma D**: pairs `(u, p)` with `u ∈ [-U, U]` (integer),
    `p ∈ [X, 2X]` prime, and `u·p ≡ w (mod q)`. -/
def lemmaD_set (X q U : ℕ) (w : ℤ) : Finset (ℤ × ℕ) :=
  ((Finset.Icc (-(U:ℤ)) (U:ℤ)) ×ˢ (Finset.Icc X (2*X))).filter
    (fun up => Nat.Prime up.2 ∧ (q:ℤ) ∣ (up.1 * (up.2 : ℤ) - w))

/-- **Per-fiber bound.** For a fixed integer `u` (`q` prime, `q ∤ w`), there are at
    most `2` primes `p ∈ [X,2X]` with `u·p ≡ w (mod q)`.

    Reason: if the fiber is nonempty then `q ∤ u` (else `q ∣ w`), so `u` is
    invertible mod the prime `q`; the congruence pins `p` to one residue class
    mod `q`, and `[X,2X]` (length `X ≤ q`) holds `≤ 2` of any class.

    **Verification finding.** The paper requires `|u| < X ≤ q` to get `u`
    invertible.  This is *unnecessary*: `q ∤ u` follows directly from `q ∤ w`
    (if `q ∣ u` then `q ∣ u·p`, so `q ∣ w`), for any `u`.  Hence the hypothesis
    `U < X` of Lemma D is not needed for the fiber bound. -/
lemma lemmaD_fiber (X q : ℕ) (hq : q.Prime) (hXq : X ≤ q) (w : ℤ)
    (hw : ¬ (q:ℤ) ∣ w) (u : ℤ) :
    ((Finset.Icc X (2*X)).filter
      (fun p => Nat.Prime p ∧ (q:ℤ) ∣ (u * (p:ℤ) - w))).card ≤ 2 := by
  by_contra h_contra;
  -- Obtain three distinct elements a, b, c from the set.
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℕ, a ∈ Finset.Icc X (2 * X) ∧ b ∈ Finset.Icc X (2 * X) ∧ c ∈ Finset.Icc X (2 * X) ∧ Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧ (q : ℤ) ∣ (u * a - w) ∧ (q : ℤ) ∣ (u * b - w) ∧ (q : ℤ) ∣ (u * c - w) ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    obtain ⟨ s, hs ⟩ := Finset.two_lt_card.mp ( lt_of_not_ge h_contra );
    rcases hs with ⟨ hs₁, b, hb₁, c, hc₁, hab, hac, hbc ⟩ ; use s, b, c; aesop;
  -- Since $q$ is prime and does not divide $u$, it must divide $(a - b)$, $(a - c)$, and $(b - c)$.
  have h_div : (q : ℤ) ∣ (a - b) ∧ (q : ℤ) ∣ (a - c) ∧ (q : ℤ) ∣ (b - c) := by
    haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_iff_eq_add ] ;
    grind +splitImp;
  -- Since $q$ divides $(a - b)$, $(a - c)$, and $(b - c)$, and $a$, $b$, and $c$ are distinct primes in the interval $[X, 2X]$, it follows that $|a - b| \geq q$, $|a - c| \geq q$, and $|b - c| \geq q$.
  have h_abs : |(a : ℤ) - b| ≥ q ∧ |(a : ℤ) - c| ≥ q ∧ |(b : ℤ) - c| ≥ q := by
    exact ⟨ Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( mod_cast habc.2.2.2.2.2.2.1 ) ) ) ( by simpa using h_div.1 ), Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( mod_cast habc.2.2.2.2.2.2.2.1 ) ) ) ( by simpa using h_div.2.1 ), Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( mod_cast habc.2.2.2.2.2.2.2.2 ) ) ) ( by simpa using h_div.2.2 ) ⟩;
  grind +suggestions

/-- **Lemma D** (`29 §2`). For prime `q` with `X ≤ q`, integer `w` with `q ∤ w`,
    and `U < X`:
    `#{(u,p) : p ∈ [X,2X] prime, |u| ≤ U, u·p ≡ w (mod q)} ≤ 2·(2U+1)`.

    The hypothesis `U < X` is kept to match the paper's statement (`29 §2`), but
    the proof does not use it — see the finding noted on `lemmaD_fiber`. -/
theorem lemmaD (X q U : ℕ) (hq : q.Prime) (hXq : X ≤ q) (_hUX : U < X)
    (w : ℤ) (hw : ¬ (q:ℤ) ∣ w) :
    (lemmaD_set X q U w).card ≤ 2 * (2 * U + 1) := by
  have key : ∀ u ∈ Finset.Icc (-(U:ℤ)) U, (Finset.filter (fun up => up.1 = u) (lemmaD_set X q U w)).card ≤ 2 := by
    intro u _hu;
    -- The fiber {x ∈ S : x.1 = u} is in bijection with the p-fiber {p ∈ Icc X (2X) : p.Prime ∧ (q:ℤ) ∣ (u·p - w)} via p ↦ (u,p).
    have h_bij : Finset.filter (fun up => up.1 = u) (lemmaD_set X q U w) ⊆ Finset.image (fun p : ℕ => (u, p)) (Finset.filter (fun p => Nat.Prime p ∧ (q:ℤ) ∣ (u * (p : ℤ) - w)) (Finset.Icc X (2 * X))) := by
      grind +locals;
    refine le_trans ( Finset.card_le_card h_bij ) ?_;
    rw [ Finset.card_image_of_injective _ fun x y hxy => by injection hxy ];
    exact lemmaD_fiber X q hq hXq w hw u;
  convert Finset.sum_le_sum key using 1;
  · rw [ ← Finset.card_eq_sum_card_fiberwise ];
    exact fun x hx => Finset.mem_Icc.mpr <| Finset.mem_Icc.mp <| Finset.mem_product.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1;
  · norm_num [ two_mul, add_assoc ];
    grind

/-! ## The dispersion corollary — `30 §1`, "Dispersion (Lemma D form)"

For `q ∉ F`, integer `E` with `q ∤ E`, `0 < |E| < q`, and `δ = |F|/(32X)`:
`#{p ∈ F : ‖E·q̄/p‖ ≤ δ} ≤ 2·(4δX+1) ≤ |F|/2`, hence
`∑_{p ∈ F} ‖E·q̄/p‖² ≥ |F|³/(2^11 X²) =: G_F`.

These statements require the fractional-norm `‖·‖` on `ℝ/ℤ` together with the
modular inverse `q̄` mod `p`; they are stated abstractly here with a real-valued
"reciprocal phase" function `phase` and isolated as `sorry`.  The mathematical
content reduces to `lemmaD` via `p ∣ E - u·q`. -/

/-- Reciprocal phase `‖E·q̄/p‖ ∈ [0, 1/2]`: the distance to the nearest integer of
    `E · q̄ / p`, where `q̄ = (q : ZMod p)⁻¹` is the modular inverse of `q` mod `p`.
    This is the faithful fractional-norm used in `30 §1`. -/
noncomputable def phase (E : ℤ) (q p : ℕ) : ℝ :=
  let x : ℝ := (E : ℝ) * (((q : ZMod p)⁻¹).val : ℝ) / (p : ℝ)
  |x - (round x : ℝ)|

/-- `phase` is nonnegative. -/
lemma phase_nonneg (E : ℤ) (q p : ℕ) : 0 ≤ phase E q p := by
  unfold phase; positivity

/-- **Dispersion residue count** (`30 §1`).  Number of fingerprint primes whose
    reciprocal phase is `≤ δ` is at most `2(4δX+1)`, and with `δ = |F|/(32X)`
    this is `≤ |F|/2`.

    **Status**: `sorry`.  Gap: the reduction `‖E·q̄/p‖ ≤ δ ⟹ p ∣ E - u·q` with
    `|u| ≤ 2δX` and the "≤ 2 prime factors of a nonzero integer `< X³`" step,
    feeding into `lemmaD`.  Needs the `phase`/modular-inverse layer. -/
theorem dispersion_residue_count
    (X : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (q : ℕ) (hq : q.Prime) (hqF : q ∉ F) (E : ℤ) (hqE : ¬ (q:ℤ) ∣ E)
    (hE0 : 0 < |E|) (hEq : |E| < (q:ℤ)) :
    ((F.filter (fun p => phase E q p ≤ (F.card : ℝ) / (32 * X))).card : ℝ)
      ≤ (F.card : ℝ) / 2 := by
  sorry

/-
**Dispersion energy bound** (`30 §1`):
    `∑_{p ∈ F} ‖E·q̄/p‖² ≥ |F|³/(2^11 X²) =: G_F`.

    **Status**: `sorry`.  Follows from `dispersion_residue_count`: at least half
    the primes have phase `> δ = |F|/(32X)`, each contributing `> δ²`.
-/
theorem dispersion_energy_bound
    (X : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (q : ℕ) (hq : q.Prime) (hqF : q ∉ F) (E : ℤ) (hqE : ¬ (q:ℤ) ∣ E)
    (hE0 : 0 < |E|) (hEq : |E| < (q:ℤ)) :
    (F.card : ℝ)^3 / (2^11 * (X:ℝ)^2)
      ≤ ∑ p ∈ F, (phase E q p)^2 := by
  -- By `dispersion_residue_count`, there are at least `F.card / 2` primes `p` in `F` such that `phase E q p > |F| / (32 * X)`.
  have h_residue_count : ((F.filter (fun p => phase E q p > (F.card : ℝ) / (32 * X))).card : ℝ) ≥ (F.card : ℝ) / 2 := by
    have h_residue_count : ((F.filter (fun p => phase E q p ≤ (F.card : ℝ) / (32 * X))).card : ℝ) ≤ (F.card : ℝ) / 2 := by
      convert dispersion_residue_count X F ‹_› q hq hqF E hqE ( by positivity ) ( by linarith ) using 1;
    have h_residue_count : ((F.filter (fun p => phase E q p > (F.card : ℝ) / (32 * X))).card : ℝ) + ((F.filter (fun p => phase E q p ≤ (F.card : ℝ) / (32 * X))).card : ℝ) = (F.card : ℝ) := by
      rw_mod_cast [ Finset.card_filter, Finset.card_filter ];
      simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones F ▸ by congr; ext; split_ifs <;> linarith;
    linarith;
  -- Let `δ := |F| / (32 * X)`. Then each prime `p` in `F` with `phase E q p > δ` contributes at least `δ^2` to the sum.
  set δ := (F.card : ℝ) / (32 * X)
  have h_contribution : ∑ p ∈ F.filter (fun p => phase E q p > δ), (phase E q p) ^ 2 ≥ (F.filter (fun p => phase E q p > δ)).card * δ ^ 2 := by
    exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( by positivity ) ( Finset.mem_filter.mp hx |>.2.le ) 2 );
  refine le_trans ?_ ( h_contribution.trans <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _ );
  convert mul_le_mul_of_nonneg_right h_residue_count ( sq_nonneg δ ) using 1 ; ring

/-! ## Theorem C (fingerprint count) — `30 §1` -/

/-- **Theorem C** (`30 §1`).  For every `ε ∈ (0,1)` there are `Cε, X₀` such that
    for `X ≥ X₀`, any prime block `P ⊆ [X,2X]`, and any
    `R ≥ R_C := Cε · X^{2/3} · (log X)^{4/3}`, the full level set satisfies
    `#{a : Q_P(a) ≤ R} ≤ N · exp(ε R)` (`N = |P|`).

    The argument: fix the fingerprint `F` (the `⌈εR/(2 log 2X)⌉` smallest primes);
    cold vertices (`t_q < T := G_F/7`) have a *unique* consistent residue (cold
    rigidity, via `dispersion_energy_bound`), so carry zero entropy; the entropy
    is `|F| log 2X + (hot count)·O(log X) ≤ εR`.

    **Status**: `sorry`.  This bundles (i) the phase identity slack
    `|H| ≥ pq‖·‖ − q`, (ii) cold rigidity (uniqueness of the cold residue, using
    the *un-recentered* centered integer representative — see the "Verification
    note" in `30 §1`), and (iii) the entropy/counting bookkeeping `3h log X ≤ εR/2
    ⟺ R ≥ R_C`.  These are the analytic estimates flagged for the verifier. -/
theorem fingerprint_count
    (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ (Ceps X0 : ℝ), 0 < Ceps ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (R : ℝ), Ceps * (X:ℝ)^((2:ℝ)/3) * (Real.log X)^((4:ℝ)/3) ≤ R →
            ((Finset.univ.filter (fun a : BlockAssignment P => QP P a ≤ R)).card : ℝ)
              ≤ (P.card : ℝ) * Real.exp (eps * R) := by
  sorry

end SBEEDispersion