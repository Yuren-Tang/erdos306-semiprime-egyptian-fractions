/-
# SBEE Dispersion: Lemma D, the dispersion corollary, and Theorem C

This file formalizes the **P1 crux** of the SBEE single-block counting proof,
following the paper proofs in `29 SBEE Master …md` (§2, Lemma D) and
`30 Theorem C …md` (§1, the dispersion corollary and the fingerprint count).

## Status overview

* `lemmaD_fiber`, `lemmaD` — **Lemma D, fully proved, no sorry.**
  This is the deterministic dispersion engine: a residue class mod `q` meets the
  interval `[X,2X]` in `≤ 2` points, and a nonzero `u` with `|u| < X ≤ q` is
  invertible mod the prime `q`.
* `dispersion_residue_count`, `dispersion_energy_bound` — the dispersion corollary
  of `30 §1`. **Fully proved, no sorry.**
* Theorem C itself (`fingerprint_count`) is assembled in
  `RequestProject/SBEEFingerprint.lean`, where the cold-rigidity and entropy
  layers it depends on are available; this file is its dispersion foundation and
  is now entirely sorry-free.
-/
import RequestProject.BlockCRTEnergy
import RequestProject.Core.SmallBallEnergy
import RequestProject.Core.ShortIntervalCongruence
import RequestProject.Core.UnitCircleResidue
import Mathlib.Analysis.Normed.Group.AddCircle

open Finset

namespace SBEEDispersion

/-! ## Lemma D (deterministic dispersion) — `29 §2` -/

/-- The counting set of **Lemma D**: pairs `(u, p)` with `u ∈ [-U, U]` (integer),
    `p ∈ [X, 2X]` prime, and `u·p ≡ w (mod q)`. -/
noncomputable def lemmaD_set (X q U : ℕ) (w : ℤ) : Finset (ℤ × ℕ) :=
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
  apply RequestProject.card_le_two_of_dvd_sub_of_mem_Icc X (2 * X) q
  · omega
  · intro p hp
    exact (Finset.mem_filter.mp hp).1
  · intro p hp p' hp'
    have hpdata := (Finset.mem_filter.mp hp).2
    have hpdata' := (Finset.mem_filter.mp hp').2
    have hu : ¬ (q : ℤ) ∣ u := by
      intro hqu
      apply hw
      exact by simpa using dvd_sub (hqu.mul_right p) hpdata.2
    have hmul : (q : ℤ) ∣ u * ((p : ℤ) - p') := by
      rw [show u * ((p : ℤ) - p') = (u * p - w) - (u * p' - w) by ring]
      exact dvd_sub hpdata.2 hpdata'.2
    exact (Int.Prime.dvd_mul' hq hmul).resolve_left hu

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
  · rfl
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
  ‖(((E : ℝ) * (((q : ZMod p)⁻¹).val : ℝ) / (p : ℝ) : ℝ) : UnitAddCircle)‖

/-- `phase` is nonnegative. -/
lemma phase_nonneg (E : ℤ) (q p : ℕ) : 0 ≤ phase E q p := by
  exact norm_nonneg _

/-
The reciprocal phase is even in `E`: `‖(−E)q̄/p‖ = ‖E q̄/p‖`.  (`round` is a
    nearest-integer map, so the distance to it is symmetric under negation.)
-/
lemma phase_neg (E : ℤ) (q p : ℕ) : phase (-E) q p = phase E q p := by
  unfold phase
  rw [show ((-E : ℤ) : ℝ) * ((q : ZMod p)⁻¹).val / p =
      -((E : ℝ) * ((q : ZMod p)⁻¹).val / p) by push_cast; ring]
  simp

/-
**Fractional-norm triangle inequality** for the reciprocal phase:
    `‖(A−B)q̄/p‖ ≤ ‖A q̄/p‖ + ‖B q̄/p‖`.

    This is the analytic mechanism behind **cold rigidity** (`30 §1`): with
    `A = a_p − w̃`, `B = a_p − w̃'`, the difference `A − B = w̃' − w̃ = E`, so
    `‖E q̄/p‖ ≤ ‖A q̄/p‖ + ‖B q̄/p‖`; summing the squares and applying
    `dispersion_energy_bound` to `E` yields the two-cold-residue contradiction.

    Proof: with `x_E := E·q̄/p`, linearity gives `x_{A−B} = x_A − x_B`.  Writing
    `k := round x_A − round x_B ∈ ℤ`, the nearest-integer minimality `round_le`
    gives `|x_{A−B} − round x_{A−B}| ≤ |x_{A−B} − k| = |(x_A − round x_A) −
    (x_B − round x_B)| ≤ |x_A − round x_A| + |x_B − round x_B|`.
-/
lemma phase_sub_le (A B : ℤ) (q p : ℕ) :
    phase (A - B) q p ≤ phase A q p + phase B q p := by
  simpa [phase, Int.cast_sub, sub_mul, sub_div] using
    norm_sub_le
      ((((A : ℝ) * (((q : ZMod p)⁻¹).val : ℝ) / (p : ℝ) : ℝ) : UnitAddCircle))
      ((((B : ℝ) * (((q : ZMod p)⁻¹).val : ℝ) / (p : ℝ) : ℝ) : UnitAddCircle))

/-
**`card_prime_factors_dyadic_le_two`** (factored out of `lemmaD_fiber`'s
    argument, per note `31 §4`).  A nonzero integer `n` with `|n| < X³` has at most
    `2` prime factors in the dyadic window `[X, 2X]`.

    Reason: three *distinct* primes `a, b, c ∈ [X, 2X]` dividing `n` are pairwise
    coprime, so their product `a·b·c` divides `n`; hence
    `|n| ≥ a·b·c ≥ X³`, contradicting `|n| < X³`.
-/
lemma card_prime_factors_dyadic_le_two (X : ℕ) (n : ℤ) (hn : n ≠ 0)
    (hX : |n| < (X:ℤ)^3) :
    ((Finset.Icc X (2*X)).filter (fun p => Nat.Prime p ∧ (p:ℤ) ∣ n)).card ≤ 2 := by
  by_contra h_contra;
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ : ∃ a b c : ℕ, a ∈ Finset.Icc X (2 * X) ∧ b ∈ Finset.Icc X (2 * X) ∧ c ∈ Finset.Icc X (2 * X) ∧ Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧ a ∣ Int.natAbs n ∧ b ∣ Int.natAbs n ∧ c ∣ Int.natAbs n ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    obtain ⟨ s, hs ⟩ := Finset.two_lt_card.mp ( by linarith ) ; simp_all +decide ;
    rcases hs with ⟨ ⟨ ⟨ hs₁, hs₂ ⟩, hs₃, hs₄ ⟩, b, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃, hb₄ ⟩, c, ⟨ ⟨ hc₁, hc₂ ⟩, hc₃, hc₄ ⟩, hbc ⟩ ; use s, ⟨ hs₁, hs₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, c, ⟨ hc₁, hc₂ ⟩ ; simp_all +decide [ ← Int.natCast_dvd_natCast ] ;
  -- Since $a$, $b$, and $c$ are pairwise coprime primes dividing $n$, their product $a \cdot b \cdot c$ also divides $n$.
  have h_prod_div : (a * b * c : ℤ) ∣ n.natAbs := by
    norm_cast;
    apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
    · simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_primes ];
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by have := Nat.coprime_primes habc.1 habc.2.1; aesop ) habc.2.2.2.1 habc.2.2.2.2.1;
    · tauto;
  have h_prod_ge : (a * b * c : ℤ) ≥ X^3 := by
    norm_cast;
    exact le_trans ( by ring_nf; norm_num ) ( Nat.mul_le_mul ( Nat.mul_le_mul ( Finset.mem_Icc.mp ha |>.1 ) ( Finset.mem_Icc.mp hb |>.1 ) ) ( Finset.mem_Icc.mp hc |>.1 ) );
  exact not_lt_of_ge ( Int.le_of_dvd ( by positivity ) h_prod_div ) ( by simpa [ abs_mul ] using hX.trans_le h_prod_ge )

/-
**Phase → divisibility witness** (the bridge of `30 §1` / `31 §4`).  If the
    reciprocal phase `‖E·q̄/p‖ = phase E q p` is `≤ δ`, then there is an integer
    `s` with `|s| ≤ 2δX` and `p ∣ E − s·q`.

    Construction: with `q̄ = (q : ZMod p)⁻¹.val` and `r = round (E·q̄/p)`, set
    `s = E·q̄ − r·p`.  Then `|s| = p·phase ≤ p·δ ≤ 2X·δ`, and modulo `p`,
    `s ≡ E·q̄`, so `s·q ≡ E·(q̄·q) ≡ E` (using `q·q̄ ≡ 1 (mod p)`, valid as
    `p ∤ q` for distinct primes `p ≠ q`); hence `p ∣ E − s·q`.
-/
lemma phase_dvd_witness (X p q : ℕ) (hp : p.Prime) (hp2X : p ≤ 2*X)
    (hq : q.Prime) (hpq : p ≠ q) (E : ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : phase E q p ≤ δ) :
    ∃ s : ℤ, |(s:ℝ)| ≤ 2*δ*(X:ℝ) ∧ (p:ℤ) ∣ (E - s*(q:ℤ)) := by
  obtain ⟨s, hsabs, hsmod⟩ :=
    RequestProject.exists_centered_residue_of_unitCircle_norm_le
      (E * ((q : ZMod p)⁻¹).val) p hp.pos δ (by simpa [phase] using hδ)
  refine ⟨s, ?_, ?_⟩
  · have hp2XR : (p : ℝ) ≤ 2 * X := by exact_mod_cast hp2X
    exact hsabs.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hp2XR hδ0])
  · haveI := Fact.mk hp
    haveI := Fact.mk hq
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul]
    have hs0 : ((E * ((q : ZMod p)⁻¹).val - s : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (E * ((q : ZMod p)⁻¹).val - s) p).2 hsmod
    have hs : (s : ZMod p) = E * (q : ZMod p)⁻¹ := by
      push_cast at hs0
      rw [ZMod.natCast_zmod_val] at hs0
      exact (sub_eq_zero.mp hs0).symm
    have hqne : (q : ZMod p) ≠ 0 := by
      rw [Ne.eq_def, ZMod.natCast_eq_zero_iff]
      exact fun h => hpq <| (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    rw [hs]
    simp [hqne]

/-
**Dispersion residue count** (`30 §1`).  Number of fingerprint primes whose
    reciprocal phase is `≤ δ := |F|/(32X)` is at most `2(4δX+1) = |F|/4 + 2`,
    which is `≤ |F|/2` once `|F| ≥ 8`.

    **Faithfulness note.**  Two hypotheses present in the paper statement
    (`30 §1`, `31 §4`) were missing from the V1 Lean statement and are restored
    here, as the conclusion is *false* without them:
    * `hq2X : q ≤ 2*X` — `q` is a block vertex `q ∈ P ⊆ [X,2X]`; the proof bounds
      `|E − s·q| ≤ |E| + |s|·q < X³` and needs `q ≤ 2X` (e.g. `F = {2}`,
      `q = 5`, `E = 2` gives `phase = 0` for the lone prime, breaking the bound).
    * `hFcard : 8 ≤ F.card` — note `31`'s `|F| ≥ 8`; needed for
      `|F|/4 + 2 ≤ |F|/2` (with `F = {2}` the count is `1 > |F|/2 = 1/2`).
-/
theorem dispersion_residue_count
    (X : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (hFcard : 8 ≤ F.card)
    (q : ℕ) (hq : q.Prime) (hqF : q ∉ F) (hq2X : q ≤ 2*X) (E : ℤ)
    (hqE : ¬ (q:ℤ) ∣ E) (_hE0 : 0 < |E|) (hEq : |E| < (q:ℤ)) :
    ((F.filter (fun p => phase E q p ≤ (F.card : ℝ) / (32 * X))).card : ℝ)
      ≤ (F.card : ℝ) / 2 := by
  -- Let m : ℤ := ⌊2*δ*(X:ℝ)⌋; then m ≥ 0 and (m:ℝ) ≤ 2*δ*X. Let T : Finset ℤ := Finset.Icc (-m) m; its card is (2*m+1).toNat and (T.card : ℝ) ≤ 2*(2*δ*X) + 1 = 4*δ*X + 1.
  set δ : ℝ := (F.card : ℝ) / (32 * X)
  set m : ℤ := ⌊2 * δ * (X : ℝ)⌋
  set T : Finset ℤ := Finset.Icc (-m) m;
  -- Apply `card_prime_factors_dyadic_le_two` to bound the cardinality of the filter.
  have : ((F.filter (fun p => phase E q p ≤ δ)).card : ℝ) ≤ 2 * T.card := by
    have h_cover : F.filter (fun p => phase E q p ≤ δ) ⊆ T.biUnion (fun s => F.filter (fun p => (p : ℤ) ∣ (E - s * q))) := by
      intro p hp; simp_all +decide ;
      obtain ⟨ s, hs₁, hs₂ ⟩ := phase_dvd_witness X p q ( hF p hp.1 |>.1 ) ( hF p hp.1 |>.2.2 ) hq ( by aesop ) E δ ( by positivity ) hp.2;
      exact ⟨ s, Finset.mem_Icc.mpr ⟨ neg_le_of_abs_le <| Int.le_floor.mpr <| mod_cast hs₁, le_of_abs_le <| Int.le_floor.mpr <| mod_cast hs₁ ⟩, hs₂ ⟩;
    refine' le_trans ( Nat.cast_le.mpr ( Finset.card_le_card h_cover ) ) _;
    refine' mod_cast le_trans ( Finset.card_biUnion_le ) _;
    refine' le_trans ( Finset.sum_le_sum fun x hx => show #_ ≤ 2 from _ ) _;
    · have := card_prime_factors_dyadic_le_two X ( E - x * q ) ?_ ?_;
      · refine' le_trans _ this;
        exact Finset.card_mono fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ hF p ( Finset.mem_filter.mp hp |>.1 ) ], by linarith [ hF p ( Finset.mem_filter.mp hp |>.1 ) ] ⟩, hF p ( Finset.mem_filter.mp hp |>.1 ) |>.1, Finset.mem_filter.mp hp |>.2 ⟩;
      · exact fun h => hqE <| by rw [ sub_eq_zero ] at h; exact h.symm ▸ dvd_mul_left _ _;
      · -- Since $|x| \leq m$, we have $|x| \leq 2 * δ * X$.
        have hx_bound : |x| ≤ 2 * δ * X := by
          exact le_trans ( mod_cast abs_le.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩ ) ( Int.floor_le _ );
        rw [ mul_div, div_mul_eq_mul_div, le_div_iff₀ ] at * <;> norm_cast at * <;> cases X <;> norm_num at *;
        · aesop;
        · have h_card_bound : (F.card : ℤ) ≤ (2 * (Nat.succ ‹_›) + 1) := by
            exact_mod_cast le_trans ( Finset.card_le_card ( show F ⊆ Finset.Icc ( Nat.succ ‹_› ) ( 2 * ( Nat.succ ‹_› ) ) from fun p hp => Finset.mem_Icc.mpr ⟨ by linarith [ hF p hp ], by linarith [ hF p hp ] ⟩ ) ) ( by simp +arith +decide );
          norm_num [ abs_lt ] at *;
          constructor <;> cases abs_cases x <;> nlinarith [ pow_succ' ( ( ‹_› : ℕ ) : ℤ ) 2 ];
        · exact absurd hq2X hq.ne_zero;
    · norm_num [ mul_comm ];
  -- Since $T$ is a finite set of integers, its cardinality is at most $2m + 1$.
  have hT_card : T.card ≤ 2 * m + 1 := by
    simp +zetaDelta at *;
    exact ⟨ by linarith, by linarith [ show ⌊2 * ( ( F.card : ℝ ) / ( 32 * X ) ) * X⌋ ≥ 0 by positivity ] ⟩;
  -- Since $m \leq 2\delta X$, we have $2m + 1 \leq 4\delta X + 1$.
  have hT_card_le : (T.card : ℝ) ≤ 4 * δ * X + 1 := by
    linarith [ Int.floor_le ( 2 * δ * X ), Int.lt_floor_add_one ( 2 * δ * X ), ( by norm_cast : ( T.card : ℝ ) ≤ 2 * m + 1 ) ];
  by_cases hX : X = 0 <;> simp_all +decide [ mul_comm ];
  nlinarith [ show ( F.card : ℝ ) ≥ 8 by norm_cast, show ( X : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hX ), mul_div_cancel₀ ( F.card : ℝ ) ( by positivity : ( 32 * X : ℝ ) ≠ 0 ) ]

/-
**Dispersion energy bound** (`30 §1`):
    `∑_{p ∈ F} ‖E·q̄/p‖² ≥ |F|³/(2^11 X²) =: G_F`.

    **Status**: `sorry`.  Follows from `dispersion_residue_count`: at least half
    the primes have phase `> δ = |F|/(32X)`, each contributing `> δ²`.
-/
theorem dispersion_energy_bound
    (X : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (hFcard : 8 ≤ F.card)
    (q : ℕ) (hq : q.Prime) (hqF : q ∉ F) (hq2X : q ≤ 2*X) (E : ℤ)
    (hqE : ¬ (q:ℤ) ∣ E) (hE0 : 0 < |E|) (hEq : |E| < (q:ℤ)) :
    (F.card : ℝ)^3 / (2^11 * (X:ℝ)^2)
      ≤ ∑ p ∈ F, (phase E q p)^2 := by
  set δ := (F.card : ℝ) / (32 * X)
  have hsmall : ((F.filter (fun p => phase E q p ≤ δ)).card : ℝ) ≤ F.card / 2 := by
    exact dispersion_residue_count X F hF hFcard q hq hqF hq2X E hqE hE0 hEq
  have henergy := RequestProject.sum_sq_lower_bound_of_small_ball F
    (fun p => phase E q p) δ (F.card / 2) (by positivity) hsmall
  calc
    (F.card : ℝ)^3 / (2^11 * (X:ℝ)^2) =
        ((F.card : ℝ) - F.card / 2) * δ^2 := by
      dsimp [δ]
      ring
    _ ≤ ∑ p ∈ F, (phase E q p)^2 := henergy

end SBEEDispersion
