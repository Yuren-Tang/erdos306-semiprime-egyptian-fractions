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

/-
The reciprocal phase is even in `E`: `‖(−E)q̄/p‖ = ‖E q̄/p‖`.  (`round` is a
    nearest-integer map, so the distance to it is symmetric under negation.)
-/
lemma phase_neg (E : ℤ) (q p : ℕ) : phase (-E) q p = phase E q p := by
  unfold phase;
  norm_num [ round_eq ];
  rw [ neg_div, abs_sub_comm ];
  rw [ show ( - ( ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val / p ) + 1 / 2 : ℝ ) = - ( ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val / p + 1 / 2 ) + 1 by ring_nf ] ; norm_num [ Int.floor_neg ] ; ring_nf;
  rw [ show ( -1 / 2 - ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ) = - ( 1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ) by ring_nf, Int.floor_neg ] ; ring_nf; norm_num;
  rw [ show ( ⌈1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹⌉ : ℤ ) = ⌊1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹⌋ + if ( 1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ) ≤ ⌊1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹⌋ then 0 else 1 from ?_ ] ; split_ifs <;> norm_num ; ring_nf;
  · rw [ abs_of_nonneg, abs_of_nonpos ] <;> linarith [ Int.floor_le ( 1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( 1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ) ];
  · ring_nf;
  · split_ifs <;> norm_num [ Int.ceil_eq_iff ] at * <;> constructor <;> linarith [ Int.floor_le ( 1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( 1 / 2 + ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val * ( p : ℝ ) ⁻¹ ) ] ;

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
  -- Let $x_A = A \cdot q^{-1} / p$ and $x_B = B \cdot q^{-1} / p$.
  set x_A : ℝ := (A : ℝ) * (((q : ZMod p)⁻¹).val : ℝ) / (p : ℝ)
  set x_B : ℝ := (B : ℝ) * (((q : ZMod p)⁻¹).val : ℝ) / (p : ℝ);
  -- By the properties of the round function, we have $|x_A - x_B - \text{round}(x_A - x_B)| \leq |x_A - \text{round}(x_A) - (x_B - \text{round}(x_B))|$.
  have h_round : |x_A - x_B - round (x_A - x_B)| ≤ |x_A - round x_A - (x_B - round x_B)| := by
    have h_round : ∀ x : ℝ, ∀ n : ℤ, |x - round x| ≤ |x - n| := by
      intros x n
      apply round_le;
    convert h_round ( x_A - x_B ) ( round x_A - round x_B ) using 1 ; push_cast ; ring_nf;
  convert h_round.trans ( abs_sub _ _ ) using 1;
  unfold phase; ring_nf;
  grind

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
  refine' ⟨ E * ( ( q : ZMod p ) ⁻¹ |> ZMod.val ) - ⌊ ( E : ℝ ) * ( ( q : ZMod p ) ⁻¹ |> ZMod.val : ℝ ) / p + 1 / 2⌋ * p, _, _ ⟩;
  · unfold phase at hδ;
    norm_num [ abs_le ] at *;
    norm_num [ round_eq ] at *;
    constructor <;> nlinarith [ show ( p : ℝ ) ≤ 2 * X by norm_cast, show ( p : ℝ ) > 0 by exact Nat.cast_pos.mpr hp.pos, mul_div_cancel₀ ( ( E : ℝ ) * ( q : ZMod p ) ⁻¹.val ) ( Nat.cast_ne_zero.mpr hp.ne_zero ) ];
  · haveI := Fact.mk hp; haveI := Fact.mk hq; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
    rw [ mul_assoc, inv_mul_cancel₀ ( by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact fun h => hpq <| by have := Nat.prime_dvd_prime_iff_eq hp hq; tauto ), mul_one, sub_self ]

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
  -- By `dispersion_residue_count`, there are at least `F.card / 2` primes `p` in `F` such that `phase E q p > |F| / (32 * X)`.
  have h_residue_count : ((F.filter (fun p => phase E q p > (F.card : ℝ) / (32 * X))).card : ℝ) ≥ (F.card : ℝ) / 2 := by
    have h_residue_count : ((F.filter (fun p => phase E q p ≤ (F.card : ℝ) / (32 * X))).card : ℝ) ≤ (F.card : ℝ) / 2 := by
      convert dispersion_residue_count X F ‹_› hFcard q hq hqF hq2X E hqE ( by positivity ) ( by linarith ) using 1;
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

end SBEEDispersion