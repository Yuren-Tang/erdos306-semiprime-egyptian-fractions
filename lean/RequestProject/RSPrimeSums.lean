import RequestProject.DyadicBlockDef

/-!
# Rosser–Schoenfeld prime estimates — verbatim axioms and dyadic specializations

This leaf states the two classical analytic inputs of the construction **in the
exact form they appear in the literature**, so that each can be checked
character-for-character against its primary source:

* `rosser_schoenfeld_cor3` — Rosser & Schoenfeld, "Approximate formulas for some
  functions of prime numbers," Illinois J. Math. **6**(1) (1962), 64–94,
  **Corollary 3, eq. (3.8), p. 69**: `3x/(5 log x) < π(2x) − π(x)` for `x ≥ 20.5`.

* `rosser_schoenfeld_mertens` — *ibid.*, **Theorem 5, eqs. (3.17)–(3.18), p. 70**:
  `log log x + B − 1/(2 log²x) < ∑_{p≤x} 1/p < log log x + B + 1/(2 log²x)`
  (left for `x > 1`, right for `x ≥ 286`), `B = 0.26149721284764…` (eq. (2.10),
  p. 65).  Historical origin: F. Mertens, "Ein Beitrag zur analytischen
  Zahlentheorie," J. reine angew. Math. **78** (1874), 46–62, eq. (13), p. 52.

The dyadic-block specializations the construction actually consumes
(`dyadic_prime_density`, `dyadic_mertens_cumulative`,
`dyadic_control_recipLoad_eventually_small`) are then **derived as theorems** from
these verbatim statements — they are no longer axioms.
-/

open Finset BigOperators

noncomputable section

namespace RosserSchoenfeld

/-- `∑_{p ≤ x} 1 / p`, with the real endpoint represented by `⌊x⌋₊`. -/
def primeRecipSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)

/-- **Rosser–Schoenfeld (1962), Corollary 3, eq. (3.8), p. 69.**
"Approximate formulas for some functions of prime numbers," Illinois J. Math.
6(1), 64–94.  DOI 10.1215/ijm/1255631807.  Verbatim: for `x ≥ 20½`,
`3x/(5 log x) < π(2x) − π(x)`, where `π` (`Nat.primeCounting`) is the number of
primes `≤ x` (so `π(2x) − π(x)` here is `Nat.primeCounting ⌊2x⌋ − Nat.primeCounting ⌊x⌋`). -/
axiom rosser_schoenfeld_cor3 (x : ℝ) (hx : (41 : ℝ) / 2 ≤ x) :
    3 * x / (5 * Real.log x) <
      (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **Rosser–Schoenfeld (1962), Theorem 5, eqs. (3.17)–(3.18), p. 70.**
"Approximate formulas for some functions of prime numbers," Illinois J. Math.
6(1), 64–94.  DOI 10.1215/ijm/1255631807.  Verbatim: there is a constant `B`
(the Mertens constant; RS eq. (2.10), p. 65, `B = 0.26149721284764…`) such that,
where the sum `∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, 1/p` below is exactly
`∑_{p ≤ x} 1/p` (reciprocals of the primes `≤ x`),
* (3.17) `log log x + B − 1/(2 log²x) < ∑_{p≤x} 1/p` for `1 < x`, and
* (3.18) `∑_{p≤x} 1/p < log log x + B + 1/(2 log²x)` for `286 ≤ x`.

Stating `B` existentially (rather than pinning a rounded decimal) keeps the
axiom an exact transcription of Theorem 5.  Historical origin of the
reciprocal-prime asymptotic: F. Mertens, "Ein Beitrag zur analytischen
Zahlentheorie," J. reine angew. Math. 78 (1874), 46–62, eq. (13), p. 52
(`∑_{q≤G} 1/q = log log G + 𝔈 − H + δ`, `δ < 4/log(G+1) + 2/(G log G)`). -/
axiom rosser_schoenfeld_thm5 :
    ∃ B : ℝ, ∀ x : ℝ,
      (1 < x →
          Real.log (Real.log x) + B - 1 / (2 * (Real.log x) ^ 2)
            < ∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧
      (286 ≤ x →
          ∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
            < Real.log (Real.log x) + B + 1 / (2 * (Real.log x) ^ 2))

end RosserSchoenfeld

namespace GlobalControl

/-- `2 ^ n` is not prime once `n ≥ 2` (it has the proper divisor `2`). -/
lemma two_pow_not_prime {n : ℕ} (hn : 2 ≤ n) : ¬ (2 ^ n).Prime := by
  intro hp
  have hdvd : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have heq : (2 : ℕ) = 2 ^ n := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd
  have hge : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

/-- `π n = π' n` when `n` is not prime (no contribution from `n` itself). -/
lemma primeCounting_eq_primeCounting'_of_not_prime {n : ℕ} (hn : ¬ n.Prime) :
    Nat.primeCounting n = Nat.primeCounting' n := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ, if_neg hn, Nat.add_zero]

/-- The dyadic block `[2ᵏ, 2ᵏ⁺¹)` has exactly `π'(2ᵏ⁺¹) − π'(2ᵏ)` primes. -/
lemma dyadicBlock_card_eq (k : ℕ) :
    (dyadicBlock k).card
      = Nat.primeCounting' (2 ^ (k + 1)) - Nat.primeCounting' (2 ^ k) := by
  have hle : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
  have hsub : Nat.primesBelow (2 ^ k) ⊆ Nat.primesBelow (2 ^ (k + 1)) := by
    intro p hp
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hle, hp.2⟩
  have hset : dyadicBlock k = Nat.primesBelow (2 ^ (k + 1)) \ Nat.primesBelow (2 ^ k) := by
    ext p
    simp only [dyadicBlock, Nat.primesBelow, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_sdiff, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨h2, hp⟩, fun h => absurd h.1 (not_lt.mpr h1)⟩
    · rintro ⟨⟨h2, hp⟩, hn⟩
      refine ⟨⟨?_, h2⟩, hp⟩
      by_contra h
      exact hn ⟨not_le.mp h, hp⟩
  have hkey : (dyadicBlock k).card + Nat.primeCounting' (2 ^ k)
      = Nat.primeCounting' (2 ^ (k + 1)) := by
    rw [hset, ← Nat.primesBelow_card_eq_primeCounting' (2 ^ k),
      ← Nat.primesBelow_card_eq_primeCounting' (2 ^ (k + 1))]
    exact Finset.card_sdiff_add_card_eq_card hsub
  omega

/-- **Dyadic prime density** (was an axiom; now derived from Rosser–Schoenfeld
Corollary 3, eq. (3.8)).  For `k ≥ 5`,
`2ᵏ / (2 log 2ᵏ) ≤ #{p prime : 2ᵏ ≤ p < 2ᵏ⁺¹}`. -/
theorem dyadic_prime_density (k : ℕ) (hk : 5 ≤ k) :
    (2 ^ k : ℝ) / (2 * Real.log (2 ^ k)) ≤ ((dyadicBlock k).card : ℝ) := by
  -- Abbreviations and basic positivity.
  set x : ℝ := (2 : ℝ) ^ k with hxdef
  have hx32 : (32 : ℝ) ≤ x := by
    rw [hxdef]
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hx1 : (1 : ℝ) < x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogpos : (0 : ℝ) < Real.log x := Real.log_pos hx1
  -- Floor evaluations: ⌊x⌋ = 2ᵏ and ⌊2x⌋ = 2ᵏ⁺¹.
  have hxnat : x = ((2 ^ k : ℕ) : ℝ) := by rw [hxdef]; push_cast; ring
  have h2xnat : 2 * x = ((2 ^ (k + 1) : ℕ) : ℝ) := by rw [hxdef]; push_cast; ring
  have hfloorx : ⌊x⌋₊ = 2 ^ k := by rw [hxnat, Nat.floor_natCast]
  have hfloor2x : ⌊2 * x⌋₊ = 2 ^ (k + 1) := by rw [h2xnat, Nat.floor_natCast]
  -- π at the two endpoints equals π' (the powers of 2 are not prime).
  have hk2 : 2 ≤ k := by omega
  have hπx : Nat.primeCounting ⌊x⌋₊ = Nat.primeCounting' (2 ^ k) := by
    rw [hfloorx, primeCounting_eq_primeCounting'_of_not_prime (two_pow_not_prime hk2)]
  have hπ2x : Nat.primeCounting ⌊2 * x⌋₊ = Nat.primeCounting' (2 ^ (k + 1)) := by
    rw [hfloor2x, primeCounting_eq_primeCounting'_of_not_prime (two_pow_not_prime (by omega))]
  -- The RS difference equals the block cardinality (as reals).
  have hmono : Nat.primeCounting' (2 ^ k) ≤ Nat.primeCounting' (2 ^ (k + 1)) :=
    Nat.monotone_primeCounting' (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
  have hcardR :
      (Nat.primeCounting ⌊2 * x⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ)
        = ((dyadicBlock k).card : ℝ) := by
    rw [hπx, hπ2x, dyadicBlock_card_eq, Nat.cast_sub hmono]
  -- Rosser–Schoenfeld Corollary 3 at this `x`.
  have hRS := RosserSchoenfeld.rosser_schoenfeld_cor3 x (by linarith)
  rw [hcardR] at hRS
  -- Close: 2ᵏ/(2 log 2ᵏ) = x/(2 log x) ≤ 3x/(5 log x) < card.
  have hlog_eq : Real.log (2 ^ k) = Real.log x := by rw [hxdef]
  rw [hlog_eq]
  have hstep : x / (2 * Real.log x) ≤ 3 * x / (5 * Real.log x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hxpos, hlogpos]
  calc x / (2 * Real.log x) ≤ 3 * x / (5 * Real.log x) := hstep
    _ ≤ _ := le_of_lt hRS

/-- `exp 1.06 < 3`, hence `1.06 < log 3` (the true value is `≈ 1.0986`); the
cheap lower bound used to clear the `21/20` threshold. -/
private lemma log_three_gt : (1.06 : ℝ) < Real.log 3 := by
  refine (Real.lt_log_iff_exp_lt (by norm_num)).mpr ?_
  have hb : (0.94 : ℝ) ≤ Real.exp (-0.06) := by
    have h := Real.add_one_le_exp (-0.06 : ℝ); linarith
  have hpos06 : (0 : ℝ) < Real.exp 0.06 := Real.exp_pos _
  rw [Real.exp_neg] at hb
  have h06m : (0.94 : ℝ) * Real.exp 0.06 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hb (le_of_lt hpos06)
    rwa [inv_mul_cancel₀ (ne_of_gt hpos06)] at this
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hsplit : Real.exp (1.06 : ℝ) = Real.exp 1 * Real.exp 0.06 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [he1, h06m, hpos06]

/-- For `m ≥ 2`, `∑_{p ≤ 2^m} 1/p = ∑_{p ∈ primesBelow (2^m)} 1/p` (the endpoint
`2^m` is composite, so the closed and open upper limits agree). -/
private lemma primeRecipSum_two_pow {m : ℕ} (hm : 2 ≤ m) :
    RosserSchoenfeld.primeRecipSum ((2 : ℝ) ^ m)
      = ∑ p ∈ Nat.primesBelow (2 ^ m), (1 : ℝ) / (p : ℝ) := by
  have hfloor : ⌊((2 : ℝ) ^ m)⌋₊ = 2 ^ m := by
    rw [show ((2 : ℝ) ^ m) = ((2 ^ m : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hset : (Finset.Icc 2 (2 ^ m)).filter Nat.Prime = Nat.primesBelow (2 ^ m) := by
    ext p
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hple⟩, hp⟩
      exact ⟨lt_of_le_of_ne hple (fun h => two_pow_not_prime hm (h ▸ hp)), hp⟩
    · rintro ⟨hlt, hp⟩
      exact ⟨⟨hp.two_le, le_of_lt hlt⟩, hp⟩
  unfold RosserSchoenfeld.primeRecipSum
  rw [hfloor, hset]

/-- The biUnion of dyadic blocks over `[k0, 3k0]` is exactly the primes in
`[2^{k0}, 2^{3k0+1})`. -/
private lemma biUnion_dyadicBlock_eq_sdiff (k0 : ℕ) :
    (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock
      = Nat.primesBelow (2 ^ (3 * k0 + 1)) \ Nat.primesBelow (2 ^ k0) := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_Icc, dyadicBlock, Finset.mem_filter,
    Finset.mem_Ico, Nat.primesBelow, Finset.mem_sdiff, Finset.mem_range, not_and]
  constructor
  · rintro ⟨k, ⟨hk0k, hk3⟩, ⟨h2k, hlt2k1⟩, hp⟩
    refine ⟨⟨?_, hp⟩, ?_⟩
    · calc p < 2 ^ (k + 1) := hlt2k1
        _ ≤ 2 ^ (3 * k0 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact fun hlt =>
        absurd hlt (not_lt.mpr (le_trans (Nat.pow_le_pow_right (by norm_num) hk0k) h2k))
  · rintro ⟨⟨hlt, hp⟩, hge⟩
    have hp0 : p ≠ 0 := hp.pos.ne'
    have hge' : 2 ^ k0 ≤ p := by
      by_contra h
      exact hge (not_le.mp h) hp
    have hkle : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 hp0
    have hklt : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
    refine ⟨Nat.log 2 p, ⟨?_, ?_⟩, ⟨hkle, hklt⟩, hp⟩
    · by_contra hc
      push_neg at hc
      have : p < 2 ^ k0 := lt_of_lt_of_le hklt (Nat.pow_le_pow_right (by norm_num) (by omega))
      omega
    · by_contra hc
      push_neg at hc
      have : 2 ^ (3 * k0 + 1) ≤ p :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hkle
      omega

/-- **Dyadic Mertens cumulative lower bound** (was an axiom; now derived from
Rosser–Schoenfeld Theorem 5, `rosser_schoenfeld_thm5`).  For all large `k0`, the
reciprocal sum of the primes in `[2^{k0}, 2^{3k0+1})` is at least `21/20` (the
true limit is `log 3 ≈ 1.0986`).  Apply (3.17) at `x = 2^{3k0+1}` (lower) and
(3.18) at `x = 2^{k0}` (upper); `B` cancels, the `log log` difference is
`log((3k0+1)/k0) ≥ log 3 > 1.06`, and the two error terms `1/(2 log²)` are
`< 0.003` each for `k0 ≥ 20`. -/
theorem dyadic_mertens_cumulative :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
      (21 : ℝ) / 20 ≤
        ∑ p ∈ (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock, (1 : ℝ) / (p : ℝ) := by
  obtain ⟨B, hB⟩ := RosserSchoenfeld.rosser_schoenfeld_thm5
  refine ⟨20, by norm_num, fun k0 hk0 => ?_⟩
  have hk0_2 : 2 ≤ k0 := by omega
  have hk0_pos : 0 < k0 := by omega
  have hbig_m : 2 ≤ 3 * k0 + 1 := by omega
  -- Block sum = prefix difference of `primeRecipSum`.
  have hsub : Nat.primesBelow (2 ^ k0) ⊆ Nat.primesBelow (2 ^ (3 * k0 + 1)) := by
    intro p hp
    simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.pow_le_pow_right (by norm_num) (by omega)), hp.2⟩
  have hsplit :
      ∑ p ∈ (Finset.Icc k0 (3 * k0)).biUnion dyadicBlock, (1 : ℝ) / (p : ℝ)
        = RosserSchoenfeld.primeRecipSum ((2 : ℝ) ^ (3 * k0 + 1))
          - RosserSchoenfeld.primeRecipSum ((2 : ℝ) ^ k0) := by
    rw [biUnion_dyadicBlock_eq_sdiff, primeRecipSum_two_pow hbig_m,
      primeRecipSum_two_pow hk0_2, eq_sub_iff_add_eq]
    exact Finset.sum_sdiff hsub
  rw [hsplit]
  -- Theorem 5 at the two endpoints.
  have hxbig : (1 : ℝ) < (2 : ℝ) ^ (3 * k0 + 1) := by
    calc (1 : ℝ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * k0 + 1) := by apply pow_le_pow_right₀ (by norm_num); omega
  have hxsmall : (286 : ℝ) ≤ (2 : ℝ) ^ k0 := by
    calc (286 : ℝ) ≤ 2 ^ 20 := by norm_num
      _ ≤ 2 ^ k0 := pow_le_pow_right₀ (by norm_num) hk0
  -- `primeRecipSum` is definitionally the inlined sum in the axiom, so these
  -- ascriptions just re-expose the bounds in terms of the proof's abbreviation.
  have hlow : Real.log (Real.log ((2 : ℝ) ^ (3 * k0 + 1))) + B
        - 1 / (2 * (Real.log ((2 : ℝ) ^ (3 * k0 + 1))) ^ 2)
        < RosserSchoenfeld.primeRecipSum ((2 : ℝ) ^ (3 * k0 + 1)) :=
    (hB ((2 : ℝ) ^ (3 * k0 + 1))).1 hxbig
  have hupp : RosserSchoenfeld.primeRecipSum ((2 : ℝ) ^ k0)
        < Real.log (Real.log ((2 : ℝ) ^ k0)) + B
          + 1 / (2 * (Real.log ((2 : ℝ) ^ k0)) ^ 2) :=
    (hB ((2 : ℝ) ^ k0)).2 hxsmall
  -- `log log` difference ≥ log 3.
  have hLL : Real.log 3 ≤
      Real.log (Real.log ((2 : ℝ) ^ (3 * k0 + 1))) - Real.log (Real.log ((2 : ℝ) ^ k0)) := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hk0R : (0 : ℝ) < ((k0 : ℕ) : ℝ) := by exact_mod_cast hk0_pos
    have hbigR : (0 : ℝ) < ((3 * k0 + 1 : ℕ) : ℝ) := by positivity
    have e1 : Real.log ((2 : ℝ) ^ (3 * k0 + 1)) = ((3 * k0 + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have e2 : Real.log ((2 : ℝ) ^ k0) = ((k0 : ℕ) : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [e1, e2, Real.log_mul (ne_of_gt hbigR) (ne_of_gt hlog2pos),
      Real.log_mul (ne_of_gt hk0R) (ne_of_gt hlog2pos)]
    have hcollapse :
        Real.log ((3 * k0 + 1 : ℕ) : ℝ) + Real.log (Real.log 2)
            - (Real.log ((k0 : ℕ) : ℝ) + Real.log (Real.log 2))
          = Real.log ((3 * k0 + 1 : ℕ) : ℝ) - Real.log ((k0 : ℕ) : ℝ) := by ring
    rw [hcollapse, ← Real.log_div (ne_of_gt hbigR) (ne_of_gt hk0R),
      Real.log_le_log_iff (by norm_num) (div_pos hbigR hk0R), le_div_iff₀ hk0R]
    push_cast
    nlinarith [hk0_pos]
  -- Error terms `< 0.003` for `m ≥ 20`.
  have herr : ∀ m : ℕ, 20 ≤ m →
      1 / (2 * (Real.log ((2 : ℝ) ^ m)) ^ 2) < (3 : ℝ) / 1000 := by
    intro m hm
    have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl : (0 : ℝ) < Real.log 2 := lt_trans (by norm_num) hlog2
    have hLm : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by rw [Real.log_pow]
    have hmR : (20 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbig13 : (13 : ℝ) < (m : ℝ) * Real.log 2 := by
      have h20 : (0 : ℝ) ≤ (m : ℝ) - 20 := by linarith
      nlinarith [hlog2, hmR, mul_nonneg h20 (le_of_lt hl)]
    have htsq : (169 : ℝ) < ((m : ℝ) * Real.log 2) ^ 2 := by nlinarith [hbig13]
    rw [hLm, div_lt_iff₀ (by positivity)]
    nlinarith [htsq]
  have he1 := herr (3 * k0 + 1) (by omega)
  have he2 := herr k0 hk0
  have hlog3 := log_three_gt
  linarith [hlow, hupp, hLL, he1, he2, hlog3]

end GlobalControl

end
