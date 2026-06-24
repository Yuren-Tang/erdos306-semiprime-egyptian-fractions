import RequestProject.DyadicPrimes

open Finset BigOperators

noncomputable section

namespace CircleMethod

/-!
# R2-mass: the block-prime product-load lower bound

The block-aligned mass batch draws from products `p·q` of two distinct block
primes.  Its available reciprocal load is `∑_{p<q} 1/(pq) = (S² − S₂)/2` where
`S = ∑ 1/p`, `S₂ = ∑ 1/p²`.  This file proves the algebraic identity (general)
and will assemble the numeric lower bound `≥ 1/2` from `dyadic_mertens_cumulative`
(`S ≥ 21/20`) plus a tail bound `S₂ ≤ 1/(2^{k₀}−1)`.
-/

/-- **The pair-sum identity.**  `(∑ x)² = ∑ x² + 2·∑_{p<q} xₚxq`.  Pure algebra,
via the diagonal/off-diagonal split of `s ×ˢ s` and the `Prod.swap` symmetry of the
off-diagonal. -/
lemma sq_sum_eq_sum_sq_add_two_sum_lt {α : Type*} [LinearOrder α]
    (s : Finset α) (x : α → ℝ) :
    (∑ p ∈ s, x p) ^ 2
      = (∑ p ∈ s, (x p) ^ 2)
        + 2 * ∑ pq ∈ s.offDiag.filter (fun pq => pq.1 < pq.2), x pq.1 * x pq.2 := by
  classical
  have hexp : (∑ p ∈ s, x p) ^ 2 = ∑ pq ∈ s ×ˢ s, x pq.1 * x pq.2 := by
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  rw [hexp, ← Finset.diag_union_offDiag s,
      Finset.sum_union (Finset.disjoint_diag_offDiag s), Finset.sum_diag]
  have hdiag : ∑ p ∈ s, x p * x p = ∑ p ∈ s, (x p) ^ 2 :=
    Finset.sum_congr rfl (fun p _ => by rw [sq])
  rw [hdiag]
  congr 1
  -- remaining: ∑_{offDiag} x.1*x.2 = 2 * ∑_{offDiag, p<q} x.1*x.2
  have hsplit := Finset.sum_filter_add_sum_filter_not s.offDiag
    (fun pq => pq.1 < pq.2) (fun pq => x pq.1 * x pq.2)
  have hswap :
      ∑ pq ∈ s.offDiag.filter (fun pq => ¬ pq.1 < pq.2), x pq.1 * x pq.2
        = ∑ pq ∈ s.offDiag.filter (fun pq => pq.1 < pq.2), x pq.1 * x pq.2 := by
    refine Finset.sum_nbij' (fun pq => Prod.swap pq) (fun pq => Prod.swap pq) ?_ ?_ ?_ ?_ ?_
    · intro pq hpq
      rw [Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
      obtain ⟨⟨h1, h2, hne⟩, hnlt⟩ := hpq
      refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact lt_of_le_of_ne (not_lt.mp hnlt) hne.symm
    · intro pq hpq
      rw [Finset.mem_filter, Finset.mem_offDiag] at hpq ⊢
      obtain ⟨⟨h1, h2, hne⟩, hlt⟩ := hpq
      refine ⟨⟨h2, h1, fun h => hne h.symm⟩, ?_⟩
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact not_lt.mpr (le_of_lt hlt)
    · intro pq _; simp
    · intro pq _; simp
    · intro pq _; simp only [Prod.fst_swap, Prod.snd_swap]; ring
  rw [← hsplit, hswap]; ring

/-! ## The block-prime pool -/

open GlobalControl in
/-- The block primes drawn from the dyadic blocks `[2^{k₀}, 2^{3k₀+1})`. -/
def blockPrimes (k0 : ℕ) : Finset ℕ :=
  (Finset.Icc k0 (3 * k0)).biUnion GlobalControl.dyadicBlock

open GlobalControl in
/-- Every block prime is prime. -/
lemma blockPrimes_prime {k0 p : ℕ} (hp : p ∈ blockPrimes k0) : Nat.Prime p := by
  rw [blockPrimes, Finset.mem_biUnion] at hp
  obtain ⟨k, _, hpk⟩ := hp
  exact (Finset.mem_filter.mp hpk).2

open GlobalControl in
/-- Every block prime is `≥ 2^{k₀}`. -/
lemma blockPrimes_ge {k0 p : ℕ} (hp : p ∈ blockPrimes k0) : 2 ^ k0 ≤ p := by
  rw [blockPrimes, Finset.mem_biUnion] at hp
  obtain ⟨k, hk, hpk⟩ := hp
  rw [GlobalControl.dyadicBlock, Finset.mem_filter, Finset.mem_Ico] at hpk
  rw [Finset.mem_Icc] at hk
  exact le_trans (Nat.pow_le_pow_right (by norm_num) hk.1) hpk.1.1

open GlobalControl in
/-- Every block prime is `< 2^{3k₀+1}`. -/
lemma blockPrimes_lt {k0 p : ℕ} (hp : p ∈ blockPrimes k0) : p < 2 ^ (3 * k0 + 1) := by
  rw [blockPrimes, Finset.mem_biUnion] at hp
  obtain ⟨k, hk, hpk⟩ := hp
  rw [GlobalControl.dyadicBlock, Finset.mem_filter, Finset.mem_Ico] at hpk
  rw [Finset.mem_Icc] at hk
  exact lt_of_lt_of_le hpk.1.2 (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The block primes are contained in `Ico (2^{k₀}) (2^{3k₀+1})`. -/
lemma blockPrimes_subset_Ico (k0 : ℕ) :
    blockPrimes k0 ⊆ Finset.Ico (2 ^ k0) (2 ^ (3 * k0 + 1)) := by
  intro p hp
  rw [Finset.mem_Ico]
  exact ⟨blockPrimes_ge hp, blockPrimes_lt hp⟩

/-! ## T1 — the squared tail is small -/

/-
**T1.**  The reciprocal-square load of the block primes is at most
`1/(2^{k₀}-1)`.
-/
lemma blockPrimes_sub_sq_tail (k0 : ℕ) (hk0 : 5 ≤ k0) :
    ∑ p ∈ blockPrimes k0, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / ((2 ^ k0 : ℝ) - 1) := by
  refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( blockPrimes_subset_Ico k0 ) ( fun _ _ _ => by positivity ) ) _;
  have h_sum_bound : ∀ n : ℕ, 2^k0 ≤ n → (1 : ℝ) / n^2 ≤ 1 / (n - 1) - 1 / n := by
    intro n hn; rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith [ show ( n : ℝ ) ≥ 2 ^ k0 by exact_mod_cast hn, show ( 2 : ℝ ) ^ k0 ≥ 32 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) hk0 ) ] ;
  have h_telescope : ∀ N : ℕ, 2^k0 ≤ N → (∑ n ∈ Finset.Ico (2^k0) N, (1 / (n - 1 : ℝ) - 1 / (n : ℝ))) = (1 / (2^k0 - 1 : ℝ)) - (1 / (N - 1 : ℝ)) := by
    intro N hN; induction hN <;> simp_all +decide [ Finset.sum_Ico_succ_top ] ;
    linarith;
  exact le_trans ( Finset.sum_le_sum fun i hi => h_sum_bound i <| Finset.mem_Ico.mp hi |>.1 ) ( by rw [ h_telescope _ <| Nat.pow_le_pow_right ( by decide ) <| by linarith ] ; exact sub_le_self _ <| one_div_nonneg.mpr <| sub_nonneg.mpr <| mod_cast Nat.one_le_iff_ne_zero.mpr <| by positivity )

/-! ## Injectivity of the product map on distinct-prime pairs -/

/-
The product map `(p,q) ↦ p·q` is injective on the strictly-ordered
off-diagonal pairs of block primes (unique factorization of a semiprime).
-/
lemma blockPrimes_pair_prod_injOn (k0 : ℕ) :
    Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2)
      ↑((blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2)) := by
  intros pq hpq pq' hpq' h_eq;
  simp +zetaDelta at *;
  -- Since `pq.1` and `pq.2` are primes and `pq.1 * pq.2 = pq'.1 * pq'.2`, we have `pq.1 = pq'.1` or `pq.1 = pq'.2`.
  have h_cases : pq.1 = pq'.1 ∨ pq.1 = pq'.2 := by
    have h_cases : Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ Nat.Prime pq'.1 ∧ Nat.Prime pq'.2 := by
      exact ⟨ blockPrimes_prime hpq.1.1, blockPrimes_prime hpq.1.2.1, blockPrimes_prime hpq'.1.1, blockPrimes_prime hpq'.1.2.1 ⟩;
    have := h_cases.1.dvd_mul.mp ( h_eq ▸ dvd_mul_right _ _ ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
  cases h_cases <;> simp_all +decide [ mul_comm ];
  · cases h_eq <;> simp_all +decide [ Prod.ext_iff ];
    exact absurd ( blockPrimes_prime hpq'.1.1 ) ( by norm_num );
  · grind

/-! ## T2 — the product-load lower bound -/

/-
**T2 (core).**  Given the Mertens reciprocal-sum lower bound `S ≥ 21/20` for a
fixed `k₀ ≥ 5`, the off-diagonal (`p<q`) reciprocal product-load of the block
primes is at least `1/2`.  (The Mertens input is supplied as a hypothesis here;
the unconditional `blockPrimes_product_load_ge` feeds it from the axiom.)
-/
lemma blockPrimes_product_load_ge_of (k0 : ℕ) (hk0 : 5 ≤ k0)
    (hmertens : (21 : ℝ) / 20 ≤ ∑ p ∈ blockPrimes k0, (1 : ℝ) / (p : ℝ)) :
    (1 : ℝ) / 2 ≤
      ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  -- By `sq_sum_eq_sum_sq_add_two_sum_lt`, we have `S^2 = S₂ + 2 * Off`.
  have h_identity : (∑ p ∈ blockPrimes k0, (1 : ℝ) / (p : ℝ)) ^ 2 =
    (∑ p ∈ blockPrimes k0, (1 : ℝ) / (p : ℝ) ^ 2) +
    2 * ∑ pq ∈ (blockPrimes k0 |>.offDiag.filter (fun pq => pq.1 < pq.2)), (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
      convert sq_sum_eq_sum_sq_add_two_sum_lt ( blockPrimes k0 ) ( fun p : ℕ => ( 1 : ℝ ) / p ) using 1 ; norm_num [ mul_comm ];
  nlinarith [ show ( ∑ p ∈ blockPrimes k0, 1 / ( p : ℝ ) ^ 2 ) ≤ 1 / 31 by exact le_trans ( blockPrimes_sub_sq_tail k0 hk0 ) ( by rw [ div_le_div_iff₀ ] <;> linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hk0 ] ) ]

/-! ## A generic greedy reciprocal-window selector -/

/-
Generic greedy window: from a finite set `P` of positive naturals whose
reciprocal load reaches `target`, with every individual reciprocal below `gap`,
one can select a subset whose reciprocal load lands in `[target, target+gap]`.
-/
lemma exists_subset_recip_window_strict_upper (P : Finset ℕ) (target gap : ℝ)
    (htarget : 0 ≤ target) (hgap : 0 < gap)
    (hsmall : ∀ e ∈ P, (1 : ℝ) / (e : ℝ) < gap)
    (hsum : target ≤ ∑ e ∈ P, (1 : ℝ) / (e : ℝ)) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧
      target ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ∧
      ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) < target + gap := by
  classical
  let goodSubsets : Finset (Finset ℕ) :=
    P.powerset.filter (fun Q => target ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ))
  have hgood_nonempty : goodSubsets.Nonempty := by
    refine ⟨P, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, hsum⟩
  obtain ⟨Q, hQgood, hQmin⟩ :=
    goodSubsets.exists_minimalFor (fun Q : Finset ℕ => Q.card) hgood_nonempty
  have hQsubset : Q ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hQgood).1
  have hQsum_lb : target ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) :=
    (Finset.mem_filter.mp hQgood).2
  have hproper_lt :
      ∀ S ⊂ Q, (∑ e ∈ S, (1 : ℝ) / (e : ℝ)) < target := by
    intro S hS
    exact not_le.mp fun hSsum => by
      have hSgood : S ∈ goodSubsets := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.Subset.trans hS.1 hQsubset), hSsum⟩
      have hcard_lt : S.card < Q.card := Finset.card_lt_card hS
      exact (not_lt_of_ge (hQmin hSgood (le_of_lt hcard_lt))) hcard_lt
  rcases Q.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp_all +decide [Finset.subset_iff]
    exact ⟨∅, by norm_num, by linarith, by linarith⟩
  · refine ⟨Q, hQsubset, hQsum_lb, ?_⟩
    have hprev := hproper_lt (Q.erase x) (Finset.erase_ssubset hx)
    rw [Finset.sum_erase_eq_sub hx] at hprev
    have hxP : x ∈ P := hQsubset hx
    linarith [hsmall x hxP]

lemma exists_subset_recip_window (P : Finset ℕ) (target gap : ℝ)
    (htarget : 0 ≤ target) (hgap : 0 < gap)
    (hsmall : ∀ e ∈ P, (1 : ℝ) / (e : ℝ) < gap)
    (hsum : target ≤ ∑ e ∈ P, (1 : ℝ) / (e : ℝ)) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧
      target ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ∧
      ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ≤ target + gap := by
  obtain ⟨Q, hQP, hQlo, hQhi⟩ :=
    exists_subset_recip_window_strict_upper P target gap htarget hgap hsmall hsum
  exact ⟨Q, hQP, hQlo, le_of_lt hQhi⟩

/-- Residual version of the greedy window.  A fixed base load has already been
spent by control and gadget edges; choose a subset whose additional load makes
the total land in `[lo, hi)` strictly. -/
lemma exists_subset_recip_residual_window (P : Finset ℕ) (base lo hi gap : ℝ)
    (hlo : base ≤ lo) (hgap_eq : gap = hi - lo) (hgap : 0 < gap)
    (hsmall : ∀ e ∈ P, (1 : ℝ) / (e : ℝ) < gap)
    (hsum : lo - base ≤ ∑ e ∈ P, (1 : ℝ) / (e : ℝ)) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧
      lo ≤ base + ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ∧
      base + ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) < hi := by
  have htarget : 0 ≤ lo - base := sub_nonneg.mpr hlo
  obtain ⟨Q, hQP, hQlo, hQhi⟩ :=
    exists_subset_recip_window_strict_upper P (lo - base) gap htarget hgap hsmall hsum
  refine ⟨Q, hQP, ?_, ?_⟩
  · linarith
  · rw [hgap_eq] at hQhi
    linarith

/-! ## T3 — the block-aligned mass batch -/

/-
**T3 (core).**  Given a threshold `k₁ ≥ 5` from which the off-diagonal
product-load of the block primes is `≥ 1/2`, for squarefree `b ≥ 3` and a finite
obstruction set `T` there is a block scale `k₀` and a finite batch `Q` of products
of two distinct block primes, avoiding `T`, whose reciprocal load lands in the
common-θ window `[3/(2b), 3/b]`.
-/
lemma exists_blockAligned_mass_batch_of (b : ℕ) (hb : 3 ≤ b) (T : Finset ℕ)
    (k1 : ℕ)
    (hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) :
    ∃ (k0 : ℕ) (Q : Finset ℕ),
      (∀ e ∈ Q, ∃ p q, p ∈ blockPrimes k0 ∧ q ∈ blockPrimes k0 ∧ p < q ∧ e = p * q) ∧
      (∀ e ∈ Q, e ∉ T) ∧
      3 / (2 * (b : ℝ)) ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ∧
        ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ≤ 3 / (b : ℝ) := by
  -- Choose `k0 := max k1 (T.sup id + b + 1)`.
  set k0 := max k1 (T.sup id + b + 1) with hk0_def;
  -- Choose `target := 3/(2*(b:ℝ))` and `gap := 3/(2*(b:ℝ))`.
  set target : ℝ := 3 / (2 * b) with htarget_def
  set gap : ℝ := 3 / (2 * b) with hgap_def;
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset ℕ, Q ⊆ ((blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2)).image (fun pq => pq.1 * pq.2) ∧ target ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ∧ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ≤ target + gap := by
    apply exists_subset_recip_window;
    · positivity;
    · positivity;
    · simp +zetaDelta at *;
      intros e x y hx hy hxy hlt heq
      have h_bound : (x * y : ℝ) ≥ 2 ^ k0 * 2 ^ k0 := by
        exact_mod_cast Nat.mul_le_mul ( blockPrimes_ge hx ) ( blockPrimes_ge hy );
      rw [ inv_eq_one_div, div_lt_div_iff₀ ] <;> norm_cast at * <;> try positivity;
      · have h_bound : 2 ^ k0 ≥ k0 := by
          exact le_of_lt ( Nat.recOn k0 ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] );
        nlinarith [ show k0 ≥ T.sup id + b + 1 by exact le_max_right _ _ ];
      · exact heq ▸ Nat.mul_pos ( Nat.Prime.pos ( blockPrimes_prime hx ) ) ( Nat.Prime.pos ( blockPrimes_prime hy ) );
    · rw [ Finset.sum_image ];
      · norm_num +zetaDelta at *;
        exact le_trans ( by rw [ div_le_iff₀ ] <;> norm_num <;> linarith [ show ( b : ℝ ) ≥ 3 by norm_cast ] ) ( hload _ ( le_max_left _ _ ) );
      · convert blockPrimes_pair_prod_injOn k0 using 1;
  refine' ⟨ k0, Q, _, _, hQ.2.1, _ ⟩;
  · intro e he; have := hQ.1 he; aesop;
  · intro e he hT
    have h_e_ge_4k0 : e ≥ 4 ^ k0 := by
      obtain ⟨ pq, hpq, rfl ⟩ := Finset.mem_image.mp ( hQ.1 he );
      have h_e_ge : pq.1 ≥ 2 ^ k0 ∧ pq.2 ≥ 2 ^ k0 := by
        simp +zetaDelta at *;
        exact ⟨ blockPrimes_ge hpq.1.1, blockPrimes_ge hpq.1.2.1 ⟩;
      exact le_trans ( by rw [ show ( 4 : ℕ ) ^ k0 = 2 ^ k0 * 2 ^ k0 by rw [ ← mul_pow ] ; norm_num ] ) ( Nat.mul_le_mul h_e_ge.1 h_e_ge.2 )
    have h_e_gt_T_sup : e > T.sup id := by
      have h_e_gt_T_sup : 4 ^ k0 > k0 := by
        exact Nat.recOn k0 ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 4 zero_lt_four ] ;
      linarith [ Nat.le_max_right k1 ( T.sup id + b + 1 ) ]
    exact absurd h_e_gt_T_sup (by
    exact not_lt_of_ge ( Finset.le_sup ( f := id ) hT ));
  · convert hQ.2.2 using 1 ; ring

/-! ## T2 and T3 — unconditional forms (fed from the dyadic-Mertens axiom) -/

/-- **T2.**  For all large `k₀`, the off-diagonal (`p<q`) reciprocal product-load
of the block primes is at least `1/2`.  This is `blockPrimes_product_load_ge_of`
with the Mertens reciprocal-sum lower bound supplied by
`GlobalControl.dyadic_mertens_cumulative`. -/
lemma blockPrimes_product_load_ge :
    ∃ k1 : ℕ, 5 ≤ k1 ∧ ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤
        ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq => pq.1 < pq.2),
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
  obtain ⟨k1, h5, hk⟩ := GlobalControl.dyadic_mertens_cumulative
  refine ⟨k1, h5, fun k0 hle => ?_⟩
  exact blockPrimes_product_load_ge_of k0 (le_trans h5 hle) (hk k0 hle)

/-- **T3.**  For squarefree `b ≥ 3` and a finite obstruction set `T`, there is a
block scale `k₀` and a finite batch `Q` of products of two distinct block primes,
avoiding `T`, whose reciprocal load lands in the common-θ window `[3/(2b), 3/b]`.
This is the `R2-mass` input to the R2 arc construction.

(The `Squarefree b` hypothesis is requested by the R2 interface; the load
bookkeeping uses only `b ≥ 3`.) -/
lemma exists_blockAligned_mass_batch (b : ℕ) (hb : 3 ≤ b) (_hbsf : Squarefree b)
    (T : Finset ℕ) :
    ∃ (k0 : ℕ) (Q : Finset ℕ),
      (∀ e ∈ Q, ∃ p q, p ∈ blockPrimes k0 ∧ q ∈ blockPrimes k0 ∧ p < q ∧ e = p * q) ∧
      (∀ e ∈ Q, e ∉ T) ∧
      3 / (2 * (b : ℝ)) ≤ ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ∧
        ∑ e ∈ Q, (1 : ℝ) / (e : ℝ) ≤ 3 / (b : ℝ) := by
  obtain ⟨k1, _, hload⟩ := blockPrimes_product_load_ge
  exact exists_blockAligned_mass_batch_of b hb T k1 hload

end CircleMethod

end
