import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Complex.ExponentialBounds
import RequestProject.Core.Asymptotics
import RequestProject.Core.FiniteInterval
import RequestProject.LocalEnergy.CrossLabelEnergy
import RequestProject.LocalEnergy.DominantLabel.Basic

/-!
# Energy forcing without a dominant label

A covering of the residue labels, cross-label dispersion, and class-mass
accounting force energy of order `X / (log X)^3` whenever no label dominates.
-/

open Finset

namespace LocalEnergy

open scoped Classical

/-! ## Energy forcing without a dominant label -/

/-! ### Covering construction -/

/-
**Pair count (`29 §4`).**  The number of ordered pairs `p < q` whose centered
    representative exceeds `B` is `≤ 16 R X⁴ / B²`: each such pair contributes
    `(H/(pq))² > (B/(4X²))²` to `QP ≤ R`, using `pq ≤ 4X²`.
-/
lemma large_crt_pair_count
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (a : BlockAssignment P) (R : ℝ) (hQ : QP P a ≤ R)
    (B : ℝ) (hB : 0 < B) :
    (((orderedPrimePairsA P).filter (fun pq =>
        B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ)
      ≤ 16 * R * (X:ℝ)^4 / B^2 := by
  rw [ le_div_iff₀ ( by positivity ) ];
  have h_card_bound : ∀ pq ∈ orderedPrimePairsA P, B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)| → ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)/((pq.1.1:ℝ)*pq.2.1))^2 ≥ B^2/(16*X^4) := by
    intros pq hpq hBpq
    have h_bound : (pq.1.1 : ℝ) * (pq.2.1 : ℝ) ≤ 4 * (X : ℝ) ^ 2 := by
      exact_mod_cast by nlinarith [ hP _ pq.1.2, hP _ pq.2.2 ] ;
    rw [ div_pow, ge_iff_le, div_le_div_iff₀ ] <;> try positivity;
    · exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by positivity ) h_bound 2 ) ( by positivity ) ) ( by nlinarith [ show ( |↑ ( crtRepr ( pq.1 : ℕ ) ( pq.2 : ℕ ) ( a pq.1 ) ( a pq.2 ) )| : ℝ ) ^ 2 = ( ↑ ( crtRepr ( pq.1 : ℕ ) ( pq.2 : ℕ ) ( a pq.1 ) ( a pq.2 ) ) : ℝ ) ^ 2 by rw [ sq_abs ], abs_mul_abs_self ( ( crtRepr ( pq.1 : ℕ ) ( pq.2 : ℕ ) ( a pq.1 ) ( a pq.2 ) : ℤ ) : ℝ ), pow_le_pow_left₀ ( by positivity ) hBpq.le 2 ] );
    · exact sq_pos_of_pos ( mul_pos ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ pq.1.2 |>.1 ) ) ) ( Nat.cast_pos.mpr ( Nat.Prime.pos ( hP _ pq.2.2 |>.1 ) ) ) );
  have h_sum_bound : ∑ pq ∈ orderedPrimePairsA P, ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)/((pq.1.1:ℝ)*pq.2.1))^2 ≥ ∑ pq ∈ orderedPrimePairsA P, if B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2):ℝ)| then B^2/(16*X^4) else 0 := by
    exact Finset.sum_le_sum fun x hx => by split_ifs <;> [ exact h_card_bound x hx ‹_›; exact by positivity ] ;
  have h_indicator :
      (∑ pq ∈ orderedPrimePairsA P,
          if B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|
          then B ^ 2 / (16 * X ^ 4) else 0) =
        (((orderedPrimePairsA P).filter (fun pq =>
          B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) *
            (B ^ 2 / (16 * X ^ 4)) := by
    rw [← Finset.sum_filter]
    simp
  have h_count_energy :
      (((orderedPrimePairsA P).filter (fun pq =>
        B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) *
          (B ^ 2 / (16 * X ^ 4)) ≤ R := by
    rw [← h_indicator]
    exact h_sum_bound.trans (by simpa [QP] using hQ)
  have hscale_pos : 0 < (16 : ℝ) * X ^ 4 := by positivity
  calc
    (((orderedPrimePairsA P).filter (fun pq =>
        B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) * B ^ 2 =
      ((((orderedPrimePairsA P).filter (fun pq =>
          B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card : ℝ) *
          (B ^ 2 / (16 * X ^ 4))) * (16 * X ^ 4) := by
        field_simp
    _ ≤ R * (16 * X ^ 4) := mul_le_mul_of_nonneg_right h_count_energy hscale_pos.le
    _ = 16 * R * X ^ 4 := by ring

/-
**Double counting (`29 §4`).**  The sum over base points of the high-`H`
    neighbour counts equals twice the (ordered `p<q`) pair count, since the
    relation `q ≠ p0 ∧ B < |H_{p0 q}|` is symmetric (`crtRepr_symm`).
-/
lemma large_crt_basepoint_sum
    (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p)
    (a : BlockAssignment P) (B : ℝ) :
    (∑ p0 ∈ P.attach, (P.attach.filter (fun q => q ≠ p0 ∧
        B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card)
      = 2 * ((orderedPrimePairsA P).filter (fun pq =>
          B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card := by
  have h_sum_eq : ∑ p0 ∈ P.attach, (Finset.filter (fun q => q ≠ p0 ∧ B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|) P.attach).card = (Finset.filter (fun pq => pq.1 ≠ pq.2 ∧ B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (P.attach ×ˢ P.attach)).card := by
    simp +decide only [card_filter];
    erw [Finset.sum_product] ; simp +decide;
    simp +decide only [eq_comm];
  have h_symm : Finset.filter (fun pq => pq.1 ≠ pq.2 ∧ B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (P.attach ×ˢ P.attach) = Finset.image (fun pq => (pq.2, pq.1)) (Finset.filter (fun pq => B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (orderedPrimePairsA P)) ∪ Finset.filter (fun pq => B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|) (orderedPrimePairsA P) := by
    ext ⟨p, q⟩; simp [orderedPrimePairsA];
    constructor <;> intro h;
    · cases lt_or_gt_of_ne h.1 <;> [ exact Or.inr ⟨ by assumption, h.2 ⟩ ; exact Or.inl ⟨ q, q.2, p, p.2, ⟨ by assumption, by simpa only [ crtRepr_symm _ _ ( hP _ p.2 ) ( hP _ q.2 ) ( by aesop ) ] using h.2 ⟩, rfl, rfl ⟩ ];
    · grind +suggestions;
  rw [ h_sum_eq, h_symm, Finset.card_union_of_disjoint ];
  · rw [ two_mul, Finset.card_image_of_injective ] ; norm_num [ Function.Injective ];
  · simp +contextual [ Finset.disjoint_left, orderedPrimePairsA ];
    lia

/-
**Base point (`29 §4`).**  Averaging over base points, some `p0 ∈ P` has at
    most `32 R X⁴ / (B² N)` vertices `q` with `|H_{p0 q}| > B`.  Indeed the sum over
    base points of these counts equals twice the pair count (`large_crt_pair_count`,
    via the symmetry `crtRepr_symm`), so the minimum is `≤` the average.
-/
lemma exists_sparse_crt_basepoint
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hPne : 0 < P.card)
    (a : BlockAssignment P) (R : ℝ) (_hR : 0 ≤ R) (hQ : QP P a ≤ R)
    (B : ℝ) (hB : 0 < B) :
    ∃ p0 : P, p0 ∈ P.attach ∧
      ((P.attach.filter (fun q => q ≠ p0 ∧
          B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ)
        ≤ 32 * R * (X:ℝ)^4 / (B^2 * P.card) := by
  have h_avg : (∑ p0 ∈ P.attach, (P.attach.filter (fun q => q ≠ p0 ∧ B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) ≤ 2 * (16 * R * (X:ℝ)^4 / B^2) := by
    have h_avg : (∑ p0 ∈ P.attach, (P.attach.filter (fun q => q ≠ p0 ∧ B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) = 2 * ((orderedPrimePairsA P).filter (fun pq => B < |(crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ)|)).card := by
      convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( large_crt_basepoint_sum P ( fun p hp => ( hP p hp ).1 ) a B ) using 1; all_goals norm_cast;
    exact h_avg.symm ▸ mul_le_mul_of_nonneg_left ( mod_cast large_crt_pair_count X hX P hP a R hQ B hB ) zero_le_two;
  contrapose! h_avg;
  convert Finset.sum_lt_sum_of_nonempty ( Finset.card_pos.mp <| by simpa [ Finset.card_attach ] using hPne ) h_avg using 1 ; norm_num ; ring_nf;
  norm_num [ hPne.ne' ]

/-
**Power-mean energy lower bound (combinatorial heart of `29 §6`).**  For a
    family of nonnegative class sizes `x` over labels `L`, with a maximal label
    `nstar`, the off-diagonal cubic form `∑_{n≠n'} x_n³ x_{n'}` is at least
    `M₂⁴ / |L|²`, where `M₂ = ∑_{n≠nstar} x_n`.  (Uses `S₄ ≤ x_{nstar}·S₃` and the
    power-mean inequality `∑ x_n³ ≥ (∑ x_n)³ / |L|²`.)
-/
lemma sum_cube_offdiag_ge {ι : Type*} [DecidableEq ι]
    (L : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ L, 0 ≤ x i)
    (nstar : ι) (hns : nstar ∈ L) (hmax : ∀ i ∈ L, x i ≤ x nstar) :
    (∑ n ∈ L \ {nstar}, x n)^4 / (L.card:ℝ)^2
      ≤ ∑ n ∈ L, ∑ n' ∈ L \ {n}, (x n)^3 * (x n') := by
  -- By the properties of sums and the power mean inequality, we can simplify the expression.
  have h_simplify : (∑ n ∈ L, ∑ n' ∈ L \ {n}, (x n)^3 * (x n')) ≥ (∑ n ∈ L, (x n)^3) * (∑ n ∈ L \ {nstar}, (x n)) := by
    have h_simplify : (∑ n ∈ L, ∑ n' ∈ L \ {n}, (x n)^3 * (x n')) = (∑ n ∈ L, (x n)^3 * (∑ n' ∈ L \ {n}, (x n'))) := by
      simp +decide only [Finset.mul_sum _ _ _];
    rw [ h_simplify, Finset.sum_mul _ _ _ ];
    refine' Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left _ ( pow_nonneg ( hx i hi ) 3 );
    by_cases hi' : i = nstar <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
    linarith [ hmax i hi ];
  -- Apply the power mean inequality to the sum of cubes.
  have h_power_mean : (∑ n ∈ L \ {nstar}, x n) ^ 3 / (L.card - 1 : ℝ) ^ 2 ≤ ∑ n ∈ L \ {nstar}, x n ^ 3 := by
    have h_power_mean : ∀ (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i), s.Nonempty → (∑ i ∈ s, f i) ^ 3 / s.card ^ 2 ≤ ∑ i ∈ s, f i ^ 3 := by
      intro s f hf hs_nonempty
      have h_power_mean : (∑ i ∈ s, f i ^ 3) / s.card ≥ ((∑ i ∈ s, f i) / s.card) ^ 3 := by
        have := @Real.rpow_arith_mean_le_arith_mean_rpow;
        specialize this s ( fun _i => 1 / s.card ) ( fun _i => f _i ) ; simp_all +decide [ div_eq_inv_mul, Finset.mul_sum _ _ _ ];
        exact_mod_cast this ( mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr hs_nonempty.card_pos.ne' ) ) ( show 1 ≤ ( 3 : ℝ ) by norm_num );
      contrapose! h_power_mean;
      convert div_lt_div_iff_of_pos_right ( Nat.cast_pos.mpr hs_nonempty.card_pos ) |>.2 h_power_mean using 1 ; ring;
    by_cases hL : L = {nstar} <;> simp_all +decide;
    convert h_power_mean ( L \ { nstar } ) x ( fun i hi => hx i ( Finset.mem_sdiff.mp hi |>.1 ) ) ( Finset.nonempty_of_ne_empty ( by aesop ) ) using 1 <;> simp +decide [*, Finset.card_sdiff];
    rw [ Nat.cast_pred ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) ];
  by_cases hL : L.card = 1 <;> simp_all +decide [ Finset.sdiff_singleton_eq_erase ];
  · rw [ Finset.card_eq_one ] at hL ; aesop;
  · refine' le_trans _ ( h_simplify.trans _ );
    · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( show ∑ n ∈ L, x n ^ 3 ≥ ( ∑ n ∈ L, x n - x nstar ) ^ 3 / ( L.card - 1 : ℝ ) ^ 2 from _ ) ( sub_nonneg.mpr <| Finset.single_le_sum ( fun i _ => hx i ‹_› ) hns ) );
      · rw [ div_mul_eq_mul_div, div_le_div_iff₀ ];
        · exact mul_le_mul_of_nonneg_left ( by nlinarith only [ show ( L.card : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) ( Ne.symm hL ) ] ) ( mul_nonneg ( pow_nonneg ( sub_nonneg.mpr <| Finset.single_le_sum ( fun i _ => hx i ‹_› ) hns ) _ ) <| sub_nonneg.mpr <| Finset.single_le_sum ( fun i _ => hx i ‹_› ) hns );
        · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) );
        · exact sq_pos_of_pos ( sub_pos_of_lt ( mod_cast lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ nstar, hns ⟩ ) ( Ne.symm hL ) ) );
      · exact h_power_mean.trans ( sub_le_self _ ( pow_nonneg ( hx _ hns ) _ ) );
    · rfl

/-
**Short list cardinality (`29 §4`).**  The covered labels `n = H_{p0 q}` lie in
    `[-B, B]` and all share the residue `a_{p0}` modulo `p0 ≥ X`, so there are at
    most `2B/X + 2` of them.
-/
lemma crt_label_shortlist_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (a : BlockAssignment P) (p0 : P) (B : ℝ) (hB : 0 ≤ B) :
    (((P.attach.filter (fun q => q ≠ p0 ∧
        |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B)).image
          (fun q => crtRepr p0.1 q.1 (a p0) (a q))).card : ℝ) ≤ 2*B/X + 2 := by
  have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (2 * B / (p0.1 : ℝ) + 2 : ℝ) := by
    have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (2 * B / (p0.1 : ℝ) + 2 : ℝ) := by
      have h_phi : ∀ q : P, q ≠ p0 → |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B → ∃ k : ℤ, |(k : ℝ)| ≤ B / (p0.1 : ℝ) + 1 / 2 ∧ (crtRepr p0.1 q.1 (a p0) (a q) : ℤ) = (k * (p0.1 : ℤ) + (a p0).valMinAbs) := by
        intro q hq hqB
        obtain ⟨k, hk⟩ : ∃ k : ℤ, (crtRepr p0.1 q.1 (a p0) (a q) : ℤ) = k * (p0.1 : ℤ) + (a p0).valMinAbs := by
          have h_crtRepr_congr_left : (crtRepr p0.1 q.1 (a p0) (a q) : ZMod p0.1) = (a p0).valMinAbs := by
            convert crtRepr_congr_left p0.1 q.1 ( a p0 ) ( a q ) _ using 1;
            · convert ZMod.coe_valMinAbs ( a p0 ) using 1;
            · exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := Nat.coprime_primes ( hP p0 p0.2 |>.1 ) ( hP q q.2 |>.1 ) ; aesop );
          exact ⟨ ( crtRepr p0.1 q.1 ( a p0 ) ( a q ) - ( a p0 ).valMinAbs ) / p0.1, by rw [ Int.ediv_mul_cancel ( by rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop ) ] ; ring ⟩;
        refine' ⟨ k, _, hk ⟩;
        rw [ div_add_div, le_div_iff₀ ] <;> norm_num;
        · have h_abs_k : |(k : ℝ) * (p0.1 : ℝ) + (a p0).valMinAbs| ≤ B := by
            convert hqB using 1 ; norm_cast ; aesop;
          have h_abs_k : |(a p0).valMinAbs| ≤ (p0.1 : ℝ) / 2 := by
            have := ZMod.natAbs_valMinAbs_le ( a p0 );
            rw [ le_div_iff₀ ] <;> norm_cast;
            linarith! [ Nat.div_mul_le_self p0 2 ];
          norm_num [ abs_le ] at *;
          cases abs_cases ( k : ℝ ) <;> nlinarith [ show ( p0 : ℝ ) ≥ 1 by exact_mod_cast Nat.Prime.pos ( hP p0 p0.2 |>.1 ) ];
        · exact Nat.Prime.pos ( hP _ p0.2 |>.1 );
        · exact Nat.Prime.ne_zero ( hP _ p0.2 |>.1 )
      have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (2 * ⌊B / (p0.1 : ℝ) + 1 / 2⌋ + 1 : ℝ) := by
        have h_card_image : ((Finset.image (fun q : P => (crtRepr p0.1 q.1 (a p0) (a q) : ℤ)) (Finset.filter (fun q : P => q ≠ p0 ∧ |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B) Finset.univ)).card : ℝ) ≤ (Finset.image (fun k : ℤ => k * (p0.1 : ℤ) + (a p0).valMinAbs) (Finset.Icc (-⌊B / (p0.1 : ℝ) + 1 / 2⌋) ⌊B / (p0.1 : ℝ) + 1 / 2⌋)).card := by
          refine' Nat.cast_le.mpr ( Finset.card_le_card _ );
          simp_all +decide [ Finset.subset_iff ];
          rintro x q hq hq' hq'' rfl; obtain ⟨ k, hk₁, hk₂ ⟩ := h_phi q hq hq' hq''; exact ⟨ k, ⟨ neg_le_of_abs_le <| Int.le_floor.mpr <| by simpa using hk₁, le_of_abs_le <| Int.le_floor.mpr <| by simpa using hk₁ ⟩, hk₂.symm ⟩ ;
        refine le_trans h_card_image ?_;
        rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, NeZero.ne ];
        norm_cast ; linarith [ Int.toNat_of_nonneg ( by linarith [ Int.floor_nonneg.mpr ( show 0 ≤ B / ( p0 : ℝ ) + 1 / 2 by positivity ) ] : 0 ≤ ⌊B / ( p0 : ℝ ) + 1 / 2⌋ + 1 + ⌊B / ( p0 : ℝ ) + 1 / 2⌋ ) ];
      refine le_trans h_card_image ?_;
      ring_nf;
      linarith [ Int.floor_le ( 1 / 2 + B * ( p0 : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( 1 / 2 + B * ( p0 : ℝ ) ⁻¹ ) ];
    convert h_card_image using 1;
  refine le_trans h_card_image ?_;
  gcongr ; aesop

/-
**Label residue (`29 §4`).**  Every covered vertex `q ≠ p0` carries the residue
    of its label: `a q = (lab q : ZMod q)` (by `crtRepr_congr_right`).
-/
lemma crtRepr_eq_label_residue (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p) (a : BlockAssignment P) (p0 q : P) (hq : q ≠ p0) :
    a q = ((crtRepr p0.1 q.1 (a p0) (a q) : ℤ) : ZMod q.1) := by
  have h_coprime : Nat.Coprime p0.1 q.1 := by
    exact (Nat.coprime_primes ( hP _ p0.2 ) ( hP _ q.2 )).mpr ( by contrapose! hq; aesop );
  -- Apply `crtRepr_congr_right` to the coprime pair.
  have := crtRepr_congr_right p0.1 q.1 (a p0) (a q) h_coprime;
  aesop

/-
**Cross-energy double count (`29 §6`).**  Summing the cross energies of
    ordered pairs of distinct label classes (a partition of `S` by `f`) is at most
    `2·Q_P`, since each unordered vertex pair is counted at most twice and the
    energy is symmetric (`crtRepr_symm`).
-/
set_option maxHeartbeats 1000000 in
lemma crossLabel_energy_sum_le
    (P : Finset ℕ) [∀ p : P, NeZero p.1] (hP : ∀ p ∈ P, Nat.Prime p)
    (a : BlockAssignment P) (S : Finset P) (hS : S ⊆ P.attach)
    (f : P → ℤ) (L : Finset ℤ) :
    ∑ n ∈ L, ∑ n' ∈ L \ {n},
        (∑ p ∈ S.filter (fun q => f q = n), ∑ q ∈ S.filter (fun q => f q = n'),
          ((crtRepr p.1 q.1 (a p) (a q) : ℝ) / ((p.1:ℝ) * q.1))^2)
      ≤ 2 * QP P a := by
  have h_symm : (∑ n ∈ L, ∑ n' ∈ L \ {n}, ∑ p ∈ S.filter (fun q => f q = n), ∑ q ∈ S.filter (fun q => f q = n'), ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2) ≤
               (∑ p ∈ S, ∑ q ∈ S, if f p ≠ f q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) := by
                 have h_symm : (∑ n ∈ L, ∑ n' ∈ L \ {n}, ∑ p ∈ S.filter (fun q => f q = n), ∑ q ∈ S.filter (fun q => f q = n'), ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2) =
                                (∑ p ∈ S.filter (fun q => f q ∈ L), ∑ q ∈ S.filter (fun q => f q ∈ L ∧ f q ≠ f p), ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2) := by
                                  simp +decide only [sum_sigma'];
                                  refine' Finset.sum_bij ( fun x hx => ⟨ x.snd.snd.fst, x.snd.snd.snd ⟩ ) _ _ _ _ <;> simp +decide; all_goals grind;
                 simp_all +decide [ Finset.sum_ite ];
                 refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _;
                 exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum_of_subset_of_nonneg ( fun j hj => by aesop ) fun _ _ _ => sq_nonneg _;
  -- Apply the fact that the sum of the cross energies is less than or equal to twice the sum of the energies.
  have h_cross_le_2QP : (∑ p ∈ S, ∑ q ∈ S, if p ≠ q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) ≤ 2 * QP P a := by
    have h_cross_le_2QP : (∑ p ∈ P.attach, ∑ q ∈ P.attach, if p ≠ q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) = 2 * QP P a := by
      have h_cross_le_2QP : (∑ p ∈ P.attach, ∑ q ∈ P.attach, if p < q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) = QP P a := by
        unfold QP; simp +decide [ Finset.sum_ite ] ;
        simp +decide [ Finset.sum_filter, Finset.sum_product, orderedPrimePairsA ];
      have h_cross_le_2QP : (∑ p ∈ P.attach, ∑ q ∈ P.attach, if p > q then ((crtRepr p q (a p) (a q) : ℝ) / ((p:ℝ) * (q:ℝ)))^2 else 0) = QP P a := by
        rw [ ← h_cross_le_2QP, Finset.sum_comm ];
        refine' Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => _;
        split_ifs <;> simp_all +decide [ mul_comm ];
        rw [ crtRepr_symm ];
        · exact hP _ q.2;
        · exact hP _ p.2;
        · exact ne_of_gt ‹_›;
      convert congr_arg₂ ( · + · ) ‹ ( ∑ p ∈ P.attach, ∑ q ∈ P.attach, if p < q then ( crtRepr p q ( a p ) ( a q ) / ( p * q : ℝ ) ) ^ 2 else 0 ) = QP P a › ‹ ( ∑ p ∈ P.attach, ∑ q ∈ P.attach, if p > q then ( crtRepr p q ( a p ) ( a q ) / ( p * q : ℝ ) ) ^ 2 else 0 ) = QP P a › using 1;
      · simp +decide only [← sum_add_distrib];
        refine' Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => _;
        grind +revert;
      · ring;
    rw [ ← h_cross_le_2QP ];
    refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => Finset.sum_nonneg fun _ _ => by positivity );
    exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum_of_subset_of_nonneg ( hS hi |> fun h => Finset.subset_univ _ ) fun _ _ _ => by positivity;
  refine le_trans h_symm <| h_cross_le_2QP.trans' <| Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_;
  split_ifs <;> norm_num ; aesop;
  positivity

/-
**Energy core (`29 §6`).**  For a covered set `S` (all `q ≠ p0` with
    `|H_{p0 q}| ≤ B`) and a set `L` of substantial labels (each class
    `Cls n = S.filter (lab = n)` has `≥ 32(B/X+1)` and `≥ 8` members), cross-label dispersion
    applied to every ordered pair of distinct classes and summed (bounded by `2Q_P`
    via `crossLabel_energy_sum_le`) gives a lower bound on `R` by the off-diagonal
    cubic form of the class sizes.
-/
set_option maxHeartbeats 1000000 in
lemma class_partition_energy_lower_bound
    (X : ℕ) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
    (a : BlockAssignment P) (p0 : P) (B : ℝ) (_hB0 : 0 ≤ B) (hBX : B ≤ (X:ℝ)^2/4)
    (S : Finset P) (hScov : ∀ q ∈ S, q ≠ p0 ∧
        |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)| ≤ B)
    (L : Finset ℤ)
    (hLsub : ∀ n ∈ L, (32*(B/X+1):ℝ) ≤
        ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)).card : ℝ))
    (hL8 : ∀ n ∈ L, (8:ℝ) ≤
        ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)).card : ℝ))
    (R : ℝ) (hQ : QP P a ≤ R)
    (cE : ℝ) (_hcE0 : 0 < cE)
    (hcE : ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1]
        (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 →
        ∀ (C C' : Finset Q),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) →
          Disjoint C C' →
          (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) →
          cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2) :
    cE/(X:ℝ)^2 *
        (∑ n ∈ L, ∑ n' ∈ L \ {n},
          ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)).card : ℝ)^3 *
            ((S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n')).card : ℝ))
      ≤ 2 * R := by
  rw [ Finset.mul_sum _ _ _ ];
  have h_cross_sum : ∀ n n' : ℤ, n ∈ L → n' ∈ L → n ≠ n' → cE / (X:ℝ)^2 * (Finset.card (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)) : ℝ)^3 * (Finset.card (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n')) : ℝ) ≤ ∑ q ∈ S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n), ∑ q' ∈ S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n'), ((crtRepr q.1 q'.1 (a q) (a q') : ℝ) / ((q.1:ℝ) * q'.1))^2 := by
    intros n n' hn hn' hne;
    specialize hcE X P a n n' B hne ?_ ?_ ?_ (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n)) (S.filter (fun q => crtRepr p0.1 q.1 (a p0) (a q) = n'));
    · obtain ⟨q, hq⟩ : ∃ q ∈ S, crtRepr p0.1 q.1 (a p0) (a q) = n := by
        contrapose! hL8;
        exact ⟨ n, hn, by rw [ Finset.filter_eq_empty_iff.mpr hL8 ] ; norm_num ⟩;
      simpa [ ← hq.2 ] using hScov q hq.1 |>.2;
    · obtain ⟨ q, hq ⟩ := Finset.card_pos.mp ( by exact_mod_cast ( by linarith [ hL8 n' hn' ] : ( 0 : ℝ ) < Finset.card ( Finset.filter ( fun q : P => crtRepr p0.1 q.1 ( a p0 ) ( a q ) = n' ) S ) ) );
      grind +qlia;
    · exact hBX;
    · convert hcE _ _ _ ( hLsub n hn ) ( hL8 n' hn' ) _ _ using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      · exact fun p hp hp' hp'' => ⟨ hP p hp |>.1, hP p hp |>.2.1, by linarith [ hP p hp |>.2.2 ] ⟩;
      · exact fun p hp hp' hp'' => ⟨ hP p hp |>.1, hP p hp |>.2.1, by linarith [ hP p hp |>.2.2 ] ⟩;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by aesop;
      · intro p hp hpS hpn
        have h_eq : a ⟨p, hp⟩ = ((crtRepr p0.1 p (a p0) (a ⟨p, hp⟩) : ℤ) : ZMod p) := by
          convert crtRepr_eq_label_residue P ( fun p hp => ( hP p hp ).1 ) a p0 ⟨ p, hp ⟩ ( hScov _ hpS |>.1 ) using 1
        rw [h_eq]
        simp [hpn];
      · intro p hp hpS hp'; specialize hScov ⟨ p, hp ⟩ hpS; simp_all +decide [ Finset.disjoint_left ] ;
        convert crtRepr_eq_label_residue P ( fun p hp => hP p hp |>.1 ) a p0 ⟨ p, hp ⟩ hScov.1 using 1;
        · exact hp'.symm ▸ rfl;
        · exact fun p => ⟨ Nat.Prime.ne_zero ( hP p p.2 |>.1 ) ⟩;
  refine' le_trans _ ( le_trans ( crossLabel_energy_sum_le P ( fun p hp => ( hP p hp ).1 ) a S ( Finset.subset_univ _ ) ( fun q => crtRepr p0.1 q.1 ( a p0 ) ( a q ) ) L ) _ );
  · exact Finset.sum_le_sum fun i hi => by simpa only [ mul_assoc, Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun j hj => h_cross_sum i j hi ( Finset.mem_sdiff.mp hj |>.1 ) ( by rintro rfl; exact Finset.mem_sdiff.mp hj |>.2 <| Finset.mem_singleton_self _ ) ;
  · exact mul_le_mul_of_nonneg_left hQ zero_le_two

/-
**Zero energy is dominant.**  If `Q_P(a) = 0` then every cross representative
    vanishes, so `a_p ≡ 0` for all `p`, and `a` is `0`-dominant.
-/
lemma zero_label_dominant_of_large_class (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (a : BlockAssignment P) (ρ : ℝ) (hρ : 0 ≤ ρ) (hQ0 : QP P a = 0) :
    HasDominantLabel X P a ρ := by
  -- Since $a_p = 0$ for all $p \in P$, we can choose $m = 0$.
  use 0; simp;
  have h_all_zero : ∀ p ∈ P.attach, a p = 0 := by
    intro p hp
    have h_cross : ∀ q ∈ P.attach, q ≠ p → crtRepr (p.1) (q.1) (a p) (a q) = 0 := by
      intro q hq hqp
      have h_cross : ((crtRepr (p.1) (q.1) (a p) (a q) : ℝ) / ((p.1 : ℝ) * (q.1 : ℝ)))^2 = 0 := by
        have h_cross : ∀ pq ∈ orderedPrimePairsA P, ((crtRepr pq.1.1 pq.2.1 (a pq.1) (a pq.2) : ℝ) / ((pq.1.1 : ℝ) * (pq.2.1 : ℝ)))^2 = 0 := by
          exact fun pq hpq => by rw [ QP ] at hQ0; exact Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 hQ0 pq hpq;
        cases lt_or_gt_of_ne hqp <;> simp_all +decide [ orderedPrimePairsA ];
        grind +suggestions;
      simp_all +decide [ div_eq_iff, NeZero.ne ];
    obtain ⟨q, hq⟩ : ∃ q ∈ P.attach, q ≠ p := by
      exact Finset.exists_mem_ne (by simpa [Finset.card_attach] using (show 1 < P.card by omega)) p;
    have := crtRepr_congr_left p.1 q.1 ( a p ) ( a q ) ( Nat.coprime_primes ( hP p p.2 |>.1 ) ( hP q q.2 |>.1 ) |>.2 <| by aesop ) ; aesop;
  exact ⟨ by positivity, by rw [ Finset.filter_true_of_mem h_all_zero ] ; norm_num; nlinarith ⟩

/-
**Covering dichotomy (`29 §6`).**  With base point `p0`, threshold `B`, and the
    exception count controlled (`hexc`), either the energy is large (disjunct 1,
    from the substantial-class energy) or the tiny-class bound forces `B/X` large
    (disjunct 2). This is the structural heart of nondominant forcing; the final parameter
    chase plugs in `B = √(A²R)·X²/N`.
-/
set_option maxHeartbeats 2000000 in
lemma label_covering_energy_dichotomy
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hN : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (hnd : ¬ HasDominantLabel X P a ρ)
    (R : ℝ) (hR0 : 0 < R) (hQ : QP P a ≤ R)
    (p0 : P) (B : ℝ) (hB0 : 0 < B) (hBX : B ≤ (X:ℝ)^2/4)
    (hexc : ((P.attach.filter (fun q => q ≠ p0 ∧
        B < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) ≤ ρ * (P.card:ℝ)/8)
    (h1 : 1 ≤ ρ * (P.card:ℝ)/8)
    (cE : ℝ) (hcE0 : 0 < cE)
    (hcE : ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1]
        (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 →
        ∀ (C C' : Finset Q),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) →
          Disjoint C C' →
          (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) →
          cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2) :
    cE * (ρ*(P.card:ℝ)/2)^4 / (2 * (X:ℝ)^2 * (2*B/X+2)^2) ≤ R ∨
      ρ*(P.card:ℝ)/4 < (2*B/X+2)*(32*(B/X+1)+8) := by
  -- Define the relevant quantities for the proof.
  set N := (P.card : ℝ)
  set lab := fun q : P => crtRepr p0.1 q.1 (a p0) (a q)
  set S := P.attach.filter (fun q => q ≠ p0 ∧ |(lab q : ℝ)| ≤ B)
  set allLabels := S.image lab
  set s0 := 32 * (B / X + 1) + 8
  set Cls := fun n => S.filter (fun q => lab q = n)
  set Lsub := allLabels.filter (fun n => s0 ≤ ((Cls n).card : ℝ))
  set exc' := P.attach.filter (fun q => q ≠ p0 ∧ B < |(lab q : ℝ)|)
  set k0 := allLabels.card;
  -- Preliminary bounds.
  have hk0 : (k0 : ℝ) ≤ 2 * B / X + 2 := by
    convert crt_label_shortlist_bound X hX P hP a p0 B hB0.le using 1
  have hS_card : (S.card : ℝ) ≥ N - 1 - ρ * N / 8 := by
    have hS_card : (S.card : ℝ) + (exc'.card : ℝ) = (P.card - 1 : ℝ) := by
      rw [ ← Nat.cast_add, ← Finset.card_union_of_disjoint ];
      · rw [ show S ∪ exc' = Finset.filter ( fun q => q ≠ p0 ) P.attach from ?_ ];
        · simp +decide [ Finset.filter_ne' ];
          rw [ Nat.cast_pred ( by linarith ) ];
        · grind +splitIndPred;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith
  have htiny_le : (∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ)) ≤ ρ * N / 4 → (∑ n ∈ Lsub, ((Cls n).card : ℝ)) ≥ (N - 1 - ρ * N / 8 - ρ * N / 4) := by
    have hsum_card : ∑ n ∈ allLabels, ((Cls n).card : ℝ) = S.card := by
      rw [ ← Nat.cast_sum, Finset.card_eq_sum_ones ];
      rw [ Finset.sum_image' ];
      simp +zetaDelta at *;
    intro htiny_le
    have hsum_card_split : ∑ n ∈ allLabels, ((Cls n).card : ℝ) = ∑ n ∈ Lsub, ((Cls n).card : ℝ) + ∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ) := by
      rw [ add_comm, Finset.sum_sdiff <| Finset.filter_subset _ _ ];
    linarith;
  by_cases htiny : (∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ)) ≤ ρ * N / 4;
  · obtain ⟨nstar, hnstar⟩ : ∃ nstar ∈ Lsub, ∀ n ∈ Lsub, (Cls n).card ≤ (Cls nstar).card := by
      apply_rules [ Finset.exists_max_image ];
      contrapose! htiny_le;
      simp [htiny_le] at *;
      exact ⟨ htiny, by nlinarith [ show ( P.card : ℝ ) ≥ 2 by norm_cast ] ⟩;
    have hCls_nstar_card : (Cls nstar).card ≤ (1 - ρ) * N := by
      have hCls_nstar_card : |nstar| ≤ (X : ℤ) ^ 2 / 2 := by
        obtain ⟨q, hq⟩ : ∃ q ∈ S, lab q = nstar := by
          exact Finset.mem_image.mp ( Finset.mem_filter.mp hnstar.1 |>.1 );
        rw [ ← hq.2, Int.le_ediv_iff_mul_le ] <;> norm_num;
        exact_mod_cast ( by linarith [ Finset.mem_filter.mp hq.1 ] : ( |lab q| : ℝ ) * 2 ≤ X ^ 2 );
      have hCls_nstar_card : (Cls nstar).card ≤ (P.attach.filter (fun q => a q = ((nstar : ℤ) : ZMod q.1))).card := by
        refine Finset.card_le_card ?_;
        simp +zetaDelta at *;
        simp +contextual [ Finset.subset_iff ];
        intro q hq hq' hq'' hq''';
        convert crtRepr_eq_label_residue P ( fun p hp => ( hP p hp ).1 ) a p0 ⟨ q, hq ⟩ hq' using 1;
        · exact hq'''.symm ▸ rfl;
        · exact fun p => ⟨ Nat.Prime.ne_zero ( hP p p.2 |>.1 ) ⟩;
      contrapose! hnd;
      use nstar;
      exact ⟨ by assumption, le_trans hnd.le <| mod_cast hCls_nstar_card ⟩;
    have hM₂ : (∑ n ∈ Lsub \ {nstar}, ((Cls n).card : ℝ)) ≥ ρ * N / 2 := by
      have hM₂ : (∑ n ∈ Lsub \ {nstar}, ((Cls n).card : ℝ)) = (∑ n ∈ Lsub, ((Cls n).card : ℝ)) - ((Cls nstar).card : ℝ) := by
        rw [Finset.sum_eq_sum_sdiff_singleton_add
          (show nstar ∈ Lsub from hnstar.1), add_tsub_cancel_right];
      linarith [ htiny_le htiny ];
    have h_energy : cE / X^2 * (∑ n ∈ Lsub, ∑ n' ∈ Lsub \ {n}, ((Cls n).card : ℝ)^3 * ((Cls n').card : ℝ)) ≤ 2 * R := by
      apply class_partition_energy_lower_bound X P hP a p0 B hB0.le hBX S (fun q hq => by
        exact Finset.mem_filter.mp hq |>.2) Lsub (fun n hn => by
        grind +qlia) (fun n hn => by
        exact le_trans ( by linarith [ show ( 0 : ℝ ) ≤ B / X by positivity ] ) ( Finset.mem_filter.mp hn |>.2 )) R hQ cE hcE0 hcE;
    have h_power_mean : (∑ n ∈ Lsub \ {nstar}, ((Cls n).card : ℝ))^4 / (Lsub.card : ℝ)^2 ≤ ∑ n ∈ Lsub, ∑ n' ∈ Lsub \ {n}, ((Cls n).card : ℝ)^3 * ((Cls n').card : ℝ) := by
      convert sum_cube_offdiag_ge Lsub ( fun n => ( Cls n |> Finset.card : ℝ ) ) _ nstar _ _ using 1 <;> norm_num [ hnstar ];
      exact hnstar.2;
    have h_final : cE / X^2 * (ρ * N / 2)^4 / (2 * B / X + 2)^2 ≤ 2 * R := by
      have h_final : cE / X^2 * (ρ * N / 2)^4 / (Lsub.card : ℝ)^2 ≤ 2 * R := by
        refine le_trans ?_ h_energy;
        rw [ mul_div_assoc ];
        gcongr;
        exact le_trans ( by gcongr ) h_power_mean;
      refine le_trans ?_ h_final;
      gcongr;
      · exact sq_pos_of_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ nstar, hnstar.1 ⟩ ) );
      · exact le_trans ( Nat.cast_le.mpr <| Finset.card_le_card <| Finset.filter_subset _ _ ) hk0;
    field_simp at h_final ⊢;
    exact Or.inl h_final;
  · have hTiny_le : (∑ n ∈ allLabels \ Lsub, ((Cls n).card : ℝ)) ≤ k0 * s0 := by
      refine' le_trans ( Finset.sum_le_sum fun x hx => show ( # ( Cls x ) : ℝ ) ≤ s0 from _ ) _ <;> norm_num [ hk0 ];
      · grind;
      · exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_le_card <| Finset.sdiff_subset ) <| by positivity;
    generalize_proofs at *; (
    exact Or.inr ( lt_of_lt_of_le ( lt_of_not_ge htiny ) ( hTiny_le.trans ( mul_le_mul_of_nonneg_right hk0 ( by positivity ) ) ) ))

/-
**Log-growth threshold.**  Since `X/ log X → ∞`, for any `K` there is `X0` with
    `K ≤ X/ log X` for all `X ≥ X0`.
-/
lemma exists_logarithmic_threshold (K : ℝ) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℕ, X0 ≤ X → K ≤ (X:ℝ)/Real.log X := by
  -- By the properties of the logarithm and the fact that $X / \log X$ tends to infinity, we can find such an $X_0$.
  have h_log_growth : Filter.Tendsto (fun X : ℕ => (X : ℝ) / Real.log (X : ℝ)) Filter.atTop Filter.atTop := by
    have h_log_growth : Filter.Tendsto (fun x : ℝ => x / Real.log x) Filter.atTop Filter.atTop := by
      -- We can use the change of variables $u = \log x$ to transform the limit expression.
      suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
      simpa using Real.tendsto_exp_div_pow_atTop 1;
    exact h_log_growth.comp tendsto_natCast_atTop_atTop;
  exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop K ) |> fun ⟨ X0, hX0 ⟩ ↦ ⟨ ⌈X0⌉₊ + 1, by positivity, fun X hX ↦ hX0 X <| by linarith [ Nat.le_ceil X0, show ( X : ℕ ) ≥ ⌈X0⌉₊ + 1 by exact_mod_cast hX ] ⟩

/-
**Left-disjunct chase.**  Pure algebra: the large-energy disjunct of the
covering dichotomy forces `R ≳ X/log³X`.
-/
/-- A cutoff with scale coefficient `kappa` and comparison loss `lambda`
transfers an energy lower bound into a quadratic lower bound with the single
combined loss `kappa * lambda`.  This is the parameter mechanism behind the
left branch of the covering dichotomy; numerical choices belong only in its
specialization. -/
lemma cutoff_energy_quadratic_lower_bound
    (energy kappa lambda rho R x N : ℝ)
    (hkappa : 0 < kappa) (hlambda : 0 < lambda) (hrho : 0 < rho)
    (hx : 0 < x) (hN : 0 < N)
    (h : energy * rho ^ 4 * N ^ 4 / (lambda * x ^ 2) ≤
      (kappa / rho) * R ^ 2 * x ^ 2 / N ^ 2) :
    energy * rho ^ 5 * N ^ 6 / (kappa * lambda * x ^ 4) ≤ R ^ 2 := by
  field_simp at h ⊢
  nlinarith

lemma low_cutoff_energy_bound (cE ρ : ℝ) (hcE0 : 0 < cE) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (X : ℕ) (N R u : ℝ)
    (hlogX : 0 < Real.log X) (hN : (X:ℝ)/(2*Real.log X) ≤ N) (hNpos : 0 < N)
    (hR0 : 0 < R) (hu0 : 0 ≤ u)
    (husq : u^2 = (256/ρ)*R*(X:ℝ)^2/N^2)
    (hRle : R ≤ cE*ρ^4*(X:ℝ)^2/(8192*(Real.log X)^4))
    (hdisj : cE*(ρ*N/2)^4/(2*(X:ℝ)^2*(2*u+2)^2) ≤ R) :
    ρ^2 * Real.sqrt (cE*ρ) / (10^6) * (X:ℝ)/(Real.log X)^3 ≤ R := by
  -- From hN: N^4 ≥ (X/(2 log X))^4 = X^4/(16*(log X)^4), so T ≥ cE*ρ^4*X^2/(4096*(log X)^4) = 2*(cE*ρ^4*X^2/(8192*(log X)^4)) ≥ 2*R (by hRle). So R ≤ T/2.
  set T := cE * ρ^4 * N^4 / (256 * X^2)
  have hT : T ≥ 2 * R := by
    have hT' : N^4 ≥ X^4 / (16 * (Real.log X)^4) := by
      exact le_trans ( by rw [ div_pow ] ; ring_nf; norm_num ) ( pow_le_pow_left₀ ( by positivity ) hN 4 );
    by_cases hX : X = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    rw [ le_div_iff₀ ] <;> first | positivity | nlinarith [ show 0 < cE * ρ ^ 4 by positivity ] ;
  -- So (256/ρ)*R^2*X^2/N^2 ≥ T/2 = cE*ρ^4*N^4/(512*X^2).
  have hR2 : (256 / ρ) * R^2 * X^2 / N^2 ≥ cE * ρ^4 * N^4 / (512 * X^2) := by
    have hR2 : cE * ρ^5 * N^6 / 16 ≤ 16 * 256 * R^2 * X^4 + 16 * ρ * R * X^2 * N^2 := by
      have hR2 : cE * ρ^5 * N^6 / 16 ≤ 2 * X^2 * (2 * u + 2)^2 * R * ρ * N^2 := by
        rw [ div_le_iff₀ ] at hdisj;
        · nlinarith [ show 0 < ρ * N ^ 2 by positivity ];
        · exact mul_pos ( mul_pos two_pos ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) ) ) ( sq_pos_of_pos ( by positivity ) );
      have hR2 : (2 * u + 2)^2 ≤ 4 * (u^2 + 1) * 2 := by
        nlinarith only [ sq_nonneg ( u - 1 ), hu0 ];
      rw [ husq ] at hR2;
      field_simp at hR2;
      nlinarith [ show 0 < ρ * N ^ 2 by positivity, show 0 < R * X ^ 2 by exact mul_pos hR0 ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) ) ];
    rw [ ge_iff_le, div_le_div_iff₀ ] <;> try positivity;
    · rw [ ge_iff_le, le_div_iff₀ ] at hT;
      · field_simp at *;
        nlinarith [ show 0 < ρ * N ^ 2 by positivity ];
      · exact mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) );
    · exact mul_pos ( by norm_num ) ( sq_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ) ) ) );
  have hX_pos : (0 : ℝ) < X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hlogX)
  -- The numerical cutoff and comparison losses enter only through their product.
  have hR2_sq : R^2 ≥ cE * ρ^5 * N^6 / ((256 * 512) * X^4) :=
    cutoff_energy_quadratic_lower_bound cE 256 512 ρ R X N
      (by norm_num) (by norm_num) hρ hX_pos hNpos hR2
  -- Substitute only the density estimate `N ≥ X/(2 log X)`.
  have hR2_sq_final : R^2 ≥
      cE * ρ^5 * X^2 / ((64 * 256 * 512) * (Real.log X)^6) := by
    -- From hN: N^6 ≥ (X/(2 log X))^6 = X^6/(64*(log X)^6).
    have hN6 : N^6 ≥ X^6 / (64 * (Real.log X)^6) := by
      exact le_trans ( by rw [ div_pow ] ; ring_nf; norm_num ) ( pow_le_pow_left₀ ( by positivity ) hN 6 );
    refine le_trans ?_ hR2_sq;
    convert mul_le_mul_of_nonneg_left hN6
      (show 0 ≤ cE * ρ ^ 5 / ((256 * 512) * X ^ 4) by positivity) using 1 ; ring_nf;
    · grind;
    · ring;
  refine' le_of_pow_le_pow_left₀ ( by positivity ) ( by positivity ) ( le_trans _ hR2_sq_final );
  field_simp;
  rw [ Real.sq_sqrt ( by positivity ) ] ; nlinarith [ show 0 ≤ ρ * cE * X ^ 2 by positivity ]

/-
**Right-disjunct chase.**  Pure algebra: the tiny-mass disjunct of the covering
    dichotomy forces `R ≳ X/log³X`.
-/
lemma high_cutoff_energy_bound (ρ : ℝ) (hρ : 0 < ρ) (_hρ4 : ρ ≤ 1/4)
    (X : ℕ) (N R u : ℝ)
    (hlogX : 0 < Real.log X) (hN : (X:ℝ)/(2*Real.log X) ≤ N) (hNpos : 0 < N)
    (_hR0 : 0 < R) (_hu0 : 0 ≤ u)
    (husq : u^2 = (256/ρ)*R*(X:ℝ)^2/N^2)
    (hbigN : 2304/ρ ≤ N)
    (hdisj : ρ*N/4 < (2*u+2)*(32*(u+1)+8)) :
    ρ^2 / (4718592) * (X:ℝ)/(Real.log X)^3 ≤ R := by
  rw [ div_le_iff₀ ( by positivity ) ] at *;
  have h_combined : ρ^2 * N^3 / 8 < 73728 * R * X^2 := by
    field_simp at *;
    nlinarith [ sq_nonneg ( u - 1 ), mul_le_mul_of_nonneg_left hbigN hρ.le, mul_le_mul_of_nonneg_left hbigN hNpos.le ];
  have h_combined : N^3 ≥ X^3 / (8 * (Real.log X)^3) := by
    rw [ ge_iff_le, div_le_iff₀ ];
    · convert pow_le_pow_left₀ ( by positivity ) hN 3 using 1 ; ring;
    · positivity;
  rw [ ge_iff_le, div_le_iff₀ ] at h_combined <;> nlinarith [ pow_pos hlogX 3 ]

/-
**Get the dichotomy in `u = B/X` form.**  Picks the base point `p0` and threshold
    `B = √(A²R)·X²/N` (so the exception count is `≤ ρN/8`), and packages the covering
    dichotomy with `u := B/X`.
-/
set_option maxHeartbeats 1000000 in
lemma nondominant_energy_dichotomy
    (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ) [∀ p : P, NeZero p.1]
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X) (hcard2 : 2 ≤ P.card)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (a : BlockAssignment P) (hnd : ¬ HasDominantLabel X P a ρ)
    (R : ℝ) (hR0 : 0 < R) (hQ : QP P a ≤ R)
    (hAR : (256/ρ)*R ≤ ((P.card:ℝ))^2/16)
    (h1 : 1 ≤ ρ*(P.card:ℝ)/8)
    (cE : ℝ) (hcE0 : 0 < cE)
    (hcE : ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1]
        (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ),
        n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 →
        ∀ (C C' : Finset Q),
          (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) →
          (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) →
          Disjoint C C' →
          (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card →
          (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) →
          (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) →
          cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤
            ∑ p ∈ C, ∑ q ∈ C',
              ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2) :
    ∃ u : ℝ, 0 ≤ u ∧ u^2 = (256/ρ)*R*(X:ℝ)^2/(P.card:ℝ)^2 ∧
      (cE*(ρ*(P.card:ℝ)/2)^4/(2*(X:ℝ)^2*(2*u+2)^2) ≤ R ∨
        ρ*(P.card:ℝ)/4 < (2*u+2)*(32*(u+1)+8)) := by
  refine' ⟨ Real.sqrt ( 256 / ρ * R * X ^ 2 / P.card ^ 2 ), _, _, _ ⟩;
  · positivity;
  · rw [ Real.sq_sqrt ( by positivity ) ];
  · obtain ⟨p0, hp0mem, hp0⟩ : ∃ p0 : P, p0 ∈ P.attach ∧ ((P.attach.filter (fun q => q ≠ p0 ∧ Real.sqrt ((256 / ρ) * R) * (X : ℝ) ^ 2 / P.card < |(crtRepr p0.1 q.1 (a p0) (a q) : ℝ)|)).card : ℝ) ≤ ρ * P.card / 8 := by
      have := exists_sparse_crt_basepoint X hX P hP (by linarith) a R hR0.le hQ (Real.sqrt ((256 / ρ) * R) * (X : ℝ) ^ 2 / P.card) (by
      positivity);
      convert this using 4;
      field_simp;
      rw [ Real.sq_sqrt ( by positivity ), mul_div_cancel₀ _ ( by positivity ) ] ; ring;
    convert label_covering_energy_dichotomy X hX P hP hcard2 ρ hρ hρ4 a hnd R hR0 hQ p0 ( Real.sqrt ( 256 / ρ * R ) * X ^ 2 / P.card ) _ _ _ _ cE hcE0 hcE using 2 <;> norm_num [ hR0.le, hρ.le, hX ];
    any_goals assumption;
    · field_simp;
    · field_simp;
    · positivity;
    · rw [ div_le_iff₀ ];
      · convert mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt hAR ) ( show ( 0 : ℝ ) ≤ X ^ 2 by positivity ) using 1 ; ring_nf;
        · norm_num [ hρ.le, hR0.le ] ; ring;
        · norm_num ; ring;
      · positivity;
    · convert hp0 using 4 ; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hR0.le, hρ.le ]

/-
For `X ≥ 3`, `1 ≤ Real.log X`.
-/
lemma one_le_log_of_large (X : ℕ) (hX : 3 ≤ X) : 1 ≤ Real.log X := by
  exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] ) )

/-
When `1 ≤ Real.log X`, `X/ log X ≤ X· log X`.
-/
lemma self_div_log_le_self (X : ℕ) (h : 1 ≤ Real.log X) :
    (X:ℝ)/Real.log X ≤ (X:ℝ)*Real.log X := by
  rw [ div_le_iff₀ ] <;> nlinarith [ show ( X : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at h ) ), mul_le_mul_of_nonneg_left h ( show ( 0 : ℝ ) ≤ X by positivity ) ]

/-
Combine `R ≤ c2·X/log³X` with the threshold `64·A²·c2 ≤ X·log X` to get `A²R ≤ N²/16`.
-/
lemma nondominant_auxiliary_range_bound (ρ c2 : ℝ) (hρ : 0 < ρ) (_hc2 : 0 ≤ c2)
    (X : ℕ) (N R : ℝ) (hlog0 : 0 < Real.log X)
    (hN : (X:ℝ)/(2*Real.log X) ≤ N)
    (hR : R ≤ c2*(X:ℝ)/(Real.log X)^3)
    (hThr1 : 64*(256/ρ)*c2 ≤ (X:ℝ)*Real.log X) :
    (256/ρ)*R ≤ N^2/16 := by
  have hXpos : (0 : ℝ) < X :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg X)).mp hlog0)
  refine le_trans ( mul_le_mul_of_nonneg_left hR ( by positivity ) ) ?_;
  rw [ ← mul_div_assoc, div_le_iff₀ ] at *;
  · ring_nf at *;
    nlinarith [ sq_nonneg ( N * Real.log X - X ), mul_le_mul_of_nonneg_left hN hlog0.le, mul_le_mul_of_nonneg_left hN hXpos.le, Real.log_le_sub_one_of_pos hXpos, Real.log_le_sub_one_of_pos hlog0 ];
  · positivity;
  · positivity

/-
Combine `R ≤ c2·X/log³X` with `8192·c2/(cEρ⁴) ≤ X/log X` to bound `R` by the
    case-B threshold.
-/
lemma cutoff_energy_upper_bound (cE ρ c2 : ℝ) (hcE0 : 0 < cE) (hρ : 0 < ρ)
    (X : ℕ) (R : ℝ) (hlog0 : 0 < Real.log X)
    (hR : R ≤ c2*(X:ℝ)/(Real.log X)^3)
    (hThr2 : 8192*c2/(cE*ρ^4) ≤ (X:ℝ)/Real.log X) :
    R ≤ cE*ρ^4*(X:ℝ)^2/(8192*(Real.log X)^4) := by
  rw [ div_le_div_iff₀ ] at * <;> try positivity;
  rw [ le_div_iff₀ ] at * <;> nlinarith [ pow_pos hlog0 3, pow_pos hlog0 4 ]

/-
For `ρ ∈ (0,1/4]` and `X` large, any low-energy
    assignment that is **not** dominant forces `R ≫ X/log³X`.  Concretely there is
    `c₂ > 0` with: if `QP P a ≤ R` and `a` is not `ρ`-dominant then
    `R ≥ c₂ · X / (Real.log X)^3`.

    The covering construction produces `≥ 2` substantial classes; cross-label
    energy with the mass accounting (`M₂ ≥ ρN/2`) forces
    `R² ≫ N⁴/(X²log²X)`, i.e. `R ≫ N²/(X log X) ≫ X/log³X`.

    The argument decomposes into the covering helpers
    (`large_crt_pair_count`, `exists_sparse_crt_basepoint`, `crt_label_shortlist_bound`), the energy
    core (`class_partition_energy_lower_bound`, `crossLabel_energy_sum_le`), the covering
    dichotomy (`label_covering_energy_dichotomy`) with the mass accounting, and the
    parameter chase (`nondominant_energy_dichotomy`, `low_cutoff_energy_bound`,
    `high_cutoff_energy_bound`).
-/
theorem nondominant_energy_lower_bound
    (ρ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    ∃ (c2 X0 : ℝ), 0 < c2 ∧ 0 < X0 ∧
      ∀ (X : ℕ), X0 ≤ X →
        ∀ (P : Finset ℕ) [∀ p : P, NeZero p.1]
          (_hP : ∀ p ∈ P, Nat.Prime p ∧ X ≤ p ∧ p ≤ 2*X)
          (_hN : (X:ℝ)/(2 * Real.log X) ≤ P.card)
          (a : BlockAssignment P) (R : ℝ),
          QP P a ≤ R → ¬ HasDominantLabel X P a ρ →
            c2 * (X:ℝ) / (Real.log X)^3 ≤ R := by
  revert ρ hρ hρ4;
  obtain ⟨cE, hcE0, hcE⟩ : ∃ cE : ℝ, 0 < cE ∧ ∀ (Y : ℕ) (Q : Finset ℕ) [∀ p : Q, NeZero p.1] (b : BlockAssignment Q) (n n' : ℤ) (D : ℝ), n ≠ n' → |(n:ℝ)| ≤ D → |(n':ℝ)| ≤ D → D ≤ (Y:ℝ)^2/4 → ∀ (C C' : Finset Q), (∀ p ∈ C, Nat.Prime (p:ℕ) ∧ Y ≤ (p:ℕ) ∧ (p:ℕ) ≤ 2*Y) → (∀ q ∈ C', Nat.Prime (q:ℕ) ∧ Y ≤ (q:ℕ) ∧ (q:ℕ) ≤ 2*Y) → Disjoint C C' → (32 * (D/Y + 1) : ℝ) ≤ C.card → (8:ℝ) ≤ C'.card → (∀ p ∈ C, b p = ((n : ℤ) : ZMod (p:ℕ))) → (∀ q ∈ C', b q = ((n' : ℤ) : ZMod (q:ℕ))) → cE * (C.card : ℝ)^3 * C'.card / (Y:ℝ)^2 ≤ ∑ p ∈ C, ∑ q ∈ C', ((crtRepr (p:ℕ) (q:ℕ) (b p) (b q) : ℝ) / ((p:ℕ) * (q:ℕ)))^2 := by
    apply crossLabel_energy_lower_bound;
  intro ρ hρ hρ4
  set c2 := min (ρ^2 * Real.sqrt (cE*ρ) / 10^6) (ρ^2/4718592) with hc2def
  have hc2pos : 0 < c2 := by
    exact lt_min ( by positivity ) ( by positivity )
  generalize_proofs at *;
  set K := max (max 4 (16/ρ)) (max (4608/ρ) (max (64*(256/ρ)*c2) (8192*c2/(cE*ρ^4)))) with hKdef
  obtain ⟨X0', hX0'0, hK⟩ := exists_logarithmic_threshold K
  use c2, ⌈X0'⌉₊ + 3, hc2pos, by positivity
  intro X hX P inst hP hN a R hQ hnd
  have hX3 : 3 ≤ X := by
    exact_mod_cast hX.trans' ( le_add_of_nonneg_left <| Nat.cast_nonneg _ )
  have hX1 : 1 ≤ X := by
    linarith
  generalize_proofs at *;
  have hlog1 : 1 ≤ Real.log X := by
    exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( X : ℝ ) ≥ 3 by norm_cast ] ) )
  have hlog0 : 0 < Real.log X := by
    linarith
  have hXpos : (0:ℝ) < X := by positivity
  have hKX : K ≤ (X:ℝ)/Real.log X := by
    exact hK X ( by linarith [ Nat.le_ceil X0' ] )
  have hself := self_div_log_le_self X hlog1
  set N := (P.card:ℝ) with hNdef
  have hNK : K/2 ≤ N := by
    have h1 : K / 2 ≤ (X:ℝ)/(2*Real.log X) := by
      convert div_le_div_of_nonneg_right hKX zero_le_two using 1
      all_goals first | rfl | ring_nf
    generalize_proofs at *;
    linarith [hN]
  have hNpos : 0 < N := by
    exact lt_of_lt_of_le ( by positivity ) hNK
  have hcard2 : 2 ≤ P.card := by
    have h1 : K/2 ≥ 2 := by
      exact le_trans ( by norm_num ) ( div_le_div_of_nonneg_right ( le_max_left _ _ |> le_trans ( le_max_left _ _ ) ) zero_le_two )
    generalize_proofs at *;
    exact_mod_cast h1.trans hNK |> le_trans <| hNdef.le
  generalize_proofs at *;
  by_cases hRbig : c2 * (X:ℝ)/(Real.log X)^3 ≤ R;
  · exact hRbig;
  · have hRle' : R ≤ c2 * (X:ℝ)/(Real.log X)^3 := by
      exact le_of_not_ge hRbig
    have hR0 : 0 < R := by
      by_contra hRneg
      push Not at hRneg
      exact hnd (zero_label_dominant_of_large_class X hX1 P hP hcard2 a ρ hρ.le (le_antisymm (le_trans hQ hRneg) (QP_nonneg P a)))
    generalize_proofs at *;
    have hThr1 : 64*(256/ρ)*c2 ≤ (X:ℝ)*Real.log X := by
      grind +splitImp
    have hThr2 : 8192*c2/(cE*ρ^4) ≤ (X:ℝ)/Real.log X := by
      exact le_trans ( le_max_of_le_right <| le_max_of_le_right <| le_max_right _ _ ) hKX
    have hAR : (256/ρ)*R ≤ N^2/16 := by
      apply nondominant_auxiliary_range_bound ρ c2 hρ hc2pos.le X N R hlog0 hN hRle' hThr1
    have h1 : 1 ≤ ρ*N/8 := by
      have h16 : 16 / ρ ≤ K := by
        exact le_max_of_le_left ( le_max_right _ _ )
      generalize_proofs at *;
      nlinarith [ mul_div_cancel₀ 16 hρ.ne' ]
    generalize_proofs at *;
    obtain ⟨u, hu0, husq, hdisj⟩ := nondominant_energy_dichotomy X hX1 P hP hcard2 ρ hρ hρ4 a hnd R hR0 hQ hAR h1 cE hcE0 hcE
    rcases hdisj with hL | hRgt
    · have hRle : R ≤ cE*ρ^4*(X:ℝ)^2/(8192*(Real.log X)^4) := cutoff_energy_upper_bound cE ρ c2 hcE0 hρ X R hlog0 hRle' hThr2
      have hcl := low_cutoff_energy_bound cE ρ hcE0 hρ hρ4 X N R u hlog0 hN hNpos hR0 hu0 husq hRle hL
      refine le_trans ?_ hcl
      have hcle : c2 ≤ ρ^2 * Real.sqrt (cE*ρ) / 10^6 := min_le_left _ _
      gcongr
    · have hbigN : 2304/ρ ≤ N := by
        grind
      have hcr := high_cutoff_energy_bound ρ hρ hρ4 X N R u hlog0 hN hNpos hR0 hu0 husq hbigN hRgt
      refine le_trans ?_ hcr
      have hcr2 : c2 ≤ ρ^2/4718592 := min_le_right _ _
      gcongr


end LocalEnergy
