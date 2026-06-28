/-
# Global Peierls bookkeeping — abstract finite combinatorics (note 37 §3)

This file isolates the *pure finite combinatorics* used by the global level-set
theorem (G5) of note 34, free of any CRT / prime-number content.  It is the
"weighted subset entropy" / "energy shell" / "segment encoder" layer the note 37
blueprint asks to prove first, before instantiating with the SBEE single-block
data.

The headline lemma `weighted_subset_entropy` is the entropy bound used twice in
G5 (for the hot set with weights `Rw_k`, and for the mismatch boundary set with
weights `Π_k`): the number of admissible subsets, weighted by a per-element
cost, is dominated by `exp(εR/2) · exp(∑ exp(-ε w/4))`.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

namespace GlobalPeierls

noncomputable section

/-
**Weighted subset entropy** (note 37 §3.2).  Let `I` be a finite index set
with nonnegative weights `w` and nonnegative costs `cost` such that
`cost i ≤ exp(ε·w i/4)`.  Then the total cost summed over all subsets whose
weight is `≤ R` is bounded by `exp(εR/2)·exp(∑_i exp(-ε·w i/4))`.

Proof: for an admissible subset `S` (i.e. `∑_{i∈S} w i ≤ R`),
`∏_{i∈S} cost i ≤ exp(εR/2)·∏_{i∈S}(cost i·exp(-ε w i/2))`; summing over *all*
subsets and using `Finset.prod_add` turns the sum into the product
`∏_i (1 + cost i·exp(-ε w i/2))`, which is `≤ exp(∑_i cost i·exp(-ε w i/2))
≤ exp(∑_i exp(-ε w i/4))`.
-/
lemma weighted_subset_entropy {ι : Type*} (I : Finset ι) (w cost : ι → ℝ)
    (eps R : ℝ) (heps : 0 ≤ eps)
    (hcost : ∀ i ∈ I, 0 ≤ cost i)
    (hcb : ∀ i ∈ I, cost i ≤ Real.exp (eps * w i / 4)) :
    (∑ S ∈ I.powerset.filter (fun S => ∑ i ∈ S, w i ≤ R), ∏ i ∈ S, cost i)
      ≤ Real.exp (eps * R / 2) * Real.exp (∑ i ∈ I, Real.exp (-eps * w i / 4)) := by
  -- By definition of $f$, we know that for each subset $S \subseteq I$ with $\sum_{i \in S} w_i \leq R$, $\prod_{i \in S} \text{cost}_i \leq \exp(\epsilon R / 2) \prod_{i \in S} f_i$.
  have h_subset_bound : ∀ S ∈ I.powerset, (∑ i ∈ S, w i ≤ R) → (∏ i ∈ S, cost i) ≤ Real.exp (eps * R / 2) * (∏ i ∈ S, (cost i * Real.exp (-eps * w i / 2))) := by
    intro S hSi hSR
    have h_subset_bound : (∏ i ∈ S, cost i) ≤ Real.exp (eps * R / 2) * (∏ i ∈ S, (cost i * Real.exp (-eps * w i / 2))) := by
      rw [ Finset.prod_mul_distrib, ← Real.exp_sum ];
      norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      exact le_mul_of_one_le_right ( Finset.prod_nonneg fun i hi => hcost i ( Finset.mem_powerset.mp hSi hi ) ) ( Real.one_le_exp ( by nlinarith ) )
    exact h_subset_bound;
  -- By combining terms, we can factor out $\exp(\epsilon R / 2)$ from the sum.
  have h_sum_bound : (∑ S ∈ I.powerset with (∑ i ∈ S, w i) ≤ R, (∏ i ∈ S, cost i)) ≤ Real.exp (eps * R / 2) * (∑ S ∈ I.powerset, (∏ i ∈ S, (cost i * Real.exp (-eps * w i / 2)))) := by
    rw [ Finset.mul_sum _ _ _ ] ; exact le_trans ( Finset.sum_le_sum fun S hS => h_subset_bound S ( Finset.mem_filter.mp hS |>.1 ) ( Finset.mem_filter.mp hS |>.2 ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( Real.exp_nonneg _ ) ( Finset.prod_nonneg fun _ _ => mul_nonneg ( hcost _ <| Finset.mem_powerset.mp ‹_› ‹_› ) <| Real.exp_nonneg _ ) ) ;
  -- By definition of $f$, we know that $\sum_{S \in I.powerset} \prod_{i \in S} f_i = \prod_{i \in I} (1 + f_i)$.
  have h_prod_add : (∑ S ∈ I.powerset, (∏ i ∈ S, (cost i * Real.exp (-eps * w i / 2)))) = (∏ i ∈ I, (1 + cost i * Real.exp (-eps * w i / 2))) := by
    exact (Finset.prod_one_add I).symm
  -- By definition of $f$, we know that $1 + f_i \leq \exp(f_i)$ for each $i \in I$.
  have h_exp_bound : ∀ i ∈ I, 1 + cost i * Real.exp (-eps * w i / 2) ≤ Real.exp (Real.exp (-eps * w i / 4)) := by
    intro i hi
    have h_exp_bound_i : cost i * Real.exp (-eps * w i / 2) ≤ Real.exp (-eps * w i / 4) := by
      exact le_trans ( mul_le_mul_of_nonneg_right ( hcb i hi ) ( Real.exp_nonneg _ ) ) ( by rw [ ← Real.exp_add ] ; ring_nf; norm_num );
    linarith [ Real.add_one_le_exp ( Real.exp ( -eps * w i / 4 ) ) ];
  exact h_sum_bound.trans ( mul_le_mul_of_nonneg_left ( h_prod_add.symm ▸ le_trans ( Finset.prod_le_prod ( fun _ _ => add_nonneg zero_le_one ( mul_nonneg ( hcost _ ‹_› ) ( Real.exp_nonneg _ ) ) ) h_exp_bound ) ( by rw [ ← Real.exp_sum ] ) ) ( Real.exp_nonneg _ ) )

/-- **Subset-count entropy** (note 37 §3.2, the `cost ≡ 1` specialization used to
bound the number of admissible *hot sets* and *mismatch-boundary sets* in G5).
The number of subsets of `I` whose total weight is `≤ R` is bounded by
`exp(εR/2)·exp(∑_i exp(-ε·w i/4))`. -/
lemma subset_count_entropy {ι : Type*} (I : Finset ι) (w : ι → ℝ)
    (eps R : ℝ) (heps : 0 ≤ eps) (hw : ∀ i ∈ I, 0 ≤ w i) :
    ((I.powerset.filter (fun S => ∑ i ∈ S, w i ≤ R)).card : ℝ)
      ≤ Real.exp (eps * R / 2) * Real.exp (∑ i ∈ I, Real.exp (-eps * w i / 4)) := by
  have h := weighted_subset_entropy I w (fun _ => 1) eps R heps
    (fun _ _ => zero_le_one)
    (fun i hi => by
      have : (0 : ℝ) ≤ eps * w i / 4 := by
        have := mul_nonneg heps (hw i hi); linarith
      simpa using Real.one_le_exp this)
  simpa using h

/-- **Product of local counts** (note 37 §3, the energy-shell product / the G5
steps 2 and 5 multiplication of hot and fixed-label cold block counts).  If each
local count `c i` is `≤ exp(ε·R i)` and the local energies sum to `≤ R`, then the
product of local counts is `≤ exp(ε·R)`. -/
lemma prod_local_count_le {ι : Type*} (I : Finset ι) (Renergy c : ι → ℝ)
    (eps R : ℝ) (heps : 0 ≤ eps)
    (hc : ∀ i ∈ I, 0 ≤ c i)
    (hcb : ∀ i ∈ I, c i ≤ Real.exp (eps * Renergy i))
    (hsum : ∑ i ∈ I, Renergy i ≤ R) :
    (∏ i ∈ I, c i) ≤ Real.exp (eps * R) := by
  calc (∏ i ∈ I, c i)
      ≤ ∏ i ∈ I, Real.exp (eps * Renergy i) :=
        Finset.prod_le_prod (fun i hi => hc i hi) (fun i hi => hcb i hi)
    _ = Real.exp (∑ i ∈ I, eps * Renergy i) := by rw [Real.exp_sum]
    _ = Real.exp (eps * ∑ i ∈ I, Renergy i) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (eps * R) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hsum heps

/-
**Shell-sum lemma** (note 38 §1, Lemma SH).  Enumerating shell vectors
`v : ι → ℕ` with `∑ v ≤ R`, the sum of products of per-block counts `c k (v k)`
(each `≤ exp(α(n+1))`) is dominated by `exp((α+β)R)·exp(|ι|·(α+log(1/(1-e^{-β}))))`.
The geometric discount in `β` makes the (unconstrained) enumeration of shell
vectors converge.  This is the energy-shell bookkeeping used by G5.
-/
lemma shell_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ → ℝ)
    (alpha beta R : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) (_hR : 0 ≤ R)
    (hc0 : ∀ k n, 0 ≤ c k n)
    (hcb : ∀ k (n : ℕ), c k n ≤ Real.exp (alpha * (n + 1))) :
    ∑ v ∈ (Fintype.piFinset (fun _ : ι => Finset.range (⌊R⌋₊ + 1))).filter
        (fun v => (∑ k, (v k : ℝ)) ≤ R),
      ∏ k, c k (v k)
    ≤ Real.exp ((alpha + beta) * R) *
      Real.exp ((Fintype.card ι : ℝ) *
        (alpha + Real.log (1 / (1 - Real.exp (-beta))))) := by
  -- For each admissible v (in the filter, so ∑ k, (v k : ℝ) ≤ R), bound the product:
  have h_bound : ∀ v ∈ Fintype.piFinset (fun _ => Finset.range (⌊R⌋₊ + 1)), (∑ k, (v k : ℝ)) ≤ R → (∏ k, c k (v k)) ≤ Real.exp (alpha * Fintype.card ι) * Real.exp ((alpha + beta) * R) * (∏ k, Real.exp (-beta * (v k : ℝ))) := by
    -- Using the bounds on $c_k(n)$ and the fact that $\sum_{k} v_k \leq R$, we can show that the product of $c_k(v_k)$ is bounded by the exponential term.
    intros v hv hvR
    have h_prod_bound : (∏ k, c k (v k)) ≤ Real.exp (alpha * (∑ k, (v k + 1))) := by
      exact le_trans ( Finset.prod_le_prod ( fun _ _ => hc0 _ _ ) fun _ _ => hcb _ _ ) ( by simp +decide [ ← Real.exp_sum, mul_add, Finset.mul_sum _ _ _ ] );
    simp_all +decide [ mul_add, ← Real.exp_add, Finset.sum_add_distrib ];
    rw [ ← Real.exp_sum, ← Real.exp_add ];
    exact h_prod_bound.trans ( Real.exp_le_exp.mpr <| by nlinarith [ show ( ∑ k : ι, ( v k : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _, show ( ∑ k : ι, - ( beta * ( v k : ℝ ) ) ) = - ( beta * ∑ k : ι, ( v k : ℝ ) ) by rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.sum_neg_distrib ] ] );
  -- Therefore, the filtered sum ≤ sum over ALL v ∈ piFinset of [exp(alpha*card)*exp((alpha+beta)*R)*∏ k, exp(-beta*(v k))], by extending the filter to the whole piFinset (all terms nonnegative).
  have h_sum_bound : (∑ v ∈ Fintype.piFinset (fun _ => Finset.range (⌊R⌋₊ + 1)) |>.filter (fun v => ∑ k, (v k : ℝ) ≤ R), (∏ k, c k (v k))) ≤ Real.exp (alpha * Fintype.card ι) * Real.exp ((alpha + beta) * R) * (∏ k : ι, (∑ n ∈ Finset.range (⌊R⌋₊ + 1), Real.exp (-beta * (n : ℝ)))) := by
    refine' le_trans ( Finset.sum_le_sum fun v hv => h_bound v ( Finset.mem_filter.mp hv |>.1 ) ( Finset.mem_filter.mp hv |>.2 ) ) _;
    refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( Real.exp_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => Real.exp_nonneg _ ) ) _;
    rw [ ← Finset.mul_sum _ _ _, Finset.prod_sum ];
    refine' le_of_eq _;
    refine' congr_arg _ ( Finset.sum_bij ( fun v hv => fun k _ => v k ) _ _ _ _ ) <;> simp +decide;
    · simp +contextual [ funext_iff ];
    · exact fun b hb => ⟨ fun k => b k ( Finset.mem_univ k ), hb, rfl ⟩;
  -- Each inner geometric sum: ∑ n ∈ range N, exp(-beta*n) = ∑ n ∈ range N, (exp(-beta))^n ≤ 1/(1-exp(-beta)) since 0 ≤ exp(-beta) < 1.
  have h_geo_sum : ∀ N : ℕ, (∑ n ∈ Finset.range N, Real.exp (-beta * (n : ℝ))) ≤ 1 / (1 - Real.exp (-beta)) := by
    intro N
    have h_geo_sum : (∑ n ∈ Finset.range N, Real.exp (-beta * (n : ℝ))) = (∑ n ∈ Finset.range N, (Real.exp (-beta)) ^ n) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [ h_geo_sum, one_div, ← tsum_geometric_of_lt_one ( by positivity ) ( by norm_num; positivity ) ] ; exact Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => by positivity ) ( by exact summable_geometric_of_lt_one ( by positivity ) ( by norm_num; positivity ) ) ;
  convert h_sum_bound.trans ( mul_le_mul_of_nonneg_left ( Finset.prod_le_prod ( fun _ _ => Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) fun _ _ => h_geo_sum _ ) ( by positivity ) ) using 1
  rfl
  have hden_pos : 0 < 1 - Real.exp (-beta) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hbeta))
  have hgeom_pos : 0 < 1 / (1 - Real.exp (-beta)) := one_div_pos.mpr hden_pos
  rw [Finset.prod_const, Finset.card_univ]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hgeom_pos]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring_nf

/-- **Segment label constancy** (note 34 G5 step 4 / note 37 §3.2 "segment
construction").  If across every index `k` of a connected run the edge predicate
`P k` forces `label k = label (k+1)`, then the label is constant throughout the
run: any two endpoints `i ≤ j` whose intermediate edges all satisfy `P` carry
equal labels.  This is the combinatorial heart of "labels are constant on each
cold segment". -/
lemma segment_label_constant {α : Type*} (label : ℕ → α) (P : ℕ → Prop)
    (h : ∀ k, P k → label k = label (k + 1)) :
    ∀ i j, i ≤ j → (∀ k, i ≤ k → k < j → P k) → label i = label j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; rfl
  | succ j hij ih =>
      intro hseg
      have hrun : label i = label j :=
        ih (fun k hk1 hk2 => hseg k hk1 (Nat.lt_succ_of_lt hk2))
      exact hrun.trans (h j (hseg j hij (Nat.lt_succ_self j)))

end

end GlobalPeierls
