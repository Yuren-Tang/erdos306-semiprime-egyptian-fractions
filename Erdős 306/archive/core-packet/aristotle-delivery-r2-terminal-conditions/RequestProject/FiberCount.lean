import RequestProject.GlobalControl

open Finset BigOperators Classical

noncomputable section

namespace CircleMethod

open GlobalControl

/-- The primes in the block support are pairwise coprime. -/
lemma blockSupport_list_pairwise_coprime (BS : BlockSystem) :
    (blockSupport BS).toList.Pairwise (fun p q : ℕ => Nat.Coprime p q) := by
  refine List.Nodup.pairwise_of_forall_ne ?_ ?_
  · exact Finset.nodup_toList (blockSupport BS)
  · intro p hp q hq hpq
    have hp_support : p ∈ blockSupport BS := by
      simpa using hp
    have hq_support : q ∈ blockSupport BS := by
      simpa using hq
    exact primes_coprime_of_ne (blockSupport_prime BS hp_support)
      (blockSupport_prime BS hq_support) hpq

/-- Equality of the frequency residue assignment implies congruence modulo the
product of all block-support primes. -/
lemma freq_assignment_eq_modEq_blockSupport_prod (BS : BlockSystem) {h h' : ℕ}
    (heq :
      (fun p : {p : ℕ // p ∈ blockSupport BS} => (h : ZMod p.1)) =
        (fun p : {p : ℕ // p ∈ blockSupport BS} => (h' : ZMod p.1))) :
    h ≡ h' [MOD ∏ p ∈ blockSupport BS, p] := by
  have hlist :
      h ≡ h' [MOD ((blockSupport BS).toList.map id).prod] := by
    refine (Nat.modEq_list_map_prod_iff (s := id)
      (l := (blockSupport BS).toList) (blockSupport_list_pairwise_coprime BS)).mpr ?_
    intro p hp
    have hp_support : p ∈ blockSupport BS := by
      simpa using hp
    have hcoord := congrFun heq ⟨p, hp_support⟩
    exact (ZMod.natCast_eq_natCast_iff h h' p).mp hcoord
  have hprod : ((blockSupport BS).toList.map id).prod = ∏ p ∈ blockSupport BS, p := by
    rw [List.map_id]
    change ((blockSupport BS).toList : Multiset ℕ).prod = ∏ p ∈ blockSupport BS, p
    rw [Finset.coe_toList, Finset.prod_val]
    rfl
  simpa [hprod] using hlist

/-- The frequency-to-block-assignment map is injective on every interval of
length `D = ∏ p ∈ blockSupport BS, p`. -/
lemma freq_assignment_injective_on_fixed_quotient (BS : BlockSystem) {D h h' q : ℕ}
    (hD : D = ∏ p ∈ blockSupport BS, p)
    (hdiv : h / D = q) (hdiv' : h' / D = q)
    (heq :
      (fun p : {p : ℕ // p ∈ blockSupport BS} => (h : ZMod p.1)) =
        (fun p : {p : ℕ // p ∈ blockSupport BS} => (h' : ZMod p.1))) :
    h = h' := by
  subst D
  have hmod := freq_assignment_eq_modEq_blockSupport_prod BS heq
  unfold Nat.ModEq at hmod
  have hdecomp : h = (∏ p ∈ blockSupport BS, p) * (h / (∏ p ∈ blockSupport BS, p)) +
      h % (∏ p ∈ blockSupport BS, p) := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod h (∏ p ∈ blockSupport BS, p)).symm
  have hdecomp' : h' = (∏ p ∈ blockSupport BS, p) * (h' / (∏ p ∈ blockSupport BS, p)) +
      h' % (∏ p ∈ blockSupport BS, p) := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod h' (∏ p ∈ blockSupport BS, p)).symm
  rw [hdecomp, hdecomp', hdiv, hdiv', hmod]

/-- The frequency→block-assignment map is `≤ b`-to-1 on `range L` when
`L = b · ∏ blockSupport`. -/
theorem mainArc_fiber_card_le (BS : BlockSystem) (L b : ℕ)
    (hL : L = b * ∏ p ∈ blockSupport BS, p) :
    ∀ a : GlobalAssignment BS,
      ((Finset.range L).filter
        (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
          (h : ZMod p.1)) = a)).card ≤ b := by
  classical
  intro a
  let D : ℕ := ∏ p ∈ blockSupport BS, p
  let S : Finset ℕ :=
    (Finset.range L).filter
      (fun h => (fun p : {p : ℕ // p ∈ blockSupport BS} =>
        (h : ZMod p.1)) = a)
  by_cases hb0 : b = 0
  · have hL0 : L = 0 := by
      simp [hL, hb0]
    simp [hL0, hb0]
  have hmap : Set.MapsTo (fun h : ℕ => h / D) S (Finset.range b) := by
    intro h hh
    rw [Finset.mem_coe, Finset.mem_range]
    have hmem_range : h ∈ Finset.range L := (Finset.mem_filter.mp hh).1
    have hltL : h < L := Finset.mem_range.mp hmem_range
    rw [hL] at hltL
    rw [mul_comm b D] at hltL
    exact Nat.div_lt_of_lt_mul hltL
  have hinj : (S : Set ℕ).InjOn (fun h : ℕ => h / D) := by
    intro h hh h' hh' hquot
    have hhF : h ∈ S := by simpa using hh
    have hhF' : h' ∈ S := by simpa using hh'
    have heqh : (fun p : {p : ℕ // p ∈ blockSupport BS} => (h : ZMod p.1)) = a :=
      (Finset.mem_filter.mp hhF).2
    have heqh' : (fun p : {p : ℕ // p ∈ blockSupport BS} => (h' : ZMod p.1)) = a :=
      (Finset.mem_filter.mp hhF').2
    have heq :
        (fun p : {p : ℕ // p ∈ blockSupport BS} => (h : ZMod p.1)) =
          (fun p : {p : ℕ // p ∈ blockSupport BS} => (h' : ZMod p.1)) := by
      exact heqh.trans heqh'.symm
    exact freq_assignment_injective_on_fixed_quotient BS (hD := rfl)
      (hdiv := rfl) (hdiv' := hquot.symm) heq
  have hcard : S.card ≤ (Finset.range b).card :=
    Finset.card_le_card_of_injOn (fun h : ℕ => h / D) hmap hinj
  simpa [S] using hcard

end CircleMethod

end
