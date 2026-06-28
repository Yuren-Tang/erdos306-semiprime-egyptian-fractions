import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Squarefree

/-- A natural number is the product of two distinct primes. -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p * q

lemma IsSemiprime.squarefree {n : ℕ} (h : IsSemiprime n) : Squarefree n := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := h
  rw [Nat.squarefree_mul_iff]
  exact ⟨hp.coprime_iff_not_dvd.mpr fun hdiv =>
      hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv),
    hp.squarefree, hq.squarefree⟩

lemma IsSemiprime.pos {n : ℕ} (h : IsSemiprime n) : 0 < n := by
  obtain ⟨p, q, hp, hq, _, rfl⟩ := h
  exact Nat.mul_pos hp.pos hq.pos

/-- A semiprime remains nonzero after coercion to `ℚ`. -/
lemma IsSemiprime.cast_ne_zero {n : ℕ} (h : IsSemiprime n) : (n : ℚ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr h.pos.ne'
