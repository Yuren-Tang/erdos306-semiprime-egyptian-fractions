/-
# Cross-Label CRT Energy Bounds

Proves qualitative and quantitative lower bounds on cross-label CRT energy
(Lemma 3.1 of CP 03), the key ingredient for proving SBEE.

For prime sets A, B and labels m ≠ m', with CRT representatives H_{pq}:
  ∑_{p∈A,q∈B} (H_{pq})² > 0
provided there exists a witnessing pair (p,q) with p ∤ m or q ∤ m'.
-/
import Mathlib

open Finset BigOperators

/-- If H(p,q) = 0 and H ≡ m (mod p), H ≡ m' (mod q), then p | m and q | m'. -/
lemma crt_zero_implies_divisibility
    {A B : Finset ℕ} {m m' : ℤ} {H : ℕ → ℕ → ℤ}
    (hH : ∀ p ∈ A, ∀ q ∈ B,
      (H p q : ZMod p) = (m : ZMod p) ∧ (H p q : ZMod q) = (m' : ZMod q))
    {p : ℕ} (hp : p ∈ A) {q : ℕ} (hq : q ∈ B) (h0 : H p q = 0) :
    (p : ℤ) ∣ m ∧ (q : ℤ) ∣ m' := by
  obtain ⟨h1, h2⟩ := hH p hp q hq
  constructor
  · rwa [h0, Int.cast_zero, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  · rwa [h0, Int.cast_zero, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2

/-- **Cross-label CRT energy positivity.**

For prime sets A, B and labels m ≠ m', if there exists p ∈ A, q ∈ B
with p ∤ m or q ∤ m', then the CRT energy ∑ H(p,q)² > 0.

This is the qualitative core of Lemma 3.1 (CP 03). The quantitative bound
∑ (H/pq)² ≫ M · min(1, M²/(X⁴L⁴)) follows from the divisor counting
argument in the paper. -/
theorem cross_label_energy_pos
    (A B : Finset ℕ)
    (_ : ∀ p ∈ A, Nat.Prime p) (_ : ∀ q ∈ B, Nat.Prime q)
    (m m' : ℤ) (_ : m ≠ m')
    (H : ℕ → ℕ → ℤ)
    (hH_crt : ∀ p ∈ A, ∀ q ∈ B,
      (H p q : ZMod p) = (m : ZMod p) ∧ (H p q : ZMod q) = (m' : ZMod q))
    (hwitness : ∃ p ∈ A, ∃ q ∈ B, ¬((p : ℤ) ∣ m) ∨ ¬((q : ℤ) ∣ m')) :
    (0 : ℤ) < ∑ p ∈ A, ∑ q ∈ B, H p q ^ 2 := by
  by_contra hsum_not_pos
  have hsum_zero : ∀ p ∈ A, ∀ q ∈ B, H p q = 0 := by
    exact fun p hp q hq => sq_eq_zero_iff.mp (le_antisymm (le_trans
      (Finset.single_le_sum (fun p _ => Finset.sum_nonneg fun q _ =>
        sq_nonneg (H p q)) hp |> le_trans
      (Finset.single_le_sum (fun q _ => sq_nonneg (H p q)) hq))
      (le_of_not_gt hsum_not_pos)) (sq_nonneg _))
  obtain ⟨p, hp, q, hq, h⟩ := hwitness
  specialize hH_crt p hp q hq
  simp_all +decide [← ZMod.intCast_zmod_eq_zero_iff_dvd]
