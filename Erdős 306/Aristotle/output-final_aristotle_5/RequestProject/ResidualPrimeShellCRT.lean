/-
  ResidualPrimeShellCRT.lean

  Bridge from anchored primitive rays to six-variable CRT interval objects
  for the Erdős 306 conditional proof.

  Mathematical content:
    anchored primitive ray  ⟹  short six-variable CRT interval hit
-/
import Mathlib
import RequestProject.AnchoredCRTLattice
import RequestProject.ValidCRTLattice
import RequestProject.ReciprocalCRTProduct
import RequestProject.PrimitiveProjectiveNormalization

/-! ## Goal 1: Six-variable CRT shell definitions -/

/-- The six short variables extracted from an anchored ray:
    (x₀, x₄, y₄, a₁, a₂, a₃). -/
structure SixVarCRTData where
  x0 : ℤ
  x4 : ℤ
  y4 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ

/-- Local invertibility witnesses for a₁, a₂, a₃ mod q₁, q₂, q₃
    and y₄ mod q₄. -/
structure SixVarInvWitnesses (D : SixVarCRTData) (q1 q2 q3 q4 : ℤ) where
  inv1 : ℤ
  inv2 : ℤ
  inv3 : ℤ
  inv4 : ℤ
  h1 : InvModWitness D.a1 q1 inv1
  h2 : InvModWitness D.a2 q2 inv2
  h3 : InvModWitness D.a3 q3 inv3
  h4 : InvModWitness D.y4 q4 inv4

/-- The six-variable local CRT residue predicate:
    p ≡ x₄·(-q₄·inv_i) (mod qᵢ) for i=1,2,3
    p ≡ x₀·(-q₀·inv₄) (mod q₄). -/
def SixVarLocalCRT
    (p q0 q1 q2 q3 q4 : ℤ)
    (D : SixVarCRTData)
    (W : SixVarInvWitnesses D q1 q2 q3 q4) : Prop :=
  p ≡ D.x4 * (-q4 * W.inv1) [ZMOD q1] ∧
  p ≡ D.x4 * (-q4 * W.inv2) [ZMOD q2] ∧
  p ≡ D.x4 * (-q4 * W.inv3) [ZMOD q3] ∧
  p ≡ D.x0 * (-q0 * W.inv4) [ZMOD q4]

/-! ## Goal 2: Anchored hit produces six-variable CRT data -/

/-- Extract SixVarCRTData from an AnchoredCRTProductHit. -/
@[simp]
def sixVarData_of_anchored (H : AnchoredCRTProductHit) : SixVarCRTData where
  x0 := H.x0
  x4 := H.x4
  y4 := H.y4
  a1 := H.a1
  a2 := H.a2
  a3 := H.a3

/-- An anchored CRT product hit with inverse witnesses yields
    the six-variable local CRT residues. -/
theorem sixVarLocalCRT_of_anchoredCRTProductHit
    (H : AnchoredCRTProductHit)
    (W : SixVarInvWitnesses (sixVarData_of_anchored H) H.q1 H.q2 H.q3 H.q4) :
    SixVarLocalCRT H.p H.q0 H.q1 H.q2 H.q3 H.q4
      (sixVarData_of_anchored H) W := by
  have bd1 : BaseDivides H.q1 H.p H.a1 H.q4 H.x4 := ⟨H.x1, by linarith [H.h1]⟩
  have bd2 : BaseDivides H.q2 H.p H.a2 H.q4 H.x4 := ⟨H.x2, by linarith [H.h2]⟩
  have bd3 : BaseDivides H.q3 H.p H.a3 H.q4 H.x4 := ⟨H.x3, by linarith [H.h3]⟩
  exact ⟨local_residue_of_baseDivides W.h1 bd1,
         local_residue_of_baseDivides W.h2 bd2,
         local_residue_of_baseDivides W.h3 bd3,
         anchor_local_residue W.h4 H.h4⟩

/-! ## Goal 3: Converse reconstruction from six-variable divisibility -/

/-- Six-variable divisibility: the divisibility conditions that allow
    reconstruction of anchored coordinates. -/
def SixVarDivisibility
    (p q0 q1 q2 q3 q4 : ℤ) (D : SixVarCRTData) : Prop :=
  q1 ∣ p * D.a1 + q4 * D.x4 ∧
  q2 ∣ p * D.a2 + q4 * D.x4 ∧
  q3 ∣ p * D.a3 + q4 * D.x4 ∧
  q4 ∣ p * D.y4 + q0 * D.x0

/-- Six-variable divisibility from an anchored hit. -/
theorem sixVarDivisibility_of_anchoredCRTProductHit
    (H : AnchoredCRTProductHit) :
    SixVarDivisibility H.p H.q0 H.q1 H.q2 H.q3 H.q4
      (sixVarData_of_anchored H) := by
  simp only [SixVarDivisibility, sixVarData_of_anchored]
  exact ⟨⟨H.x1, by linarith [H.h1]⟩,
         ⟨H.x2, by linarith [H.h2]⟩,
         ⟨H.x3, by linarith [H.h3]⟩,
         ⟨H.x4, by linarith [H.h4]⟩⟩

/-- From six-variable divisibility plus the anchor equation,
    reconstruct InAnchoredCRTLattice.

    The anchor equation q₄·x₄ - q₀·x₀ = p·y₄ is a stronger condition
    than the divisibility q₄ ∣ p·y₄ + q₀·x₀; we need it for the exact
    lattice membership. -/
theorem inAnchoredCRTLattice_of_sixVarDivisibility
    {p q0 q1 q2 q3 q4 : ℤ}
    (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) (hq3 : q3 ≠ 0)
    (D : SixVarCRTData)
    (hdiv : SixVarDivisibility p q0 q1 q2 q3 q4 D)
    (hanchor : q4 * D.x4 - q0 * D.x0 = p * D.y4) :
    InAnchoredCRTLattice p q0 q1 q2 q3 q4
      D.x0 D.x4
      ((p * D.a1 + q4 * D.x4) / q1)
      ((p * D.a2 + q4 * D.x4) / q2)
      ((p * D.a3 + q4 * D.x4) / q3)
      D.y4 D.a1 D.a2 D.a3 := by
  obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩, ⟨k3, hk3⟩, _⟩ := hdiv
  exact ⟨by rw [hk1, Int.mul_ediv_cancel_left _ hq1]; linarith,
         by rw [hk2, Int.mul_ediv_cancel_left _ hq2]; linarith,
         by rw [hk3, Int.mul_ediv_cancel_left _ hq3]; linarith,
         hanchor⟩

/-- From six-variable divisibility plus the anchor equation,
    construct an AnchoredCRTProductHit. -/
noncomputable def anchoredCRTProductHit_of_sixVarDivisibility
    {p q0 q1 q2 q3 q4 : ℤ}
    (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0) (hq3 : q3 ≠ 0)
    (D : SixVarCRTData)
    (hdiv : SixVarDivisibility p q0 q1 q2 q3 q4 D)
    (hanchor : q4 * D.x4 - q0 * D.x0 = p * D.y4) :
    AnchoredCRTProductHit :=
  anchoredCRTProductHit_of_inAnchoredCRTLattice
    (inAnchoredCRTLattice_of_sixVarDivisibility hq1 hq2 hq3 D hdiv hanchor)

/-- The reconstructed y-coordinates: yᵢ = aᵢ + y₄. -/
def reconstructY (D : SixVarCRTData) : ℤ × ℤ × ℤ :=
  (D.a1 + D.y4, D.a2 + D.y4, D.a3 + D.y4)

/-! ## Goal 4: Zero-denominator cleanup shell -/

/-
If q and r are coprime, 0 < |x| < |r|, 0 < |y| < |q|, and q·x = r·y,
    then contradiction.
-/
/-- If q and r are coprime, 0 < |y| < |q|, and q·x = r·y,
    then contradiction. (The bounds on x are not needed.) -/
theorem coprime_short_eq_absurd
    {q r x y : ℤ}
    (hcop : IsCoprime q r)
    (hy_pos : 0 < |y|) (hy_bd : |y| < |q|)
    (heq : q * x = r * y) : False := by
  -- From q*x = r*y and IsCoprime q r, we get q | y (since q | r*y = q*x and gcd(q,r)=1).
  have hq_div_y : q ∣ y := by
    exact hcop.dvd_of_dvd_mul_left <| heq ▸ dvd_mul_right _ _;
  obtain ⟨ k, hk ⟩ := hq_div_y; simp_all +decide [ abs_mul ] ;
  cases abs_cases q <;> cases abs_cases k <;> nlinarith [ show |k| > 0 by aesop ] ;

/-
From a short anchored ray with coprime moduli, aᵢ ≠ 0.
-/
theorem ai_ne_zero_of_short_anchored
    {qi q4 xi x4 p ai : ℤ}
    (hcop : IsCoprime qi q4)
    (hx4_pos : 0 < |x4|) (hx4_bd : |x4| < |qi|)
    (hlat : qi * xi - q4 * x4 = p * ai)
    (hai : ai = 0) : False := by
  subst hai; simp only [mul_zero] at hlat
  exact @coprime_short_eq_absurd qi q4 xi x4 hcop hx4_pos hx4_bd (by linarith)

/-- From a short anchored ray with coprime moduli, y₄ ≠ 0. -/
theorem y4_ne_zero_of_short_anchored
    {q4 q0 x4 x0 p y4 : ℤ}
    (hcop : IsCoprime q4 q0)
    (hx0_pos : 0 < |x0|) (hx0_bd : |x0| < |q4|)
    (hlat : q4 * x4 - q0 * x0 = p * y4)
    (hy4 : y4 = 0) : False := by
  subst hy4; simp only [mul_zero] at hlat
  exact @coprime_short_eq_absurd q4 q0 x4 x0 hcop hx0_pos hx0_bd (by linarith)

/-
When q is prime and q ∤ a, then a has a modular inverse mod q.
-/
theorem invModWitness_of_prime_ne_zero
    {q a : ℤ} (hq : Prime q) (ha : ¬(q ∣ a)) :
    ∃ inv : ℤ, InvModWitness a q inv := by
  -- Since q is prime and q does not divide a, we have gcd(a, q) = 1.
  have h_coprime : IsCoprime a q := by
    exact IsCoprime.symm ( hq.coprime_iff_not_dvd.mpr ha );
  exact ⟨ h_coprime.choose, Int.modEq_iff_dvd.mpr ⟨ h_coprime.choose_spec.choose, by linarith [ h_coprime.choose_spec.choose_spec ] ⟩ ⟩

/-! ## Goal 5: Interval-hit language -/

/-- A six-variable CRT interval hit: p lies in [X, 2X] and satisfies
    the local CRT congruences. -/
def SixVarCRTIntervalHit
    (X p q0 q1 q2 q3 q4 : ℤ)
    (D : SixVarCRTData)
    (W : SixVarInvWitnesses D q1 q2 q3 q4) : Prop :=
  X ≤ p ∧ p ≤ 2 * X ∧
  SixVarLocalCRT p q0 q1 q2 q3 q4 D W

/-- From an anchored CRT product hit with p in [X, 2X] and inverse witnesses,
    produce a six-variable CRT interval hit. -/
theorem intervalHit_of_anchoredCRTProductHit
    (H : AnchoredCRTProductHit)
    (W : SixVarInvWitnesses (sixVarData_of_anchored H) H.q1 H.q2 H.q3 H.q4)
    (X : ℤ)
    (hlo : X ≤ H.p) (hhi : H.p ≤ 2 * X) :
    SixVarCRTIntervalHit X H.p H.q0 H.q1 H.q2 H.q3 H.q4
      (sixVarData_of_anchored H) W :=
  ⟨hlo, hhi, sixVarLocalCRT_of_anchoredCRTProductHit H W⟩

/-- Strict-inequality version of the interval hit. -/
def SixVarCRTIntervalHitStrict
    (X p q0 q1 q2 q3 q4 : ℤ)
    (D : SixVarCRTData)
    (W : SixVarInvWitnesses D q1 q2 q3 q4) : Prop :=
  X < p ∧ p < 2 * X ∧
  SixVarLocalCRT p q0 q1 q2 q3 q4 D W

/-- Strict interval hit implies non-strict. -/
theorem intervalHit_of_strict
    {X p q0 q1 q2 q3 q4 : ℤ}
    {D : SixVarCRTData}
    {W : SixVarInvWitnesses D q1 q2 q3 q4}
    (h : SixVarCRTIntervalHitStrict X p q0 q1 q2 q3 q4 D W) :
    SixVarCRTIntervalHit X p q0 q1 q2 q3 q4 D W :=
  ⟨le_of_lt h.1, le_of_lt h.2.1, h.2.2⟩

/-! ## Goal 6: Fixed-height shell packaging (optional) -/

/-- Height predicate for the six variables: all have absolute value at most B. -/
def SixVarHeightBound (D : SixVarCRTData) (B : ℤ) : Prop :=
  |D.x0| ≤ B ∧ |D.x4| ≤ B ∧ |D.y4| ≤ B ∧
  |D.a1| ≤ B ∧ |D.a2| ≤ B ∧ |D.a3| ≤ B

/-- The residual prime shell bound: count of primes p in [X, 2X] arising from
    short six-tuples is at most `bound`. -/
def ResidualPrimeShellBound
    (X B q0 q1 q2 q3 q4 : ℤ) (bound : ℕ) : Prop :=
  ∀ (S : Finset ℤ),
    (∀ p ∈ S, X ≤ p ∧ p ≤ 2 * X) →
    (∀ p ∈ S, ∃ D : SixVarCRTData,
      SixVarHeightBound D B ∧
      SixVarDivisibility p q0 q1 q2 q3 q4 D) →
    S.card ≤ bound

/-- Bridge theorem: if the residual prime shell bound holds,
    it directly bounds any finite set of primes in the interval
    with six-variable witnesses. -/
theorem residualPrimeShellBound_of_intervalBound
    {X B q0 q1 q2 q3 q4 : ℤ} {bound : ℕ}
    (hbound : ResidualPrimeShellBound X B q0 q1 q2 q3 q4 bound)
    (S : Finset ℤ)
    (hS_interval : ∀ p ∈ S, X ≤ p ∧ p ≤ 2 * X)
    (hS_anchored : ∀ p ∈ S, ∃ D : SixVarCRTData,
      SixVarHeightBound D B ∧
      SixVarDivisibility p q0 q1 q2 q3 q4 D) :
    S.card ≤ bound :=
  hbound S hS_interval hS_anchored