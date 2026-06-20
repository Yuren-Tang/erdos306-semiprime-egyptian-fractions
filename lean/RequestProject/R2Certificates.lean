import RequestProject.R2TopAssembly

/-!
# R2 construction certificates

This file makes the architecture of the R2 arc construction explicit by factoring
the (previously monolithic) terminal assembly
`CircleMethod.exists_arcConstruction_final` through a sequence of named
*certificate* structures, one per conceptual layer:

* `R2FoundationCertificate` — global scale, the numeric ledger of constants
  (`c3, η, Ctail, C, base_b, Dmp, G, …`), the block system `BS`, and the
  prime-supply / large-`k0` facts every later layer consumes.
* `R2ConcreteCertificate` — the gadget-prime reservoir `S` and the prime-side
  structural facts (sizes, ordering, block membership).
* `R2MassCertificate` — the residual mass batch `Q` (a `R2MassBatchSupply`), the
  concrete edge data `D`, weights `W`, and the semiprime / avoidance /
  divisibility / nonemptiness / reciprocal-load-window facts of the edge set.
* `R2MainArcWindow` — the main-arc window parameter `N`, the `σ_E ↔ σ_ctrl`
  comparison, the Taylor/Gaussian numeric fields, and the `2N+1 ≤ L` bound.
* `R2MinorCertificate` — the minor-arc budget `Bm`, its block/extra component
  ledger, the domination `hbeat`, and the per-`MainArcFields` minor bound.
* `R2FinalSupply` (already defined upstream) — the socket consumed to produce an
  `ArcConstruction`.

The terminal theorem then reads as the schematic obtain-chain
`foundation → concrete → mass → main-arc → minor → final`, and each layer is an
independently inspectable node of the dependency graph rather than one black hole.

All proofs are transplanted verbatim from the original assembly; no mathematics
is changed.
-/

open Finset BigOperators GlobalControl
open scoped Classical

noncomputable section

namespace CircleMethod

/-! ## Foundation / scale layer -/

/-- **Foundation certificate.**  Bundles the numeric ledger of constants, the
block system `BS` at a large bottom scale, and all the prime-supply and
large-`k0` facts the later layers consume.  The three `Pi`-valued fields
(`hSB`, `hk0density`, `hk0ctrl`, `hload`) are the abstract supply principles
(minor-support budget, dyadic prime density, control-load smallness, and the
block-product Mertens bound) instantiated for these constants. -/
structure R2FoundationCertificate (T : Finset ℕ) (b : ℕ) where
  /-- minor main-control constant `c3 = 0.8·exp(-π²/2)/2`. -/
  c3 : ℝ
  /-- main-arc tail budget per unit `b`. -/
  η : ℝ
  /-- Gaussian-tail constant from the global-control partition. -/
  Ctail : ℝ
  /-- main-arc window constant. -/
  C : ℝ
  /-- per-gadget worst-case sibling damping base. -/
  base_b : ℝ
  /-- target per-frequency damping budget. -/
  Dmp : ℝ
  /-- number of gadget primes. -/
  G : ℕ
  /-- bottom-scale threshold from the minor-support budget. -/
  k0minM : ℕ
  /-- bottom-scale threshold from the dyadic density bound. -/
  k0density : ℕ
  /-- bottom-scale threshold from the control-load bound. -/
  k0ctrl : ℕ
  /-- bottom-scale threshold from the block-product load bound. -/
  k1 : ℕ
  /-- the block system. -/
  BS : BlockSystem
  hbpos : 0 < b
  hb3 : 3 ≤ b
  hbsf : Squarefree b
  hc3eq : c3 = r2MinorMainCtrlConstant
  hc3pos : 0 < c3
  hηdef : η = c3 / (2004 * (b : ℝ))
  hηpos : 0 < η
  hCtail : 0 < Ctail
  /-- the minor-support budget supply principle for these `η, Ctail`. -/
  hSB : ∀ {T' : Finset ℕ} {b' : ℕ}
      (D : R2ConcreteData T' b') (W : R2ConcreteData.Weights D) (N : ℤ)
      (Bblock Bextra ρ : ℝ) (Cls : R2MinorClassificationData D W N),
      k0minM ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameMultiGadgetLanes D W N Bblock Bextra η Ctail ρ Cls →
      Nonempty (R2MinorSupportBudgetData D W N Bblock Bextra)
  hCge3 : (3 : ℝ) ≤ C
  hCge1 : (1 : ℝ) ≤ C
  hCbound : (b : ℝ) * (Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) < c3 / 2004
  hbbdef : base_b = Real.sqrt (1 - (8 / 9) / (b : ℝ) ^ 2)
  hG : base_b ^ G ≤ Dmp
  hDmpdef : Dmp = c3 / (2004 * (b : ℝ) * (2 * C + 3))
  hDmppos : 0 < Dmp
  hk05 : 5 ≤ BS.k0
  hadm : admissibleGlobalRange BS
  hsub : blockPrimes BS.k0 ⊆ blockSupport BS
  hcopB : BlockSupportCoprimeWith BS b
  hRp : ∀ r ∈ b.primeFactors, Nat.Prime r
  hRdvd : ∀ r ∈ b.primeFactors, r ∣ b
  hcovR : CoversPrimeDivisors b.primeFactors b
  hRout : ∀ r ∈ b.primeFactors, r ∉ blockSupport BS
  hdyadic2k : dyadicBlock (2 * BS.k0) ⊆ blockSupport BS
  hk0minM : k0minM ≤ BS.k0
  hk0dens : k0density ≤ BS.k0
  hk0density : ∀ k : ℕ, k0density ≤ k →
      (G : ℝ) ≤ (2 : ℝ) ^ k / (2 * Real.log ((2 : ℝ) ^ k))
  hk0ctrlle : k0ctrl ≤ BS.k0
  hk0ctrl : ∀ BS' : BlockSystem, k0ctrl ≤ BS'.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS') ≤ 3 / (4 * (b : ℝ))
  hk1le : k1 ≤ BS.k0
  hk15 : 5 ≤ k1
  hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤ ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
  hk0big : 1000 * G + 1000 * b + 100000 ≤ BS.k0
  hk0T : T.sup id + 1 ≤ BS.k0
  hk0dom : 1000000 * (Nat.ceil C + 1) ^ 4 ≤ BS.k0

/-- **Numeric ledger.**  The scale-parameter / constant slice of the foundation:
the constants (`c3, η, Ctail, C, base_b, Dmp, G`), the bottom-scale thresholds
(`k0minM, k0density, k0ctrl, k1`), and all the facts that are *independent of the
chosen block system* — the numeric relations among the constants, the abstract
minor-support supply principle `hSB`, the dyadic prime-density bound `hk0density`,
the control-load bound `hk0ctrl`, and the block-product Mertens load `hload`. -/
structure R2NumericLedger (b : ℕ) where
  c3 : ℝ
  η : ℝ
  Ctail : ℝ
  C : ℝ
  base_b : ℝ
  Dmp : ℝ
  G : ℕ
  k0minM : ℕ
  k0density : ℕ
  k0ctrl : ℕ
  k1 : ℕ
  hbpos : 0 < b
  hb3 : 3 ≤ b
  hbsf : Squarefree b
  hc3eq : c3 = r2MinorMainCtrlConstant
  hc3pos : 0 < c3
  hηdef : η = c3 / (2004 * (b : ℝ))
  hηpos : 0 < η
  hCtail : 0 < Ctail
  hSB : ∀ {T' : Finset ℕ} {b' : ℕ}
      (D : R2ConcreteData T' b') (W : R2ConcreteData.Weights D) (N : ℤ)
      (Bblock Bextra ρ : ℝ) (Cls : R2MinorClassificationData D W N),
      k0minM ≤ D.BS.k0 → admissibleGlobalRange D.BS →
      R2MinorEndgameMultiGadgetLanes D W N Bblock Bextra η Ctail ρ Cls →
      Nonempty (R2MinorSupportBudgetData D W N Bblock Bextra)
  hCge3 : (3 : ℝ) ≤ C
  hCge1 : (1 : ℝ) ≤ C
  hCbound : (b : ℝ) * (Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) < c3 / 2004
  hbbdef : base_b = Real.sqrt (1 - (8 / 9) / (b : ℝ) ^ 2)
  hG : base_b ^ G ≤ Dmp
  hDmpdef : Dmp = c3 / (2004 * (b : ℝ) * (2 * C + 3))
  hDmppos : 0 < Dmp
  hk0density : ∀ k : ℕ, k0density ≤ k →
      (G : ℝ) ≤ (2 : ℝ) ^ k / (2 * Real.log ((2 : ℝ) ^ k))
  hk0ctrl : ∀ BS' : BlockSystem, k0ctrl ≤ BS'.k0 →
      R2ConcreteData.recipLoad (ctrlEdges BS') ≤ 3 / (4 * (b : ℝ))
  hk15 : 5 ≤ k1
  hload : ∀ k0 : ℕ, k1 ≤ k0 →
      (1 : ℝ) / 2 ≤ ∑ pq ∈ (blockPrimes k0).offDiag.filter (fun pq : ℕ × ℕ => pq.1 < pq.2),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))

/-- **Block-system / prime-factor certificate.**  Given the numeric ledger `L`,
construct a block system `BS` whose bottom scale dominates every ledger threshold
(so all the later `k0`-largeness side conditions hold), together with the
prime-factor / support facts of `b` relative to `BS` (`hRp, hRdvd, hcovR, hRout`,
the block-support coprimality `hcopB`, and `hsub, hdyadic2k`). -/
structure R2BlockSystemCertificate (T : Finset ℕ) (b : ℕ) (L : R2NumericLedger b) where
  BS : BlockSystem
  hk05 : 5 ≤ BS.k0
  hadm : admissibleGlobalRange BS
  hsub : blockPrimes BS.k0 ⊆ blockSupport BS
  hcopB : BlockSupportCoprimeWith BS b
  hRp : ∀ r ∈ b.primeFactors, Nat.Prime r
  hRdvd : ∀ r ∈ b.primeFactors, r ∣ b
  hcovR : CoversPrimeDivisors b.primeFactors b
  hRout : ∀ r ∈ b.primeFactors, r ∉ blockSupport BS
  hdyadic2k : dyadicBlock (2 * BS.k0) ⊆ blockSupport BS
  hk0minM : L.k0minM ≤ BS.k0
  hk0dens : L.k0density ≤ BS.k0
  hk0ctrlle : L.k0ctrl ≤ BS.k0
  hk1le : L.k1 ≤ BS.k0
  hk0big : 1000 * L.G + 1000 * b + 100000 ≤ BS.k0
  hk0T : T.sup id + 1 ≤ BS.k0
  hk0dom : 1000000 * (Nat.ceil L.C + 1) ^ 4 ≤ BS.k0

/-- Choose the numeric ledger of constants and bottom-scale thresholds.  This is
the scale-parameter slice of the foundation; no block system is constructed. -/
lemma exists_r2_numeric_ledger (b : ℕ) (hb : 3 ≤ b) (hbsf : Squarefree b) :
    Nonempty (R2NumericLedger b) := by
  classical
  have hbpos : 0 < b := by omega
  have hc3pos : 0 < r2MinorMainCtrlConstant := by
    rw [r2MinorMainCtrlConstant]; positivity
  set c3 := r2MinorMainCtrlConstant with hc3def
  set η : ℝ := c3 / (2004 * (b : ℝ)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨k0minM, Ctail, hCtail, hSB⟩ :=
    exists_r2_minorSupportBudget_from_multiGadget_lanes (1 : ℝ) one_pos η hηpos
  obtain ⟨C0, hC0one, hC0bd⟩ := r2_exists_C Ctail (c3 / 501) b hCtail (by positivity) hbpos
  set C : ℝ := max C0 3 with hCdef
  have hCge3 : (3 : ℝ) ≤ C := le_max_right _ _
  have hCge1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hCge3
  set base_b : ℝ := Real.sqrt (1 - (8 / 9) / (b : ℝ) ^ 2) with hbbdef
  have hbb0 : 0 ≤ base_b := Real.sqrt_nonneg _
  have hbb1 : base_b < 1 := by
    rw [hbbdef]
    have hbr : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    refine (Real.sqrt_lt' (by norm_num)).2 ?_
    rw [one_pow]
    have : (0 : ℝ) < (8 / 9) / (b : ℝ) ^ 2 := by positivity
    linarith
  set Dmp : ℝ := c3 / (2004 * (b : ℝ) * (2 * C + 3)) with hDmpdef
  have hDmppos : 0 < Dmp := by
    rw [hDmpdef]; positivity
  obtain ⟨G, hG⟩ := r2_exists_pow_le base_b Dmp hbb0 hbb1 hDmppos
  obtain ⟨k0density, hk0density⟩ := r2_exists_k0_density G
  obtain ⟨k1, hk15, hload⟩ := blockPrimes_product_load_ge
  obtain ⟨k0ctrl, hk0ctrl⟩ := exists_k0_controlLoad_lt (3 / (4 * (b : ℝ))) (by positivity)
  have hCbound : (b : ℝ) * (Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) < c3 / 2004 := by
    have hCC0 : C0 ≤ C := by rw [hCdef]; exact le_max_left _ _
    have hC0nn : (0 : ℝ) ≤ C0 := le_trans (by norm_num) hC0one
    have hmono : Real.exp (-C ^ 2 * (16 / 9) / 2) ≤ Real.exp (-C0 ^ 2 * (16 / 9) / 2) := by
      apply Real.exp_le_exp.mpr; nlinarith only [hCC0, hC0nn]
    calc (b : ℝ) * (Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2))
        = (b : ℝ) * Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2) := by ring
      _ ≤ (b : ℝ) * Ctail * Real.exp (-C0 ^ 2 * (16 / 9) / 2) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ < c3 / 501 / 4 := hC0bd
      _ = c3 / 2004 := by ring
  exact ⟨{
    c3 := c3, η := η, Ctail := Ctail, C := C, base_b := base_b, Dmp := Dmp, G := G,
    k0minM := k0minM, k0density := k0density, k0ctrl := k0ctrl, k1 := k1,
    hbpos := hbpos, hb3 := hb, hbsf := hbsf, hc3eq := hc3def, hc3pos := hc3pos,
    hηdef := hηdef, hηpos := hηpos, hCtail := hCtail, hSB := hSB,
    hCge3 := hCge3, hCge1 := hCge1, hCbound := hCbound, hbbdef := hbbdef, hG := hG,
    hDmpdef := hDmpdef, hDmppos := hDmppos, hk0density := hk0density, hk0ctrl := hk0ctrl,
    hk15 := hk15, hload := hload }⟩

/-- Build the block-system / prime-factor certificate at a bottom scale large
enough to dominate every threshold of the ledger `L`. -/
lemma exists_r2_block_system_certificate (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b)
    (L : R2NumericLedger b) :
    Nonempty (R2BlockSystemCertificate T b L) := by
  classical
  set k0min' : ℕ :=
    L.k0minM + L.k0density + L.k1 + L.k0ctrl + T.sup id + 1000 * L.G + 1000 * b + 100000
      + 1000000 * (Nat.ceil L.C + 1) ^ 4
      with hk0mindef
  obtain ⟨BS, hk0, hk05, hadm, hsub, hcopB, hRp, hRdvd, hcovR, hRout, _h2kK, hdyadic2k⟩ :=
    exists_r2_foundation_dyadic b hb k0min'
  have hk0minM : L.k0minM ≤ BS.k0 := by have h := hk0; rw [hk0mindef] at h; omega
  have hk0dens : L.k0density ≤ BS.k0 := by have h := hk0; rw [hk0mindef] at h; omega
  have hk1le : L.k1 ≤ BS.k0 := by have h := hk0; rw [hk0mindef] at h; omega
  have hk0ctrlle : L.k0ctrl ≤ BS.k0 := by have h := hk0; rw [hk0mindef] at h; omega
  have hk0big : 1000 * L.G + 1000 * b + 100000 ≤ BS.k0 := by
    have h := hk0; rw [hk0mindef] at h; omega
  have hk0T : T.sup id + 1 ≤ BS.k0 := by have h := hk0; rw [hk0mindef] at h; omega
  have hk0dom : 1000000 * (Nat.ceil L.C + 1) ^ 4 ≤ BS.k0 := by
    have h := hk0; rw [hk0mindef] at h; omega
  exact ⟨{
    BS := BS, hk05 := hk05, hadm := hadm, hsub := hsub, hcopB := hcopB,
    hRp := hRp, hRdvd := hRdvd, hcovR := hcovR, hRout := hRout, hdyadic2k := hdyadic2k,
    hk0minM := hk0minM, hk0dens := hk0dens, hk0ctrlle := hk0ctrlle, hk1le := hk1le,
    hk0big := hk0big, hk0T := hk0T, hk0dom := hk0dom }⟩

/-- Produce the foundation certificate by assembling the two named components:
the numeric ledger (`exists_r2_numeric_ledger`) and the block-system /
prime-factor certificate (`exists_r2_block_system_certificate`).  This layer only
threads the ledger constants and block-system facts into the flat certificate. -/
lemma exists_r2_foundation_certificate (T : Finset ℕ) (b : ℕ) (hb : 3 ≤ b)
    (hbsf : Squarefree b) :
    Nonempty (R2FoundationCertificate T b) := by
  obtain ⟨L⟩ := exists_r2_numeric_ledger b hb hbsf
  obtain ⟨BSc⟩ := exists_r2_block_system_certificate T b hb L
  exact ⟨{
    c3 := L.c3, η := L.η, Ctail := L.Ctail, C := L.C, base_b := L.base_b, Dmp := L.Dmp,
    G := L.G, k0minM := L.k0minM, k0density := L.k0density, k0ctrl := L.k0ctrl, k1 := L.k1,
    BS := BSc.BS,
    hbpos := L.hbpos, hb3 := L.hb3, hbsf := L.hbsf, hc3eq := L.hc3eq, hc3pos := L.hc3pos,
    hηdef := L.hηdef, hηpos := L.hηpos, hCtail := L.hCtail, hSB := L.hSB,
    hCge3 := L.hCge3, hCge1 := L.hCge1, hCbound := L.hCbound, hbbdef := L.hbbdef, hG := L.hG,
    hDmpdef := L.hDmpdef, hDmppos := L.hDmppos,
    hk05 := BSc.hk05, hadm := BSc.hadm, hsub := BSc.hsub, hcopB := BSc.hcopB, hRp := BSc.hRp,
    hRdvd := BSc.hRdvd, hcovR := BSc.hcovR, hRout := BSc.hRout, hdyadic2k := BSc.hdyadic2k,
    hk0minM := BSc.hk0minM, hk0dens := BSc.hk0dens, hk0density := L.hk0density,
    hk0ctrlle := BSc.hk0ctrlle, hk0ctrl := L.hk0ctrl, hk1le := BSc.hk1le, hk15 := L.hk15,
    hload := L.hload, hk0big := BSc.hk0big, hk0T := BSc.hk0T, hk0dom := BSc.hk0dom }⟩


/-! ## Concrete semiprime data layer (gadget prime reservoir) -/

/-- **Concrete certificate.**  The gadget-prime reservoir `S` chosen in the high
dyadic block `2·k0`, together with the prime-side structural facts: `S` consists
of primes that are large (`≥ 2^{2k0}`), sit in the block support, number exactly
`G`, and dominate the divisor primes `R = b.primeFactors`. -/
structure R2ConcreteCertificate {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) where
  /-- the gadget primes. -/
  S : Finset ℕ
  hScard : S.card = F.G
  hSprime : ∀ s ∈ S, Nat.Prime s
  hSge : ∀ s ∈ S, 2 ^ (2 * F.BS.k0) ≤ s
  hSblock : S ⊆ blockSupport F.BS
  hb2k0 : b < 2 ^ F.BS.k0
  hRpos' : ∀ r ∈ b.primeFactors, 2 ≤ r
  hlt' : ∀ r ∈ b.primeFactors, ∀ s ∈ S, r < s

/-- Produce the concrete (gadget-prime) certificate from the foundation. -/
lemma exists_r2_concrete_certificate {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) :
    Nonempty (R2ConcreteCertificate F) := by
  classical
  have hbpos := F.hbpos
  have hk05 := F.hk05
  have hk0dens := F.hk0dens
  have hk0big := F.hk0big
  obtain ⟨S, hSsub, hScard, hSprime, hSge⟩ :=
    exists_block_primes (2 * F.BS.k0) (by omega) F.G
      (F.hk0density (2 * F.BS.k0) (by omega))
  have hSblock : S ⊆ blockSupport F.BS := fun s hs => F.hdyadic2k (hSsub hs)
  have hb2k0 : b < 2 ^ F.BS.k0 := lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self)
  have hRpos' : ∀ r ∈ b.primeFactors, 2 ≤ r := fun r hr => (F.hRp r hr).two_le
  have hlt' : ∀ r ∈ b.primeFactors, ∀ s ∈ S, r < s := by
    intro r hr s hs
    have hrle : r ≤ b := Nat.le_of_dvd hbpos (F.hRdvd r hr)
    have hsge : 2 ^ (2 * F.BS.k0) ≤ s := hSge s hs
    have : 2 ^ F.BS.k0 ≤ 2 ^ (2 * F.BS.k0) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨⟨S, hScard, hSprime, hSge, hSblock, hb2k0, hRpos', hlt'⟩⟩

/-! ## Mass batch layer (residual batch `Q`, edge data, load window) -/

/-- **Mass certificate.**  The residual mass batch `Q` (packaged as a
`R2MassBatchSupply`, which records the reciprocal-load window
`3/(2b) ≤ baseLoad + recipLoad Q < 3/b`), the assembled concrete edge data `D`
and weights `W`, and the structural facts of the edge set: every edge is a
semiprime, positive, divides the period `L`, avoids `T`; the set is nonempty;
the total reciprocal load is `< 3/b`; and the inverse-square load is controlled
by `σ_ctrl`. -/
structure R2MassCertificate {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F) where
  /-- the residual mass batch. -/
  Q : Finset ℕ
  /-- the assembled concrete edge data. -/
  D : R2ConcreteData T b
  /-- the edge weights. -/
  W : R2ConcreteData.Weights D
  /-- the mass-batch supply (encodes the load window). -/
  QB : R2MassBatchSupply D
  hDdef : D = (⟨F.BS, ∅, b.primeFactors, Cc.S⟩ : R2ConcreteData T b).withQ Q
  hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p
  hL : 0 < D.L
  hsemi : ∀ e ∈ D.E, IsSemiprime e
  he0 : ∀ e ∈ D.E, 0 < e
  heL : ∀ e ∈ D.E, e ∣ D.L
  hne : D.E.Nonempty
  hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T
  hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T
  havoid : ∀ e ∈ D.E, e ∉ T
  hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ)
  hsumE : ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1000001 * (sigmaCtrl D.BS) ^ 2

/-- Produce the mass-batch certificate: choose the residual batch `Q`, assemble
`D` and `W`, and discharge the edge structural facts. -/
lemma exists_r2_mass_certificate {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F) :
    Nonempty (R2MassCertificate F Cc) := by
  classical
  have hbpos := F.hbpos
  obtain ⟨Q, QB⟩ := r2_getQ F.hb3 F.BS Cc.S F.hsub Cc.hSge F.hRout
    (F.hk0ctrl F.BS F.hk0ctrlle) F.k1 F.hk15 F.hk1le F.hload
    (by rw [Cc.hScard]; exact F.hk0big) F.hk0T
  set D : R2ConcreteData T b := (⟨F.BS, ∅, b.primeFactors, Cc.S⟩ : R2ConcreteData T b).withQ Q
    with hDdef
  set W : R2ConcreteData.Weights D := QB.weights hbpos with hWdef
  have hk0bigD : 1000 * F.G + 1000 * b + 100000 ≤ D.BS.k0 := F.hk0big
  have hScardD : D.S.card = F.G := Cc.hScard
  have hk0TD : T.sup id + 1 ≤ D.BS.k0 := F.hk0T
  have hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p := rfl
  have hL : 0 < D.L := D.period_pos hbpos
  have hsemi : ∀ e ∈ D.E, IsSemiprime e := D.semiprime QB.q_semiprime F.hRp Cc.hSprime Cc.hlt'
  have he0 : ∀ e ∈ D.E, 0 < e := D.edges_pos hsemi
  have heL : ∀ e ∈ D.E, e ∣ D.L := D.dvd_period QB.q_dvd_period F.hRdvd Cc.hSblock
  have hne : D.E.Nonempty := D.nonempty_of_massBatch_nonempty QB.hQne
  have hTlt : ∀ e ∈ T, e < 2 ^ (2 * D.BS.k0) := by
    intro e he
    have h1 : e ≤ T.sup id := Finset.le_sup (f := id) he
    have h2 : D.BS.k0 < 2 ^ D.BS.k0 := Nat.lt_two_pow_self
    have h3 : 2 ^ D.BS.k0 ≤ 2 ^ (2 * D.BS.k0) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hctrlAvoid : ∀ e ∈ ctrlEdges D.BS, e ∉ T := by
    intro e he hT
    have hge : 2 ^ D.BS.k0 * 2 ^ D.BS.k0 ≤ e := ctrlEdges_ge_k0_square D.BS he
    have : 2 ^ D.BS.k0 * 2 ^ D.BS.k0 = 2 ^ (2 * D.BS.k0) := by rw [← pow_add]; ring_nf
    have := hTlt e hT; omega
  have hgadgetAvoid : ∀ e ∈ gadgetEdges D.R D.S, e ∉ T := by
    intro e he hT
    rw [mem_gadgetEdges] at he
    obtain ⟨r, hr, s, hs, rfl⟩ := he
    have hsge : 2 ^ (2 * D.BS.k0) ≤ s := Cc.hSge s hs
    have hr2 : 2 ≤ r := Cc.hRpos' r hr
    have := hTlt (r * s) hT
    have hsr : s ≤ r * s := le_mul_of_one_le_left (Nat.zero_le s) (by omega)
    omega
  have havoid : ∀ e ∈ D.E, e ∉ T :=
    D.avoid hctrlAvoid QB.hQavoid hgadgetAvoid
  have hloadUpper : R2ConcreteData.recipLoad D.E < 3 / (b : ℝ) :=
    (D.total_recipLoad_window_of_residual QB.hloadDisj QB.hloadLower QB.hloadUpper).2
  have hsumE : ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1000001 * (sigmaCtrl D.BS) ^ 2 := by
    have hsplit : ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2
        = (∑ e ∈ ctrlEdges D.BS, (1 : ℝ) / (e : ℝ) ^ 2)
          + ∑ e ∈ D.E \ ctrlEdges D.BS, (1 : ℝ) / (e : ℝ) ^ 2 := by
      rw [← Finset.sum_sdiff D.ctrlEdges_subset_E]; ring
    rw [hsplit, sum_inv_sq_ctrlEdges_eq_sigmaCtrl_sq]
    have hextra := r2_extra_inv_sq_le D
      (show 14 ≤ D.BS.k0 by omega)
      (show 1000 * D.S.card + 1000 * b + 100000 ≤ D.BS.k0 by
        rw [hScardD]; exact hk0bigD)
      QB Cc.hSge Cc.hRpos'
      (show D.R.card ≤ b from
        le_trans (Finset.card_le_card (fun x hx => Finset.mem_Icc.mpr
          ⟨Nat.pos_of_mem_primeFactors hx, Nat.le_of_mem_primeFactors hx⟩))
          (by rw [Nat.card_Icc]; omega))
    linarith [hextra]
  exact ⟨⟨Q, D, W, QB, hDdef, hLeq, hL, hsemi, he0, heL, hne, hctrlAvoid,
    hgadgetAvoid, havoid, hloadUpper, hsumE⟩⟩

/-! ## Main-arc window layer -/

/-- **σ_E ↔ σ_ctrl comparison.**  The edge variance `σ_E = √(sigmaE2 E θ)` is
two-sidedly comparable with the control deviation `σ_ctrl`: it is at least
`√(2/9)·σ_ctrl` (so positive) and at most `501·σ_ctrl`.  This is the conceptual
"compare σ_E with σ_ctrl" step; the upper bound uses the reciprocal-square load
window `M.hsumE`, the lower bound uses `sigmaE2_ge_ctrl`. -/
lemma r2_main_arc_sigmaE_compare {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) :
    Real.sqrt (2 / 9) * sigmaCtrl M.D.BS ≤ Real.sqrt (sigmaE2 M.D.E M.W.theta)
      ∧ Real.sqrt (sigmaE2 M.D.E M.W.theta) ≤ 501 * sigmaCtrl M.D.BS
      ∧ 0 < Real.sqrt (sigmaE2 M.D.E M.W.theta) := by
  classical
  set D : R2ConcreteData T b := M.D with hDeq
  set W : R2ConcreteData.Weights D := M.W with hWeq
  have hBS : D.BS = F.BS := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_BS]
  have hadmD : admissibleGlobalRange D.BS := by rw [hBS]; exact F.hadm
  have hsumE : ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1000001 * (sigmaCtrl D.BS) ^ 2 := M.hsumE
  set σ : ℝ := sigmaCtrl D.BS with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact sigmaCtrl_pos D.BS hadmD
  have hsigmaE2_le : sigmaE2 D.E W.theta ≤ 250001 * σ ^ 2 := by
    have h := sigmaE2_le_quarter_sum_inv_sq D.E W.theta
    have h2 : (1 / 4 : ℝ) * ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2
        ≤ (1 / 4 : ℝ) * (1000001 * σ ^ 2) :=
      mul_le_mul_of_nonneg_left hsumE (by norm_num)
    linarith [h, h2, sq_nonneg σ]
  have hsigmaE_ub : Real.sqrt (sigmaE2 D.E W.theta) ≤ 501 * σ := by
    rw [show (501 : ℝ) * σ = Real.sqrt ((501 * σ) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    calc sigmaE2 D.E W.theta ≤ 250001 * σ ^ 2 := hsigmaE2_le
      _ ≤ (501 * σ) ^ 2 := by nlinarith only [sq_nonneg σ]
  have hsigmaE_lb : Real.sqrt (2 / 9) * σ ≤ Real.sqrt (sigmaE2 D.E W.theta) := by
    rw [show Real.sqrt (2 / 9) * σ = Real.sqrt ((2 / 9) * σ ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hσpos.le]]
    apply Real.sqrt_le_sqrt
    have := sigmaE2_ge_ctrl D W; rw [show σ = sigmaCtrl D.BS from hσdef]; linarith
  have hsigmaEpos : 0 < Real.sqrt (sigmaE2 D.E W.theta) :=
    lt_of_lt_of_le (by positivity) hsigmaE_lb
  exact ⟨hsigmaE_lb, hsigmaE_ub, hsigmaEpos⟩


/-- **Main-arc window certificate.**  The window parameter `N ≈ C/σ`, the
two-sided `σ_E ↔ σ_ctrl` comparison, the window bounds (`N·σ`, `(2N+1)·σ`, and
`2N < 2^{2k0}`), the period bound `2N+1 ≤ L`, and the Taylor/Gaussian numeric
fields `MainArcNumericFields`.  The fields are stated so the minor-arc layer can
reuse the window facts (`hNlo`, `hN2`, `h2N1sigma`, `hsigmaE_ub`, `hsigmaEpos`)
without re-deriving `N`. -/
structure R2MainArcWindow {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) where
  /-- the main-arc window parameter. -/
  N : ℤ
  hNnonneg : 0 ≤ N
  hNlo : F.C / sigmaCtrl M.D.BS ≤ (N : ℝ)
  hN2 : 2 * N < (2 : ℤ) ^ (2 * M.D.BS.k0)
  hNL : 2 * N + 1 ≤ (M.D.L : ℤ)
  hsigmapos : 0 < sigmaCtrl M.D.BS
  h2N1sigma : (2 * (N : ℝ) + 1) * sigmaCtrl M.D.BS ≤ 2 * F.C + 3
  hsigmaE_ub : Real.sqrt (sigmaE2 M.D.E M.W.theta) ≤ 501 * sigmaCtrl M.D.BS
  hsigmaEpos : 0 < Real.sqrt (sigmaE2 M.D.E M.W.theta)
  hNF : MainArcNumericFields M.D.E M.W.theta N

/-- **Main-arc window scale/period bounds.**  For `N` essentially `⌈C/σ_ctrl⌉`
(`hNhi`), the window stays below the squared bottom scale (`2N < 2^{2k₀}`), fits
inside the common period (`2N+1 ≤ L`), and obeys the explicit growth bound
`N ≤ 100·k₀²·2^{k₀}+1` consumed by the Taylor numeric fields.  This boxes the
constant-chasing "N-window" ledger out of the main-arc assembly. -/
lemma r2_main_arc_window_scale_period {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (N : ℤ)
    (hNhi : (N : ℝ) ≤ F.C / sigmaCtrl M.D.BS + 1) :
    2 * N < (2 : ℤ) ^ (2 * M.D.BS.k0)
      ∧ 2 * N + 1 ≤ (M.D.L : ℤ)
      ∧ (N : ℝ) ≤ 100 * (M.D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ M.D.BS.k0 + 1 := by
  classical
  have hbpos := F.hbpos
  set D : R2ConcreteData T b := M.D with hDeq
  set C : ℝ := F.C with hCeq
  have hBS : D.BS = F.BS := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_BS]
  have hS : D.S = Cc.S := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_S]
  have hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p := M.hLeq
  have hadmD : admissibleGlobalRange D.BS := by rw [hBS]; exact F.hadm
  have hCge3 : (3 : ℝ) ≤ C := F.hCge3
  have hbr : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast F.hb3
  have hk0dom : 1000000 * (Nat.ceil C + 1) ^ 4 ≤ D.BS.k0 := by rw [hBS]; exact F.hk0dom
  have hSgeD : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s := by rw [hS, hBS]; exact Cc.hSge
  have hSblockD : D.S ⊆ blockSupport D.BS := by rw [hS, hBS]; exact Cc.hSblock
  have hScardD : D.S.card = F.G := by rw [hS]; exact Cc.hScard
  set σ : ℝ := sigmaCtrl D.BS with hσdef
  have hk0big6 : 1000000 ≤ D.BS.k0 := by
    have h1 : 1 ≤ (Nat.ceil C + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [hk0dom, h1]
  have hσpos : 0 < σ := by rw [hσdef]; exact sigmaCtrl_pos D.BS hadmD
  have hσstrong : (1 : ℝ) / (100 * (D.BS.k0 : ℝ) * (2 : ℝ) ^ D.BS.k0) ≤ σ := by
    rw [hσdef]; exact sigmaCtrl_ge_strong D.BS (by omega)
  have hN2nat : 200 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 2 < 2 ^ (2 * D.BS.k0) := by
    have hsq := two_hundred_sq_lt_two_pow D.BS.k0 hk0big6
    have h2le : 2 ≤ 2 ^ D.BS.k0 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ D.BS.k0 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpoweq : 2 ^ (2 * D.BS.k0) = 2 ^ D.BS.k0 * 2 ^ D.BS.k0 := by rw [two_mul, pow_add]
    calc 200 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 2
        ≤ 200 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 2 ^ D.BS.k0 := by omega
      _ = (200 * D.BS.k0 ^ 2 + 1) * 2 ^ D.BS.k0 := by ring
      _ < 2 ^ D.BS.k0 * 2 ^ D.BS.k0 := mul_lt_mul_of_pos_right hsq (by positivity)
      _ = 2 ^ (2 * D.BS.k0) := hpoweq.symm
  have hNreal : (N : ℝ) ≤ 100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 + 1 := by
    have hinvσ : (1 : ℝ) / σ ≤ 100 * (D.BS.k0 : ℝ) * (2 : ℝ) ^ D.BS.k0 := by
      rw [div_le_iff₀ hσpos]
      have hs := hσstrong
      rw [div_le_iff₀ (by positivity)] at hs
      nlinarith only [hs, hσpos]
    have hCk0 : C ≤ (D.BS.k0 : ℝ) := by
      have hCm : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
      have hmk0 : (Nat.ceil C : ℝ) ≤ (D.BS.k0 : ℝ) := by
        have hnat : Nat.ceil C ≤ D.BS.k0 := by
          have hp : Nat.ceil C + 1 ≤ (Nat.ceil C + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
          nlinarith only [hp, hk0dom]
        exact_mod_cast hnat
      linarith
    have hCσ : C / σ ≤ 100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 := by
      rw [div_eq_mul_one_div]
      calc C * (1 / σ)
          ≤ (D.BS.k0 : ℝ) * (100 * (D.BS.k0 : ℝ) * (2 : ℝ) ^ D.BS.k0) :=
            mul_le_mul hCk0 hinvσ (by positivity) (by positivity)
        _ = 100 * (D.BS.k0 : ℝ) ^ 2 * (2 : ℝ) ^ D.BS.k0 := by ring
    linarith [hNhi, hCσ]
  have hN2 : 2 * N < (2 : ℤ) ^ (2 * D.BS.k0) := by
    have hNint : N ≤ (100 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 1 : ℕ) := by
      have hcast : (N : ℝ) ≤ ((100 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 1 : ℕ) : ℝ) := by
        push_cast; linarith [hNreal]
      exact_mod_cast hcast
    calc 2 * N ≤ (200 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 2 : ℕ) := by
          have hi : (N : ℤ) ≤ (100 * D.BS.k0 ^ 2 * 2 ^ D.BS.k0 + 1 : ℕ) := by exact_mod_cast hNint
          push_cast at hi ⊢; linarith [hi]
      _ < ((2 ^ (2 * D.BS.k0) : ℕ) : ℤ) := by exact_mod_cast hN2nat
      _ = (2 : ℤ) ^ (2 * D.BS.k0) := by push_cast; ring
  have hNL : 2 * N + 1 ≤ (D.L : ℤ) := by
    have hc3lt1 : F.c3 < 1 := by
      rw [F.hc3eq, r2MinorMainCtrlConstant]
      have he : Real.exp (-(Real.pi ^ 2 / 2)) < 1 :=
        Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
      nlinarith only [he, Real.exp_pos (-(Real.pi ^ 2 / 2))]
    have hDmplt1 : F.Dmp < 1 := by
      rw [F.hDmpdef, div_lt_one (by positivity)]
      nlinarith only [hc3lt1, hbr, hCge3]
    have hG1 : 1 ≤ F.G := by
      rcases Nat.eq_zero_or_pos F.G with hG0 | hGpos
      · have hh := F.hG; rw [hG0, pow_zero] at hh; linarith [hDmplt1]
      · exact hGpos
    have hSne : D.S.Nonempty := by rw [← Finset.card_pos, hScardD]; omega
    obtain ⟨s, hs⟩ := hSne
    have hprodpos : 0 < ∏ p ∈ blockSupport D.BS, p :=
      Finset.prod_pos (fun p hp => (blockSupport_prime D.BS hp).pos)
    have hLge : (2 : ℕ) ^ (2 * D.BS.k0) ≤ D.L := by
      rw [hLeq]
      calc (2 : ℕ) ^ (2 * D.BS.k0) ≤ s := hSgeD s hs
        _ ≤ ∏ p ∈ blockSupport D.BS, p :=
            Nat.le_of_dvd hprodpos (Finset.dvd_prod_of_mem _ (hSblockD hs))
        _ ≤ b * ∏ p ∈ blockSupport D.BS, p := Nat.le_mul_of_pos_left _ hbpos
    calc 2 * N + 1 ≤ (2 : ℤ) ^ (2 * D.BS.k0) := by linarith [hN2]
      _ ≤ (D.L : ℤ) := by exact_mod_cast hLge
  exact ⟨hN2, hNL, hNreal⟩


/-- Produce the main-arc window certificate: choose `N = ⌈C/σ⌉`, prove the
`σ_E ↔ σ_ctrl` comparison and window bounds, and build the numeric fields. -/
lemma exists_r2_main_arc_window {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) :
    Nonempty (R2MainArcWindow F Cc M) := by
  classical
  have hbpos := F.hbpos
  set D : R2ConcreteData T b := M.D with hDeq
  set W : R2ConcreteData.Weights D := M.W with hWeq
  set QB : R2MassBatchSupply D := M.QB with hQBeq
  set C : ℝ := F.C with hCeq
  -- bridge the opaque mass-batch data back to the foundation/concrete witnesses
  have hBS : D.BS = F.BS := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_BS]
  have hS : D.S = Cc.S := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_S]
  have hR : D.R = b.primeFactors := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_R]
  have he0 : ∀ e ∈ D.E, 0 < e := M.he0
  have hLeq : D.L = b * ∏ p ∈ blockSupport D.BS, p := M.hLeq
  have hsumE : ∑ e ∈ D.E, (1 : ℝ) / (e : ℝ) ^ 2 ≤ 1000001 * (sigmaCtrl D.BS) ^ 2 := M.hsumE
  have hk05 : 5 ≤ D.BS.k0 := by rw [hBS]; exact F.hk05
  have hCge3 : (3 : ℝ) ≤ C := F.hCge3
  have hk0dom : 1000000 * (Nat.ceil C + 1) ^ 4 ≤ D.BS.k0 := by rw [hBS]; exact F.hk0dom
  have hadmD : admissibleGlobalRange D.BS := by rw [hBS]; exact F.hadm
  have hSgeD : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s := by rw [hS, hBS]; exact Cc.hSge
  have hRpos'D : ∀ r ∈ D.R, 2 ≤ r := by rw [hR]; exact Cc.hRpos'
  set σ : ℝ := sigmaCtrl D.BS with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact sigmaCtrl_pos D.BS hadmD
  have hσle1 : σ ≤ 1 := by rw [hσdef]; exact sigmaCtrl_le_one D.BS (by omega)
  set N : ℤ := ⌈C / σ⌉ with hNdef
  have hNlo : C / σ ≤ (N : ℝ) := Int.le_ceil _
  have hNhi : (N : ℝ) ≤ C / σ + 1 := le_of_lt (Int.ceil_lt_add_one _)
  have hNnonneg : 0 ≤ N := by
    have : (0 : ℝ) ≤ C / σ := by positivity
    have := le_trans this hNlo
    exact_mod_cast this
  -- σ_E two-sided control (named certificate: compare σ_E with σ_ctrl)
  obtain ⟨hsigmaE_lb, hsigmaE_ub, hsigmaEpos⟩ := r2_main_arc_sigmaE_compare F Cc M
  -- N bounds vs σ
  have hNsigma : (N : ℝ) * σ ≤ C + 1 := by
    have h1 : (N : ℝ) * σ ≤ (C / σ + 1) * σ := mul_le_mul_of_nonneg_right hNhi hσpos.le
    rw [add_mul, one_mul, div_mul_cancel₀ C (ne_of_gt hσpos)] at h1
    linarith [h1, hσle1]
  have h2N1sigma : (2 * (N : ℝ) + 1) * σ ≤ 2 * C + 3 := by
    have h1 : (2 * (N : ℝ) + 1) * σ ≤ (2 * (C / σ + 1) + 1) * σ := by
      apply mul_le_mul_of_nonneg_right _ hσpos.le; linarith [hNhi]
    have h2 : (2 * (C / σ + 1) + 1) * σ = 2 * C + 3 * σ := by
      have hσne : σ ≠ 0 := ne_of_gt hσpos; field_simp; ring
    rw [h2] at h1
    linarith [h1, hσle1]
  -- large-k0 window facts (named certificate: N-window scale/period ledger)
  obtain ⟨hN2, hNL, hNreal⟩ := r2_main_arc_window_scale_period F Cc M N hNhi
  have hNF : MainArcNumericFields D.E W.theta N :=
    r2_close_numericFields D W N σ C hσpos he0 QB hSgeD hRpos'D hsumE hsigmaE_lb
      hNnonneg hCge3 hNlo hNsigma hk0dom hNreal
  exact ⟨⟨N, hNnonneg, hNlo, hN2, hNL, hσpos, h2N1sigma, hsigmaE_ub, hsigmaEpos, hNF⟩⟩

/-! ## Minor-arc budget layer

The minor-arc budget factors through explicitly named certificate steps:

* **classification + lanes** — `r2_buildFreqLanes` builds the
  `R2MinorEndgameFrequencyLanes`, i.e. the block-lane fibre-tail estimate
  (`r2_blockFiberTail`, with the bounded `b`-to-1 multiplicity), the extra
  frequency count bound (`r2_extra_count_le`, `≤ b(2N+1)`), and the per-frequency
  gadget damping (`r2ExtraSiblingChoice_of_intLabelData`, the `G`-fold damping).
* **support budget** — `r2_minor_support_budget` feeds those lanes through the
  abstract minor-support supply principle `F.hSB` to produce the
  `R2MinorSupportBudgetData` (the block/extra cover with its two budget fields).
* **lane bound** — `r2_minor_lane_bound` combines the block and extra budgets via
  `hminorSum_of_block_extra_norm_bounds` into the per-`MainArcFields` minor sum
  bound `≤ r2MinorBudget`.
* **budget closure** — `r2_minor_budget_closure` proves the budget is dominated by
  the main-term floor at the actual `σ_E` (`r2_close_budget_501` +
  `hbeat_of_sigma_le_sigmaCtrl`).
-/

/-- **Minor-arc budget value.**  The block component
`(b·η + b·Ctail·e^{-C²·(16/9)/2})/σ_ctrl` plus the extra component
`b·(2N+1)·Dmp`. -/
def r2MinorBudget {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) {Cc : R2ConcreteCertificate F}
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M) : ℝ :=
  ((b : ℝ) * F.η + (b : ℝ) * (F.Ctail * Real.exp (-F.C ^ 2 * (16 / 9) / 2)))
      / sigmaCtrl M.D.BS
    + (b : ℝ) * (2 * (A.N : ℝ) + 1) * F.Dmp

/-- **Minor classification + support-budget certificate.**  Build the block,
extra-count, and gadget-damping frequency lanes (`r2_buildFreqLanes`) and feed
them through the abstract minor-support supply principle `F.hSB` to obtain the
`R2MinorSupportBudgetData`: the block/extra cover of the minor frequencies with
its block budget `(b·(η + Ctail·e^{…}))/σ_ctrl` and extra budget `b·(2N+1)·Dmp`. -/
lemma r2_minor_support_budget {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M) :
    Nonempty (R2MinorSupportBudgetData M.D M.W A.N
      ((b : ℝ) * (F.η + F.Ctail * Real.exp (-F.C ^ 2 * (16 / 9) / 2)) / sigmaCtrl M.D.BS)
      ((b : ℝ) * (2 * (A.N : ℝ) + 1) * F.Dmp)) := by
  classical
  have hbpos := F.hbpos
  set D : R2ConcreteData T b := M.D with hDeq
  set W : R2ConcreteData.Weights D := M.W with hWeq
  set N : ℤ := A.N with hNeq
  -- bridge the opaque mass-batch data back to the foundation/concrete witnesses
  have hBS : D.BS = F.BS := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_BS]
  have hS : D.S = Cc.S := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_S]
  have hR : D.R = b.primeFactors := by simp only [hDeq, M.hDdef, R2ConcreteData.withQ_R]
  have hcovRD : CoversPrimeDivisors D.R b := by rw [hR]; exact F.hcovR
  have hcopBD : BlockSupportCoprimeWith D.BS b := by rw [hBS]; exact F.hcopB
  have hRpD : ∀ r ∈ D.R, Nat.Prime r := by rw [hR]; exact F.hRp
  have hSprimeD : ∀ s ∈ D.S, Nat.Prime s := by rw [hS]; exact Cc.hSprime
  have hRdvdD : ∀ r ∈ D.R, r ∣ b := by rw [hR]; exact F.hRdvd
  have hSblockD : D.S ⊆ blockSupport D.BS := by rw [hS, hBS]; exact Cc.hSblock
  have hlt'D : ∀ r ∈ D.R, ∀ s ∈ D.S, r < s := by rw [hR, hS]; exact Cc.hlt'
  have hSgeD : ∀ s ∈ D.S, 2 ^ (2 * D.BS.k0) ≤ s := by rw [hS, hBS]; exact Cc.hSge
  have hScardD : D.S.card = F.G := by rw [hS]; exact Cc.hScard
  have hk0minMD : F.k0minM ≤ D.BS.k0 := by rw [hBS]; exact F.hk0minM
  have hadmD : admissibleGlobalRange D.BS := by rw [hBS]; exact F.hadm
  have hCge1 : (1 : ℝ) ≤ F.C := F.hCge1
  -- classification + block/extra/gadget lanes
  obtain ⟨Ln⟩ := r2_buildFreqLanes D W N F.C F.η F.Ctail F.Dmp F.G hbpos F.hbsf
    hcovRD hcopBD hRpD hSprimeD hRdvdD hSblockD hlt'D M.hctrlAvoid M.hgadgetAvoid
    M.heL M.he0 M.hL M.hLeq hCge1 A.hNnonneg hSgeD hScardD A.hNlo A.hN2
    (le_of_lt F.hDmppos) (F.hbbdef ▸ F.hG)
  -- abstract minor-support supply principle applied to the lanes
  exact F.hSB D W N
    ((b : ℝ) * (F.η + F.Ctail * Real.exp (-F.C ^ 2 * (16 / 9) / 2)) / sigmaCtrl D.BS)
    ((b : ℝ) * (2 * (N : ℝ) + 1) * F.Dmp) (N : ℝ)
    (mainArcClassificationData D W N F.C) hk0minMD hadmD Ln.toMultiGadget

/-- **Minor lane bound.**  Combine the block and extra budgets of the
`R2MinorSupportBudgetData` (via `hminorSum_of_block_extra_norm_bounds`) into the
per-`MainArcFields` minor-sum bound `∑_{h∈Sm} ‖fourierTerm h‖ ≤ r2MinorBudget`. -/
lemma r2_minor_lane_bound {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M) :
    ∀ MA : MainArcFields M.D.E M.W.theta b M.D.L A.N,
      (∑ h ∈ MA.Sm, ‖fourierTerm M.D.E M.W.theta b M.D.L h‖) ≤ r2MinorBudget F M A := by
  obtain ⟨MB⟩ := r2_minor_support_budget F Cc M A
  intro MA
  refine hminorSum_of_block_extra_norm_bounds M.D.E M.W.theta b M.D.L MA.Sm
    ⟨MB.Sblock MA, MB.Sextra MA, MB.hcover MA⟩ _ _ (r2MinorBudget F M A)
    (MB.hblock MA) (MB.hextra MA) (le_of_eq ?_)
  unfold r2MinorBudget
  ring

/-- **Minor budget closure.**  The minor-arc budget is strictly dominated by the
main-term floor `0.8·e^{-π²/2}/2 / σ_E` at the actual edge variance `σ_E`.  Uses
the numeric collapse `r2_close_budget_501` (budget `< c3/(501·σ_ctrl)`) and the
variance comparison `hbeat_of_sigma_le_sigmaCtrl` (`σ_E ≤ 501·σ_ctrl`). -/
lemma r2_minor_budget_closure {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M) :
    r2MinorBudget F M A < 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) /
      Real.sqrt (sigmaE2 M.D.E M.W.theta) := by
  have hbpos := F.hbpos
  have hσpos : 0 < sigmaCtrl M.D.BS := A.hsigmapos
  have hb1 : (b : ℝ) * F.η = F.c3 / 2004 := by rw [F.hηdef]; field_simp
  have hb2 : (b : ℝ) * (F.Ctail * Real.exp (-F.C ^ 2 * (16 / 9) / 2)) < F.c3 / 2004 :=
    F.hCbound
  have hb3 : (b : ℝ) * (2 * (A.N : ℝ) + 1) * F.Dmp * sigmaCtrl M.D.BS ≤ F.c3 / 2004 := by
    have hstep : (b : ℝ) * (2 * (A.N : ℝ) + 1) * F.Dmp * sigmaCtrl M.D.BS
        = (b : ℝ) * F.Dmp * ((2 * (A.N : ℝ) + 1) * sigmaCtrl M.D.BS) := by ring
    rw [hstep]
    have hle : (b : ℝ) * F.Dmp * ((2 * (A.N : ℝ) + 1) * sigmaCtrl M.D.BS)
        ≤ (b : ℝ) * F.Dmp * (2 * F.C + 3) :=
      mul_le_mul_of_nonneg_left A.h2N1sigma (mul_nonneg (by positivity) F.hDmppos.le)
    refine le_trans hle (le_of_eq ?_)
    have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have hCne : (2 * F.C + 3 : ℝ) ≠ 0 :=
      ne_of_gt (show (0 : ℝ) < 2 * F.C + 3 by have := F.hCge3; linarith)
    rw [F.hDmpdef]; field_simp
  have hBm501 : r2MinorBudget F M A < F.c3 / (501 * sigmaCtrl M.D.BS) := by
    have h := r2_close_budget_501 (sigmaCtrl M.D.BS) ((b : ℝ) * F.η)
      ((b : ℝ) * (F.Ctail * Real.exp (-F.C ^ 2 * (16 / 9) / 2)))
      ((b : ℝ) * (2 * (A.N : ℝ) + 1) * F.Dmp) F.c3 hσpos F.hc3pos hb1 hb2 hb3
    unfold r2MinorBudget
    exact h
  have hc3eq : F.c3 = 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) := by
    rw [F.hc3eq, r2MinorMainCtrlConstant]
  rw [← hc3eq]
  exact hbeat_of_sigma_le_sigmaCtrl F.c3 (Real.sqrt (sigmaE2 M.D.E M.W.theta))
    (501 * sigmaCtrl M.D.BS) (r2MinorBudget F M A)
    F.hc3pos A.hsigmaEpos (by positivity) A.hsigmaE_ub hBm501

/-- **Minor certificate.**  The minor-arc budget `Bm`, the per-`MainArcFields`
minor-sum bound (assembled from the block lane and the gadget/extra lane via the
frequency-lane construction and the minor-support budget supply), and the
domination `hbeat` of `Bm` by the main-term floor at the actual `σ_E`. -/
structure R2MinorCertificate {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M) where
  /-- the minor-arc budget. -/
  Bm : ℝ
  hminor : ∀ MA : MainArcFields M.D.E M.W.theta b M.D.L A.N,
      (∑ h ∈ MA.Sm, ‖fourierTerm M.D.E M.W.theta b M.D.L h‖) ≤ Bm
  hbeat : Bm < 0.8 * (Real.exp (-(Real.pi ^ 2 / 2)) / 2) /
      Real.sqrt (sigmaE2 M.D.E M.W.theta)

/-- Produce the minor-arc certificate: take the minor budget `r2MinorBudget`, its
per-`MainArcFields` lane bound (`r2_minor_lane_bound`), and the budget-closure
domination (`r2_minor_budget_closure`).  This layer only assembles the named
component certificates. -/
lemma exists_r2_minor_certificate {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M) :
    Nonempty (R2MinorCertificate F Cc M A) :=
  ⟨⟨r2MinorBudget F M A, r2_minor_lane_bound F Cc M A, r2_minor_budget_closure F Cc M A⟩⟩



/-! ## Final assembly -/

/-- **Final assembly.**  Consume the five certificates and fill the
`ArcConstruction` socket through the upstream `R2FinalSupply` endpoint.  This
layer chooses no parameters and chases no constants — it only threads the
already-built certificate data into `exists_arcConstruction_of_mainArcParams`. -/
lemma assemble_arcConstruction {T : Finset ℕ} {b : ℕ}
    (F : R2FoundationCertificate T b) (Cc : R2ConcreteCertificate F)
    (M : R2MassCertificate F Cc) (A : R2MainArcWindow F Cc M)
    (R : R2MinorCertificate F Cc M A) :
    Nonempty (ArcConstruction T b) :=
  exists_arcConstruction_of_mainArcParams F.hb3 M.D M.W A.N R.Bm A.hNnonneg A.hNL
    M.hsemi M.havoid M.hne M.heL M.he0 M.hloadUpper A.hNF.hN A.hNF.htw A.hNF.hsmall
    R.hminor R.hbeat

/-- **Terminal R2 existence theorem (factored).**  The arc construction exists
for squarefree `b ≥ 3`, assembled through the explicit certificate chain
`foundation → concrete → mass → main-arc → minor → final`. -/
theorem exists_arcConstruction_final (T : Finset ℕ) (b : ℕ)
    (hb : 3 ≤ b) (hbsf : Squarefree b) :
    Nonempty (ArcConstruction T b) := by
  obtain ⟨F⟩ := exists_r2_foundation_certificate T b hb hbsf
  obtain ⟨Cc⟩ := exists_r2_concrete_certificate F
  obtain ⟨M⟩ := exists_r2_mass_certificate F Cc
  obtain ⟨A⟩ := exists_r2_main_arc_window F Cc M
  obtain ⟨Rm⟩ := exists_r2_minor_certificate F Cc M A
  exact assemble_arcConstruction F Cc M A Rm

end CircleMethod

end
