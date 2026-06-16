# R2 Extra-Energy Minor Arc Interface Task

Back to [[46 R2 Construction Design - Multiplicity Is Not Enough]] and
[[48 R2 Extra Support Bookkeeping Completed]].

This is the next bounded Lean task.  It is not the full construction theorem
`CircleMethod.exists_arcConstruction`; do not try to prove that directly.

## Purpose

The existing theorem

```lean
CircleMethod.minor_arc_bound_mult
```

bounds the minor arc using a raw fiber multiplicity `M`.  Note 46 explains why
this is too crude when mass/gadget edges introduce primes outside
`blockSupport BS`.

The next interface should retain extra-edge energy inside each fiber:

```text
QE E h >= Qctrl BS (a h) + Qextra h
```

and use a fiber tail bound

```text
sum_{h in fiber(a)} exp(-c * Qextra h) <= K
```

instead of a cardinality bound.

## Target File

Create a new file:

```text
RequestProject/ExtraEnergyMinorArc.lean
```

with:

```lean
import RequestProject.ArcConstructionExtra
```

Keep the file sorry-free.

## Target 1: Abstract Fiber-Tail Energy Lemma

Prove an analogue of `minor_energy_sum_le_mult`:

```lean
lemma minor_energy_sum_le_fiber_tail
    (BS : BlockSystem) (E : Finset ℕ) (c C K : ℝ) (Sm : Finset ℕ)
    (Qextra : ℕ → ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hQE : ∀ h ∈ Sm,
      Qctrl BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE E h)
    (hnotmain : ∀ h ∈ Sm,
      (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C)
    (hfiber : ∀ a : GlobalAssignment BS,
      ∑ h ∈ Sm.filter
        (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) = a),
        Real.exp (-c * Qextra h) ≤ K) :
    ∑ h ∈ Sm, Real.exp (-c * QE E h) ≤
      K * ∑' a : {a : GlobalAssignment BS // a ∉ mainArc BS C},
        Real.exp (-c * Qctrl BS a.1)
```

Proof plan:

1. Set

   ```lean
   af : ℕ → GlobalAssignment BS :=
     fun h => (fun p => ((h : ZMod p.1)))
   ```

2. Use `hQE` and `hc` to show

   ```lean
   Real.exp (-c * QE E h)
     ≤ Real.exp (-c * (Qctrl BS (af h) + Qextra h))
   ```

3. Rewrite the right side as

   ```lean
   Real.exp (-c * Qctrl BS (af h)) * Real.exp (-c * Qextra h)
   ```

   using `Real.exp_add` and ring normalization of the exponent.

4. Fiber the sum over `Sm.image af`.  Existing code in
   `ArcConstruction.lean` around `minor_energy_sum_le_mult` uses

   ```lean
   Finset.sum_fiberwise_of_maps_to'
   ```

   and can be copied/adapted.  If the dependency is awkward, a direct
   `calc` using the same API is fine.

5. For each fiber, factor out the constant

   ```lean
   Real.exp (-c * Qctrl BS a)
   ```

   and apply `hfiber a`.

6. Enlarge the sum from `Sm.image af` to

   ```lean
   Finset.univ.filter (fun a => a ∉ mainArc BS C)
   ```

   using `hnotmain`, exactly as in `minor_energy_sum_le_mult`.

## Target 2: Fourier Minor-Arc Bound With Fiber Tail

If Target 1 is done, prove the direct Fourier wrapper:

```lean
theorem minor_arc_bound_fiber_tail (eps : ℝ) (heps : 0 < eps) :
    ∀ η : ℝ, 0 < η →
    ∃ (k0min : ℕ) (Ctail : ℝ), 0 < Ctail ∧
      ∀ (BS : BlockSystem), k0min ≤ BS.k0 → admissibleGlobalRange BS →
      ∀ (C : ℝ), 1 ≤ C →
      ∀ (E : Finset ℕ) (theta : ℕ → ℝ) (b L : ℕ)
        (Sm : Finset ℕ) (K : ℝ) (Qextra : ℕ → ℝ),
      0 ≤ K →
      (∀ e ∈ E, (1 / 3 : ℝ) ≤ theta e) → (∀ e ∈ E, theta e ≤ 2 / 3) →
      (∀ e ∈ E, e ∣ L) → (∀ e ∈ E, 0 < e) → 0 < L →
      (∀ h ∈ Sm,
        Qctrl BS (fun p => ((h : ZMod p.1))) + Qextra h ≤ QE E h) →
      (∀ h ∈ Sm,
        (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) ∉ mainArc BS C) →
      (∀ a : GlobalAssignment BS,
        ∑ h ∈ Sm.filter
          (fun h => (fun p => ((h : ZMod p.1)) : GlobalAssignment BS) = a),
          Real.exp (-(16 / 9 : ℝ) * Qextra h) ≤ K) →
      ‖∑ h ∈ Sm,
          (∏ e ∈ E, ((theta e : ℂ) *
              Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((L / e : ℕ) : ℂ) / (L : ℂ))
              + (1 - theta e)))
          * Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * ((L / b : ℕ) : ℂ) / (L : ℂ)))‖
        ≤ K * (η + Ctail * Real.exp (-C ^ 2 * (16 / 9) / 2)) / sigmaCtrl BS
```

This should follow exactly like `minor_arc_bound_mult`, replacing
`minor_energy_sum_le_mult` with Target 1.

## Deliverable

Return:

1. files changed;
2. theorem names proved;
3. `lake build RequestProject.ExtraEnergyMinorArc` result;
4. `#print axioms` for the two new theorems.

If Target 2 is too slow, still return Target 1 green; it is already useful.
