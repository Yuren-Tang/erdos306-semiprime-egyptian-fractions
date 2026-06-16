# Aristotle task: R2 multi-gadget reservoir selection

Work in this Lean project.  The main target file is:

```lean
RequestProject/R2ExtraReservoirSelection.lean
```

Build only:

```bash
lake build RequestProject.R2ExtraReservoirSelection
```

## Context

The current mainline already has:

- `R2ExtraCRTSibling.lean`
  - `CoversPrimeDivisors`
  - `BlockSupportCoprimeWith`
  - `exists_R_mismatch_of_block_eq_not_global`
  - `extra_sibling_card_le_pred_b`
- `R2ExtraMultiGadgetReservoir.lean`
  - `R2MultiGadgetReservoir`
  - `multiGadgetBoundData_of_reservoir`
- `R2MinorEndgameMultiGadget.lean`
  - consumes `R2MultiGadgetReservoir` and produces the final minor-ready data.

The remaining terminal extra-minor object is now a finite reservoir-selection
problem.  It is not a new analytic-number-theory gap.

## Mandatory deliverable

Complete `RequestProject/R2ExtraReservoirSelection.lean` with no `sorry`,
`admit`, or new axioms.

The file asks you to prove an important bridge:

> Given prepared per-frequency data `rfun`, `mfun`, `Gset` satisfying the CRT
> sibling congruences, small-label bounds, and a finite damping budget, construct
> the concrete `R2MultiGadgetReservoir`.

This is the precise interface the mainline needs.

### Mathematical proof sketch

For each extra frequency \(h\):

1. `rfun h ∈ D.R` is supplied.
2. `Gset h ⊆ D.S` is supplied.
3. Therefore every edge \(rfun(h)\cdot s\), \(s\in Gset(h)\), lies in `D.E`,
   because `D.gadgetEdges_subset_E` contains all products `r ∈ D.R`, `s ∈ D.S`.
4. Since `W.hlb` and `W.hub` hold on every edge of `D.E`, the theta bounds
   on all selected gadget edges follow.
5. The congruence fields `hm_s`, `hm_r`, `hm_small` are exactly the hypotheses.
6. The finite budget field is exactly the supplied `hbudget`.

### Useful definitions/theorems already available

- `multiGadgetEdges r G = G.image (fun s => r * s)`
- `mem_gadgetEdges`
- `D.gadgetEdges_subset_E`
- `W.hlb`, `W.hub`

Expected proof of `hGmem`:

```lean
intro e he
rw [multiGadgetEdges, Finset.mem_image] at he
obtain ⟨s, hsG, rfl⟩ := he
exact D.gadgetEdges_subset_E
  (mem_gadgetEdges.mpr ⟨X.rfun h, X.hRmem h hh, s, X.hSmem h hh hsG, rfl⟩)
```

Theta bounds then use that edge-membership proof.

## Optional stretch deliverable

If the mandatory file is completed quickly, add another file:

```lean
RequestProject/R2ExtraReservoirUniformBudget.lean
```

Prove a uniform-budget constructor: if every extra frequency has a gadget set
whose damped power is at most `C`, and `(extraPart.card : ℝ) * C ≤ Bextra`,
then the total `hbudget` required by `R2ExtraPreparedChoice` follows.

Suggested theorem:

```lean
theorem preparedChoice_of_pointwise_budget ...
```

Do not edit `R2FinalAssembly*`.

