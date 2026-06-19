# Aristotle task: R2 extra-frequency choice

Please complete `RequestProject/R2ExtraFrequencyChoice.lean`.

## Goal

Prove the finite CRT-selection bridge from per-frequency block-label data to the
already-built multi-gadget reservoir interface.

The file has three real holes:

1. `exists_r_sibling_of_extraFrequencyLabelData`
2. `r2ExtraSiblingChoice_of_labelData`
3. `preparedChoice_of_extraFrequencyLabelData`

The last theorem `r2MultiGadgetReservoir_of_extraFrequencyLabelData` should then
close automatically.

## Mathematical content

For each frequency
`h ∈ extraMinorPart MA.Sm Sblock Sextra`, the label `X.mfun h` agrees with `h`
on every prime in `blockSupport D.BS`, but not modulo the full R2 period
`D.L = b * ∏ s ∈ blockSupport D.BS, s`.

Use the existing theorem

```lean
exists_R_mismatch_of_block_eq_not_global
```

from `R2ExtraCRTSibling.lean`, with:

```lean
BS := D.BS
R := D.R
L := D.L
m := X.mfun h
```

The period equality should be by unfolding `R2ConcreteData.L` and
`primeSupportPeriod` (often `rfl` or `simpa [R2ConcreteData.L, primeSupportPeriod]`).

The result gives `∃ r ∈ D.R` such that `h` and `X.mfun h` differ modulo `r`.

Then use classical choice over the finite extra part:

```lean
let P h r := r ∈ D.R ∧ Nat.Prime r ∧ r ∣ b ∧
  (h : ZMod r) ≠ (X.mfun h : ZMod r)
let rfun h := if hh : h ∈ extraMinorPart MA.Sm Sblock Sextra
  then Classical.choose (hex h hh)
  else 0
```

For `preparedChoice_of_extraFrequencyLabelData`, call
`preparedChoice_of_pointwise_budget`.  Use:

- `rfun := chosen.rfun`
- `Gset := Gset`
- `mfun := fun h => (X.mfun h : ℤ)`
- `hRmem := chosen.hRmem`
- `hm_r := chosen.hm_r`, after simplifying the integer/natural casts if needed
- `hm_s`: if `s ∈ Gset h`, then `s ∈ D.S`, then `s ∈ blockSupport D.BS`,
  so apply `X.hblock h hh s ...`
- `hm_small`: exactly the hypothesis
- `hcard`, `hpt`: exactly the hypotheses

## Constraints

- Do not add axioms.
- Do not modify unrelated files.
- No new mathematical assumptions.
- Build target:

```text
lake build RequestProject.R2ExtraFrequencyChoice
```

Please report whether there are any remaining `sorry`, `admit`, or `axiom`.
