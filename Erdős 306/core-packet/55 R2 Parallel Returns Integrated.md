# R2 Parallel Returns Integrated

Back to [[54 R2 Final Assembly Ledger]].

## Integrated Returns

Two parallel lanes returned and have been integrated.

### Aristotle lane

Added:

```lean
RequestProject/R2MinorEstimateInterface.lean
```

Main endpoints:

```lean
CircleMethod.block_part_bound
CircleMethod.extra_part_bound
CircleMethod.r2_hminor_bound_from_block_and_extra
```

Meaning:

- `block_part_bound` specializes `minor_energy_sum_le_fiber_tail` to
  `blockMinorPart`;
- `extra_part_bound` sums the one-gadget damping bound from
  `gadget_charFun_damp`;
- `r2_hminor_bound_from_block_and_extra` is the generic finite glue through
  `r2_minor_bound_split`.

### Codex lane

Added:

```lean
RequestProject/R2ConcreteData.lean
```

and stabilized the strict residual selector in:

```lean
RequestProject/BlockMassPool.lean
```

Main endpoints:

```lean
CircleMethod.r2Concrete_semiprime
CircleMethod.r2Concrete_avoid
CircleMethod.r2Concrete_dvd_period
CircleMethod.r2Concrete_edges_pos
CircleMethod.r2Concrete_nonempty
CircleMethod.r2Concrete_sigma_le_sigmaCtrl_of_light
CircleMethod.r2Concrete_exists_residual_subset_recip_window
CircleMethod.r2Concrete_total_recipLoad_window_of_residual
```

The concrete data namespace also provides:

```lean
CircleMethod.R2ConcreteData
CircleMethod.R2ConcreteData.E
CircleMethod.R2ConcreteData.L
CircleMethod.R2ConcreteData.recipLoad
CircleMethod.R2ConcreteData.baseLoad
CircleMethod.R2ConcreteData.Weights
```

## Build

Verified in the warm build project:

```bash
lake build RequestProject.R2ConcreteData RequestProject.R2MinorEstimateInterface
lake build RequestProject.R2AssemblyFields
```

Both completed successfully.

I did not rerun axiom traces locally for every endpoint because both returning
agents reported standard traces and the immediate integration question was build
compatibility.  From here, axiom traces should be reserved for final/critical
endpoints or suspicious changes, not every green leaf.

## Clean-Up

The root-level Aristotle return folders were moved into:

```text
Erdős 306/archive/Aristotle/2026-06-15-integrated/
```

The live `aristotle-delivery/` bundle was regenerated with:

```bash
./REGENERATE.sh --with-oleans
```

so future Aristotle uploads use the integrated source and prebuilt artifacts.

## Current Remaining Assembly Fields

The integrated wrappers close or expose the easy structural layer:

```lean
hsemi
havoid
hne
hL
hbL
heL
he0
hlb / hub / hmass    -- abstracted by R2ConcreteData.Weights
hminor              -- reduced to block/extra hypotheses
sigma comparison    -- via r2Concrete_sigma_le_sigmaCtrl_of_light
```

Still not closed:

```lean
theta
N
SM
Sm
lbl
Bm
hbound
hpart
hdisj
hN
htw
hsmall
hmaps
hinj
hsurj
hterm
hbeat
```

But several of these are now standard assembly rather than new estimates:

- `hpart`, `hdisj`, `hmaps`, `hinj`, `hsurj`, `hterm` should come from
  `exists_mainArc_bijection` and `fourierTerm_eq_term_label_of_modL`;
- `hbound` now has the helper
  `period_div_sum_lt_of_recip_sum_lt` / `r2Concrete_hbound_of_recipLoad_lt_one`;
- `hbeat` now has the helper `hbeat_of_sigma_le_sigmaCtrl` /
  `hbeat_of_block_extra_sigmaCtrl`; it remains to feed the concrete
  `sigmaE ≤ sigmaCtrl` comparison and strict budget;
- `hN`, `htw`, `hsmall` are large-scale inequalities after choosing `N`.

## Local Assembly Leaf

```lean
RequestProject/R2AssemblyFields.lean
```

has been added with generic lemmas for:

1. `period_div_sum_lt_of_recip_sum_lt` giving `hbound`;
2. `r2Concrete_hbound_of_recipLoad_lt_one` in the concrete-data language;
3. `hbeat_of_sigma_le_sigmaCtrl`;
4. `hbeat_of_block_extra_sigmaCtrl`.

The next local target is the main-arc record-field package, consuming
`exists_mainArc_bijection` and `fourierTerm_eq_term_label_of_modL`.
