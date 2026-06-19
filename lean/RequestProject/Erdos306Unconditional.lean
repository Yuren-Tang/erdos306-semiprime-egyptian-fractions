/-
# Erdős Problem 306 — shared infrastructure shim

The concrete per-base instances and the original (pre-R2) circle-method chain
that once lived here have been superseded by the block-aligned R2 construction.
The unconditional, fully verified result is `erdos_306_unconditional` in
`Erdos306Final`, and the community-formulation statement is `erdos_306` in
`Erdos306FormalConjectures`.

This file is kept as an import shim re-exporting the shared reduction
infrastructure (`reduction_to_unit_numerator_avoiding` from `MainTheorem`, etc.)
used by the final assembly.
-/
import Mathlib
import RequestProject.Defs
import RequestProject.MainTheorem
import RequestProject.SemiprimeInfinity
import RequestProject.FourierPositivity

open scoped BigOperators Classical

noncomputable section

end
