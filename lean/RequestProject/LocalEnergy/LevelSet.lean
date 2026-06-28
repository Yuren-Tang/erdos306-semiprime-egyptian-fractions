import RequestProject.SBEEAssembly

/-! Uniform single-block level-set and partition-function bounds. -/

namespace LocalEnergy

/-- Uniform cardinality bound for a block-energy sublevel set. -/
alias block_level_set_bound := SBEEAssembly.unified_levelset

/-- A level-set estimate implies the corresponding exponential partition-
function estimate. -/
alias partition_function_bound_of_level_sets :=
  SBEEAssembly.partfun_series_bound

end LocalEnergy
