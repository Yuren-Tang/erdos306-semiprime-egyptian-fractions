import RequestProject.SBEEForcing

/-! Dominant-label uniqueness, nondominant energy forcing, and cold-block
label/exception bounds for a single prime block. -/

namespace LocalEnergy

open scoped Classical

/-- A block assignment has a label carried by at least a `(1 - rho)` proportion
of its primes, with the label in the canonical range. -/
abbrev HasDominantLabel := SBEEForcing.IsDominant

/-- Two labels carried by the same sufficiently dense prime block coincide. -/
alias dominant_label_unique := SBEEForcing.dominant_label_unique

/-- A nondominant assignment has energy at least a constant multiple of
`X / (log X)^3`. -/
alias nondominant_energy_lower_bound :=
  SBEEForcing.theorem_B_nondominant_forcing

/-- The deviation scale of a dense dyadic prime block has the expected lower
bound. -/
alias block_deviation_lower_bound := SBEEForcing.sigmaP_lower

/-- Energy controls the size of the label carried by a dominant assignment. -/
alias dominant_label_bound := SBEEForcing.theoremA_label_range

/-- Energy controls the number of primes outside a dominant label class. -/
alias dominant_exception_count_bound := SBEEForcing.exception_count_bound

/-- At fixed dominant label, a block energy sublevel set has exponential size. -/
alias fixed_label_level_set_bound := SBEEForcing.fixed_label_count

/-- A dominant assignment below the nondominant energy scale has uniformly
boundedly many exceptional primes. -/
alias cold_exception_count_bound := SBEEForcing.cold_exception_bound

/-- A dominant label below the nondominant energy scale is small relative to
the block size. -/
alias cold_label_bound := SBEEForcing.cold_label_size

end LocalEnergy
