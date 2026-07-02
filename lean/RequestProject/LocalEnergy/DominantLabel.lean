import RequestProject.LocalEnergy.CrossLabelEnergy
import RequestProject.LocalEnergy.DominantLabel.Basic
import RequestProject.LocalEnergy.DominantLabel.Counting
import RequestProject.LocalEnergy.DominantLabel.Forcing
import RequestProject.LocalEnergy.DominantLabel.ColdBounds

/-!
# Dominant labels for local CRT energy

An assignment has a dominant label when one integer residue is carried by a
fixed positive proportion of its prime coordinates. This file develops the
single-block theory around that notion:

* CRT representatives inside one label class recover the integer label;
* cross-label dispersion forces quadratic energy;
* low-energy dominant assignments admit a small encoding;
* nondominant assignments have energy of order `X / (log X)^3`;
* below that scale, dominant labels and their exceptional coordinates obey
  uniform bounds.

The public conclusions are `dominant_level_set_bound`,
`nondominant_energy_lower_bound`, `fixed_label_level_set_bound`,
`cold_exception_count_bound`, and `cold_label_bound`.
-/
