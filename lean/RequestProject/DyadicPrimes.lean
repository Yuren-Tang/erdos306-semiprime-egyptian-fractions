import RequestProject.AnalyticInputs

/-!
# Dyadic prime blocks and structural analytic inputs

This module is the construction-facing import for dyadic prime-supply facts.
It re-exports the block definition together with the stable downstream analytic
interfaces:

* `GlobalControl.dyadic_prime_density`
* `GlobalControl.dyadic_mertens_cumulative`

The actual non-standard assumptions are declared in `RequestProject.AnalyticInputs`
as `GlobalControl.pnt_dyadic_prime_density` and
`GlobalControl.mertens_dyadic_window_mass`; downstream construction files should
use the theorem wrappers above rather than importing a historical
Rosser--Schoenfeld compatibility layer.
-/
