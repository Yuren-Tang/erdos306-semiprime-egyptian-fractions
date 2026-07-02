import RequestProject.Public.Erdos306

/-!
# Verification audit entry point

`lake env lean RequestProject/Audit.lean` prints everything an external reviewer
needs in order to verify the result, without reading the proof:

* the full statement of `erdos_306` (compare against Erdős Problem 306 / the
  `google-deepmind/formal-conjectures` formulation);
* its axiom dependencies (must be sorry-free, with no axiom beyond the three
  standard Lean ones and the two structural analytic inputs);
* the statements of those two analytic axioms: a PNT-type dyadic prime-density
  input and a Mertens-type reciprocal-prime window-mass input.

CI runs this file and gates on the axiom audit.
-/

open Erdos306 GlobalControl

-- The theorem that is proved:
#check @erdos_306

-- Sorry-free, and depends only on the axioms listed here:
#print axioms erdos_306

-- The two non-standard axioms (structural analytic-number-theory inputs):
#print pnt_dyadic_prime_density
#print mertens_dyadic_window_mass
