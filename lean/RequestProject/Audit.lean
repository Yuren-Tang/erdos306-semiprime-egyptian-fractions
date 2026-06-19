import RequestProject.Erdos306FormalConjectures

/-!
# Verification audit entry point

`lake env lean RequestProject/Audit.lean` prints everything an external reviewer
needs in order to verify the result, without reading the proof:

* the full statement of `erdos_306` (compare against Erdős Problem 306 / the
  `google-deepmind/formal-conjectures` formulation);
* its axiom dependencies (must be sorry-free, with no axiom beyond the three
  standard Lean ones and the two Rosser–Schoenfeld inputs);
* the verbatim statements of those two axioms (compare against Rosser–Schoenfeld,
  Illinois J. Math. 6(1) (1962), 64–94, Cor. 3 eq. (3.8) p. 69 and Thm. 5
  eqs. (3.17)–(3.18) p. 70).

CI runs this file and gates on the axiom audit.
-/

open Erdos306 RosserSchoenfeld

-- The theorem that is proved:
#check @erdos_306

-- Sorry-free, and depends only on the axioms listed here:
#print axioms erdos_306

-- The two non-standard axioms, verbatim (check against Rosser–Schoenfeld 1962):
#print rosser_schoenfeld_cor3
#print rosser_schoenfeld_thm5
