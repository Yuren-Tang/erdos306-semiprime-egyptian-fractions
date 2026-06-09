# Lean Formalization Map

Back to [[00 README]].

Current Lean working package:

$$
\texttt{lean/}
$$

It is a curated subset of the latest archived Aristotle package
`../Aristotle/output-final_aristotle_7/`. Future Lean work should use this
clean workbench unless a specific archived dependency must be reintroduced.

## Boundary file

`RequestProject/FourierPositivity.lean`

- isolates `fourier_positivity_unconditional`;
- contains exactly the current final `sorry`;
- documents why naive decompositions fail;
- should be read as a boundary statement, not as a proof.

`RequestProject/Erdos306Unconditional.lean`

- states the unconditional theorem;
- proves concrete examples and supporting identities;
- depends on `fourier_positivity_unconditional`.

## Algebraic infrastructure now closed

`RequestProject/PrimitiveProjectiveNormalization.lean`

- fixed-$p$ projective proportionality plus Bezout primitivity gives equality
  up to sign.

`RequestProject/ResidualPrimeShellCRT.lean`

- anchored hits produce six-variable CRT interval hits;
- divisibility data reconstructs the anchored lattice with the anchor equation;
- zero denominators are excluded in the short coprime range;
- fixed-height residual shell predicates are packaged.

`RequestProject/SplitStarCorrelation.lean`

- six-variable divisibility is equivalent to a split anchored star;
- diagonal split stars recover anchored hits;
- split stars imply three factorable ternary relations;
- defines $A_{04}$, $B_{123}$, and `SplitCorrelation`;
- proves the exact double-counting identity;
- proves the anchor-side collision determinant.

## Earlier useful files

- `AnchoredDeterminantRank.lean`: fixed-$p$ determinant obstruction.
- `AnchoredCRTLattice.lean`: anchored CRT lattice.
- `ValidCRTLattice.lean`: unanchored CRT lattice and primitive rays.
- `ReciprocalCRTProduct.lean`: local CRT residues.
- `AnchoredSelectionPipeline.lean`: finite cluster-selection trichotomy.
- `AdaptiveClusterSelection.lean`, `ClusterCoverBookkeeping.lean`,
  `TwoCoreBookkeeping.lean`: finite cover/bookkeeping.
- `BernoulliFourier.lean`, `LatticeSpan.lean`, `CrossLabelEnergy.lean`:
  partial Fourier/lattice/energy infrastructure.

Bucket/FIE formalization files from the archived Aristotle packages are not in
the core Lean workbench. They should be restored only if the active
rational-collision theorem needs them.

## Lean status

The useful Lean fact is not "Erdős 306 is proved". It is:

$$
\text{all finite/algebraic interfaces around the current shell are no-sorry}.
$$

The remaining theorem is mathematical and analytic/inverse-combinatorial.

Local note: Codex could not rebuild this package here because the shell did not
have a `lake` command available.
