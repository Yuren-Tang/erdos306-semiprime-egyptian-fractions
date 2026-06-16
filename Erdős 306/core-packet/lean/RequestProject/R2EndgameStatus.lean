import RequestProject.R2MinorChoiceArc

/-!
# R2 endgame status

This marker module documents the current formal R2 endgame socket.

Current strongest verified endpoint:

* `exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_choiceMinor`

It says: after choosing a residual mass batch `Q`, a numeric scale `N`, a
component/core supply, and concrete minor lanes, the resulting edge set gives
`ArcConstruction T b`.

The remaining mathematical construction is therefore **not** the Fourier
orthogonality or the final positivity assembly.  It is the terminal R2 supply:

* choose/classify each minor frequency into block or extra support;
* prove the block lane `R2BlockFiberTailData` for the block part;
* for the extra part, choose `r_h ∈ R`, `s_h ∈ S`, and `m_h` satisfying the
  sibling congruence and damping budget, i.e. `R2ExtraMinorGadgetChoiceData`;
* provide the component, mass-batch, scale, and numeric inequalities at one
  sufficiently large dyadic bottom scale.

The only named analytic input introduced at this layer is
`CircleMethod.dyadic_control_recipLoad_eventually_small`; no new literature
input is currently forced by the formal endpoint itself.
-/
