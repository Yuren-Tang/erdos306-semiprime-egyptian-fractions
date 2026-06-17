import RequestProject.R2MassBatchBaseLoadBudget

/-!
# R2 endgame status

This marker module documents the current formal R2 endgame socket.

Verified upstream leaves now reduce the residual mass-batch branch to:

* a split base-load budget `R2BaseLoadBudget D`;
* denominator gadget primes outside `blockSupport D.BS`;
* `blockPrimes D.BS.k0 ⊆ blockSupport D.BS`;
* the remaining component supply, minor-support budget, and final scale choices.

The only named analytic input introduced at this layer is
`CircleMethod.dyadic_control_recipLoad_eventually_small`.
-/

