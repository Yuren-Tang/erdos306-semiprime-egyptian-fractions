# Aristotle prompt: ambient FIE finite bookkeeping

Copy the following to Aristotle when useful.

```text
Continue the existing Lean 4 project.

Create a new file:

RequestProject/PotentialTree.lean

Import Mathlib.

Do not attempt SBEE, Fourier analysis, Kloosterman estimates, prime number theory, or asymptotics.
No sorry.
No `True := trivial` placeholders for substantive claims.
No new axioms.

Goal: formalize the abstract finite-tree bookkeeping behind the ambient-sensitive FIE recursion.

Mathematical background:

We have recursive container states. Each internal node has:
- a potential value P(node) : ℝ,
- a nonnegative cost cost(node) : ℝ,
- two child nodes left(node), right(node).

The intended local inequality is:

cost(node) + P(left node) + P(right node) ≤ P(node).

The desired global theorem is the telescoping statement:

sum of internal costs + sum of leaf potentials ≤ root potential.

Tasks:

1. Define a simple finite binary tree type, or use an existing Mathlib tree type if convenient.

2. Define:
   - leaves,
   - internal nodes,
   - total leaf potential,
   - total internal cost.

3. Prove a theorem of the following mathematical form:

If every internal node satisfies

  cost v + potential (left v) + potential (right v) ≤ potential v

and all costs/potentials are nonnegative, then

  totalInternalCost tree + totalLeafPotential tree ≤ potential root.

4. If binary-tree formalization is too heavy, use an inductive recursive function:

inductive BinTree (α : Type) where
| leaf : α → BinTree α
| node : α → BinTree α → BinTree α → BinTree α

and prove the telescoping theorem by induction on `BinTree`.

5. Optional, only if easy:
   Prove a weighted version where an internal node also carries a "saving" term, and local inequality is

   cost v + saving v + P(left v) + P(right v) ≤ P(v).

   Then show

   totalCost + totalSaving + totalLeafPotential ≤ rootPotential.

Return:
- theorem names,
- any simplifications,
- whether the optional weighted theorem was completed.
```
