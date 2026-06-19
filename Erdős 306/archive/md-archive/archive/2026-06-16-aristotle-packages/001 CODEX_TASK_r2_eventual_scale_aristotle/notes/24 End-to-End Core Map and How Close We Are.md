# End-to-End Core Map and How Close We Are

Back to [[00 README]]. After reading CP 01 (the circle-method layer) and with the
cluster-selection atom now proved ([[23 Proof of the Reciprocal-Cluster Selection Lemma]]),
this note gives the **complete logical chain** from the Lean `sorry` down to the
proved/elementary bottom, with an **honest status** on each link.

## 1. The chain

$$
\boxed{\texttt{fourier\_positivity\_unconditional}}
\ \underset{\text{(L1) circle method}}{\Longleftarrow}\
\text{ConditionSBEE}
\ \underset{\text{(L2) single-block counting}}{\Longleftarrow}\
\text{non-dominant SBEE case}
\ \underset{\text{(L3) FIE}}{\Longleftarrow}\
\{\text{cluster selection}+\text{entropy descent}+\text{energy ledger}\}
$$

## 2. Link L1 — circle method (CP 01 §§3–7): STANDARD, not a research gap

Bernoulli model $Y=\sum_e\xi_eL/e$, target $\mathbb P(Y=L/b)>0$ via Fourier
inversion on $\mathbb Z/L$:
$$
\mathbb P(Y=L/b)=\tfrac1L\sum_h\widehat\mu(h)e(-h/b),\qquad
\widehat\mu(h)=\prod_e(1-\theta_e+\theta_e e(h/e)),\quad |\widehat\mu(h)|\le e^{-cQ_E(a)}.
$$
* **Main arc** ($h\equiv m$, $|m|\le C/\sigma_E$): Taylor ⇒
  $\widehat\mu(m)e(-m/b)=e^{-2\pi^2\sigma_E^2m^2+o(1)}$ (linear phase cancelled by
  mass tuning $\sum\theta_e/e=1/b$); sum $\asymp 1/\sigma_E>0$.
* **Minor arc**: $\sum_{h\notin\mathfrak M_C}|\widehat\mu(h)|\le\sum_{a\notin\mathfrak M_C}e^{-cQ_{\rm ctrl}(a)}=o_C(1/\sigma_E)$ — **this is the ONLY place SBEE enters** (via Prop 8.1).
* Positivity ⇒ deterministic subset, all denominators semiprime.

**Status:** standard analytic number theory. Inputs are lemma-bank items, all
proved or cited: Bernoulli Fourier bound (`BernoulliFourier.lean` ✓), lattice span
(`LatticeSpan.lean` ✓), edge construction + mass/variance tuning (Lemma 9.1,
construction), Irving (cited, for pruning only). **No open analytic theorem here**
— L1 is contingent only on SBEE (through the minor arc) and on the edge
construction delivering $\sigma_E\to0$ with $\sum\theta_e/e=1/b$.

## 3. Link L2 — SBEE ⇒ minor arc (CP 02 §4): bookkeeping

ConditionSBEE (single-block energy-entropy) gives the conditional single-block
counting theorem, hence Prop 8.1 (global control partition), hence the minor-arc
bound. The dominant and tiny cases are handled by Irving-good majority
correction; the **only nontrivial case is the non-dominant substantial case** =
the content of SBEE.

## 4. Link L3 — FIE ⇒ SBEE (the non-dominant case): the real content

The non-dominant substantial SBEE bound reduces (FIE/BCE route) to:
* **cluster selection** — the good-seed / reciprocal-cluster lemma:
  **PROVED** elementarily, [[23 Proof of the Reciprocal-Cluster Selection Lemma]],
  and interface-checked against the formalized pipeline (note 23 §6);
* **regular-uniqueness** (no short kernel ⇒ ≤1 witness per prime): proved
  (FIE draft §21);
* **singular-tuple sparsity** (power-thin): proved elementarily
  ([[18 What SBEE Actually Needs (Synthesis)]] §2, FIE draft §21.3);
* **ambient-sensitive entropy descent** (the recursive potential
  $\mathcal P(W,Y)=AW^4/(D^2X^2)+BW\log(eY/W)$ decreases enough to pay fingerprint
  + leaf entropy): "essentially proved up to dyadic log constants" per CP 02
  §3.1 / the FIE draft §§1–11 — its hard atom *was* the cluster selection, now
  closed;
* **energy ledger** (cross-label divisor energy pays the encoding): cross-label
  divisor-energy is proved (`CrossLabelEnergy.lean` / `SBEE.cross_label_divisor_energy` ✓).

## 5. Honest assessment: how close

* **No remaining *research-level analytic* gap is visible on this route.** The
  circle method (L1) is standard; the genuine combinatorial heart (cluster
  selection) is **proved**; the surrounding FIE pieces are proved or
  "essentially proved." The heavy Fourier/Kloosterman/Irving apparatus
  (notes 11–16) is confirmed **off** the critical path (Irving only in pruning).
* **What genuinely remains is assembly + verification + formalization, not new
  ideas:**
  1. **Edge construction (Lemma 9.1) — AUDITED ✓ (no gap found).** Checked
     line-by-line (CP 03 §9): mass tuning is clean ($M_0<1/(4b)$,
     $\Delta=1/b-M_0$, greedy batch $2\Delta\le W_H\le3\Delta$,
     $\theta_H=\Delta/W_H\in[1/3,1/2]$ ⇒ total mass exactly $1/b$, all
     $\theta_e\in[1/3,2/3]$); variance $\sigma_E^2=\sigma_{\rm ctrl}^2+o(\sigma_{\rm ctrl}^2)$
     (mass-edge variance $\ll 2^{-2K_1}W_H=o$), and $\sigma_E\asymp 2^{-k_0}/k_0\to0$
     so the main arc $\asymp1/\sigma_E\to\infty$; every prime incident to an edge
     (gadgets for $r\mid b$, $O_b(1)$, negligible) ⇒ Lemma 10.1 $\gcd=1$. It is a
     legitimate standard construction.
  2. **Entropy-descent potential algebra** — confirm the $\mathcal P(W,Y)$ descent
     closes with the cluster selection plugged in (the "dyadic log constants"
     and the two nested savings of CP 02 §3.1).
  3. **Formalization / de-islanding** — the whole L1–L3 chain is markdown; in Lean
     it is the assumed `ConditionSBEE` + the disconnected Component C
     ([[20 Lean Core Audit and Dependency Map]]). Wiring it is a large but
     idea-free Lean effort.
* **Caveat on confidence.** "Essentially proved up to log constants" and
  "standard construction" are exactly where hidden work tends to live. The Lean
  audit (note 20) already showed one such claim ("SBEE is proved") was false.
  So items 1–2 deserve the same line-by-line scrutiny the Lean core received
  before declaring the route closed.

## 6. Recommended next pushes (in order)

1. ~~**Audit the edge construction (Lemma 9.1)**~~ — **DONE ✓**, §5 item 1. No gap.
   So **L1 (circle method) is now fully audited and sound, conditional only on the
   minor-arc/SBEE input.**
2. **Verify the entropy-descent potential algebra** closes with note 23 plugged
   in (CP 02 §3.1 nested savings, ambient-FIE draft §§1–11). This is the one
   remaining unaudited mathematical link in L3.
3. **Formalize the chain** (Aristotle): start by formalizing note 23
   (`good_kSubset_exists_of_size`, note 23 §7) to de-island Component C, then the
   L1 circle-method skeleton against the lemma bank.

This is the first point in the project where the bottleneck is **audit +
assembly + formalization** rather than an unproved mathematical idea. After the
edge-construction audit, the only mathematical link not yet personally verified
is the entropy-descent algebra (item 2).
