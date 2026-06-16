# R2 Terminal Mathematical Gap

Status date: 2026-06-16.

## Current Formal Endpoint

The strongest current Lean endpoint is:

```lean
CircleMethod.exists_arcConstruction_of_selectedQ_coreSupply_autoWeights_choiceMinor
```

It reduces `ArcConstruction T b` to terminal R2 supply data:

1. a residual mass batch `Q`;
2. a component/core supply for control edges and gadget edges;
3. numeric main-arc scale estimates;
4. a minor classification into a block part and an extra part;
5. block-lane estimates for the block part;
6. extra-gadget damping data for the extra part.

The Fourier positivity assembly after `ArcConstruction` is no longer the local
obstacle. The local obstacle is the construction of the terminal R2 supply.

## Important Correction

The present extra-lane interface is too weak for the final asymptotic proof if
used literally.

`R2ExtraMinorGadgetChoiceData` chooses one gadget edge \(r_h s_h\) for each
extra frequency \(h\), giving a bound of the shape

\[
\sum_{h\in S_{\mathrm{extra}}} |\widehat{\mu}(h)|
  \le |S_{\mathrm{extra}}| D_r .
\]

But the number of main-arc sibling frequencies is typically

\[
|S_{\mathrm{extra}}| \asymp \frac{C}{\sigma_{\mathrm{ctrl}}}\cdot O_b(1),
\]

so one fixed damping factor \(D_r<1\) does not beat the required
\(O(1/\sigma_{\mathrm{ctrl}})\) budget uniformly in \(C\). The mathematical
argument described in the notes needs a product of several independent gadget
factors:

\[
|S_{\mathrm{extra}}| D_r^G
  \ll \frac{1}{\sigma_{\mathrm{ctrl}}},
\qquad
G \asymp_b \log C .
\]

Thus the next main task is not another wrapper around the one-gadget interface,
but a multi-gadget extra lane.

## Correct Extra-Lane Lemma

Fix a main-arc field `MA` and a frequency \(h\in MA.Sm\). Let

\[
a_h(p) = h \pmod p
\]

for \(p\in \operatorname{blockSupport}(BS)\). Put \(h\) into the block lane if
\(a_h\notin \mathfrak M_C\). Otherwise \(a_h\in\mathfrak M_C\), so there exists
an integer label \(m\) with

\[
|m| \le \frac{C}{\sigma_{\mathrm{ctrl}}},\qquad
h\equiv m \pmod s
\]

for every block prime \(s\in \operatorname{blockSupport}(BS)\).

Since \(h\in MA.Sm\), \(h\) is not congruent modulo the full period \(L\) to any
label in \([-N,N]\). If \(N\) is chosen so that \(C/\sigma_{\mathrm{ctrl}}\le N\),
then \(h\not\equiv m\pmod L\). Because the block-prime congruences already hold,
the failure must occur in the denominator part. Therefore one needs a component
hypothesis saying that the denominator gadget primes cover the prime divisors
of \(b\):

\[
\forall r,\quad r\mid b,\ r\ \text{prime} \Longrightarrow r\in R.
\]

Then there is \(r\in R\) such that

\[
h\not\equiv m \pmod r.
\]

For every chosen \(s\in S\subseteq\operatorname{blockSupport}(BS)\), we have
\(h\equiv m\pmod s\), and if \(s\) is large enough that

\[
2|m|<s,
\]

the already-proved lemma `gadget_charFun_damp` gives

\[
\left|\varphi_{\theta_{rs}}\!\left(\frac{h}{rs}\right)\right|
  \le D_r
  := \sqrt{1-\frac{8}{9r^2}} < 1 .
\]

If we choose \(G_r(C)\) distinct primes \(s\in S\) for each denominator prime
\(r\mid b\), then every extra frequency with offset at \(r\) gains the product
bound

\[
|\widehat\mu(h)| \le D_r^{G_r(C)}.
\]

Choosing \(G_r(C)\) so that

\[
(2C/\sigma_{\mathrm{ctrl}}+1)\,D_r^{G_r(C)}
  \le \frac{\eta_r}{\sigma_{\mathrm{ctrl}}},
\]

and summing over the finitely many \(r\mid b\), gives the required extra budget

\[
\sum_{h\in S_{\mathrm{extra}}} |\widehat\mu(h)|
  \le \frac{\eta_{\mathrm{extra}}}{\sigma_{\mathrm{ctrl}}}.
\]

## Required New Lean Interface

Replace the one-gadget extra choice data by multi-gadget data:

```lean
structure R2ExtraMinorMultiGadgetChoiceData ... where
  Gset : ℕ → Finset ℕ
  rfun : ℕ → ℕ
  mfun : ℕ → ℤ
  hRmem : ∀ h ∈ extraMinorPart ..., rfun h ∈ D.R
  hSmem : ∀ h hh, Gset h ⊆ D.S
  hCard : ∀ h hh, Gmin (rfun h) ≤ (Gset h).card
  hm_s : ∀ h hh, ∀ s ∈ Gset h, (h : ZMod s) = (mfun h : ZMod s)
  hm_r : ∀ h hh, (h : ZMod (rfun h)) ≠ (mfun h : ZMod (rfun h))
  hm_small : ∀ h hh, ∀ s ∈ Gset h, 2 * |mfun h| < (s : ℤ)
  hbudget :
    ∑ h ∈ extraMinorPart ..., (Damp (rfun h)) ^ (Gset h).card ≤ Bextra
```

The existing one-gadget lemma becomes the pointwise factor used inside the
product proof. The new work is to prove:

```lean
theorem r2_extra_minor_budget_of_multiGadgetData :
  ∑ h ∈ extraMinorPart ..., fourierNormWeight ... h ≤ Bextra
```

## Is External Literature Needed?

Not at this local terminal step. It is finite CRT, finite products, and
elementary inequalities:

* the already-proved CRT damping lemma;
* finite product norm bounds;
* \(D_r^G\) beating \(C\) with \(G=O(\log C)\);
* enough large block primes in `S` to choose the required disjoint gadget primes.

Literature may still be relevant for global prime-density choices if the
current dyadic-prime infrastructure is insufficient, but the terminal gap above
does not itself require citing new analytic number theory.
