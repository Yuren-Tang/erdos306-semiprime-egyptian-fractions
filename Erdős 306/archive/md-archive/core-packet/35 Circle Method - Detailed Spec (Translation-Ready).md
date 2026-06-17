# Circle Method: Detailed Spec (Translation-Ready)

Back to [[00 README]]. The final layer: from the global control theorem
([[34 Global Control - Detailed Proof (Translation-Ready)]], G7 = Prop 8.1) to
`fourier_positivity_unconditional`, hence `erdos_306`. This is CP 01 §§3–7
(audited; edge construction audited in note 24), restated deterministically
(no probability) with the key computations done.

## C0. Definitions

**Construction** (for given squarefree $b>0$ and finite obstruction set $T$):
* A BlockSystem (note 34 G0) with $2^{k_0}>\max(T\cup\{b\}\cup\{X_0\})$.
* **Edge set** $E$ = finite set of pairs $\{p,q\}$, $p\ne q\in\mathcal P\cup\{r:r\mid b\}$:
  $E_{\rm int}\cup E_{\rm skel}$ (the control pairs of G0) $\cup\ E_{\rm mass}$
  (high-scale bipartite pairs, blocks $K_1\le k\le K$) $\cup\ E_{\rm gad}$
  (for each prime $r\mid b$: one pair $\{r,s_r\}$, $s_r$ a fresh high prime).
* **Weights** $\theta:E\to[1/3,2/3]$ with the **mass identity**
  $\sum_{e\in E}\theta_e/\mathrm{val}(e)=1/b$, where $\mathrm{val}(\{p,q\})=pq$.
* $L:=\prod_{p\in\mathcal P_E}p$ over all primes appearing; $b\mid L$ (gadgets).
* $\sigma_E^2:=\sum_e\theta_e(1-\theta_e)\mathrm{val}(e)^{-2}$; required:
  $\sigma_E\asymp\sigma_{\rm ctrl}$ and $1/(\sigma_E\cdot\min_{e\in E_{\rm mass}\cup E_{\rm gad}}\mathrm{val}(e))\le2^{-k_0}k_0$ (high edges don't disturb the main arc).

**The weighted count (deterministic; no probability).** For $x\in\{0,1\}^E$ put
$w(x):=\prod_e\theta_e^{x_e}(1-\theta_e)^{1-x_e}>0$ and
$$W:=\sum_{x\in\{0,1\}^E}w(x)\cdot\mathbf 1\Big[\sum_ex_e\,\tfrac L{\mathrm{val}(e)}=\tfrac Lb\Big].$$
**$W>0$ ⟺ ∃ subset $S\subseteq E$ with $\sum_{e\in S}1/\mathrm{val}(e)=1/b$** (all
weights positive). That subset gives the representation (each $\mathrm{val}(e)$ a
squarefree semiprime $>\max T$, distinct) ⟹ `HasEgyptianSemiprimeReprAvoiding T (1/b)`.

**Fourier identity (finite orthogonality on $\mathbb Z/L$).**
$$W=\frac1L\sum_{h=0}^{L-1}\widehat\mu(h)\,e(-h/b\cdot\ldots)\quad\text{precisely}\quad
W=\frac1L\sum_{h\bmod L}\Big[\prod_{e\in E}\big(1-\theta_e+\theta_e\,e(h/\mathrm{val}(e))\big)\Big]e(-h/b),$$
using $\tfrac1L\sum_he(hn/L)=\mathbf1[L\mid n]$ and $\tfrac{h}{\mathrm{val}(e)}=\tfrac{h\,L/\mathrm{val}(e)}L$. Pure finite algebra.

## C1. Edge construction (Lemma 9.1; audited note 24 — translate)

Existence of the Construction with all C0 properties. Proof = CP 03 §9 verbatim
(mass tuning: $M_0<1/(4b)$ from control+gadget at $\theta=1/2$… greedy batch $H$
with $2\Delta\le W_H\le3\Delta$, $\theta_H=\Delta/W_H\in[1/3,1/2]$ ⟹ mass exactly
$1/b$; variance dominated by $\sigma_{k_0}$). **External input needed: block
density** $\pi(2x)-\pi(x)\ge x/(2\log x)$ for $x\ge x_0$ — Chebyshev-type; check
Mathlib (`Nat.primeCounting` bounds / Bertrand iterations / central-binomial
route); if absent, isolate as ONE named hypothesis `chebyshev_block_density` with
a documented elementary proof path (central binomial coefficient). Everything
else is finite/greedy bookkeeping.

## C2. The pointwise Fourier bound (extend `product_charFun_bound`)

> For $h\bmod L$, let $a(h):=(h\bmod p)_p$ (CRT bijection). Then
> $$\big|\widehat\mu(h)\big|\le\exp\Big(-\tfrac{16}9\,Q_E(a(h))\Big),\qquad
> Q_E(a):=\sum_{e=\{p,q\}\in E}\Big(\frac{H_{pq}(a)}{pq}\Big)^2.$$

*Computation.* $|1-\theta+\theta e(t)|^2=1-4\theta(1-\theta)\sin^2(\pi t)$;
$\theta\in[\tfrac13,\tfrac23]$ ⟹ $\theta(1-\theta)\ge\tfrac29$; $\sin^2(\pi t)\ge4\|t\|^2$
⟹ $|{\cdot}|^2\le1-\tfrac{32}9\|t\|^2\le e^{-\frac{32}9\|t\|^2}$. And
$\|h/\mathrm{val}(e)\|=\|H_{pq}(a(h))/pq\|=|H_{pq}|/pq$ (centered). Multiply over $e$. $\square$

Also $Q_E\ge Q_{\rm ctrl}$ (control pairs $\subseteq E$, terms $\ge0$).

## C3. Main arc

$\mathfrak M_C$ as in G6, with $|m|\le C/\sigma_E$. For $h$ with $a(h)\equiv m$:

> $$\widehat\mu(h)e(-h/b)=\exp\big(-2\pi^2m^2\sigma_E^2+\delta_m\big),\qquad
> |\delta_m|\le 60\,\big(|m|^3{\textstyle\sum_e}\mathrm{val}(e)^{-3}+|m|^4{\textstyle\sum_e}\mathrm{val}(e)^{-4}\big)\le\tfrac1{10}$$
> for $|m|\le C/\sigma_E$ and $k_0\ge k_0(C)$, using the **exact linear cancellation**
> $\sum_e\theta_e\,2\pi m/\mathrm{val}(e)=2\pi m/b$ (mass identity) against $e(-m/b)$,
> and $|m|^3\sum\mathrm{val}^{-3}\le|m|^3\sigma_E^2\cdot\max\mathrm{val}^{-1}\cdot\tfrac92\le\tfrac92C^3/(\sigma_E\,4^{k_0})\to0$.

*Proof sketch (standard complex-log Taylor; all bounds explicit):*
$\log(1-\theta(1-e(t)))=2\pi i\theta t-2\pi^2\theta(1-\theta)t^2+O(|t|^3)$ with the
$O$-constant absolute for $|t|\le\tfrac1{10}$ (here $t=m/\mathrm{val}(e)$,
$|t|\le C/(\sigma_E 4^{k_0})\le\tfrac1{10}$ ✓). Hence
$$\sum_{h\in\mathfrak M_C}\widehat\mu(h)e(-h/b)\ \ge\ \tfrac12\sum_{|m|\le C/\sigma_E}e^{-2\pi^2m^2\sigma_E^2}-\ldots\ \ge\ \frac{c_3(C)}{\sigma_E},\qquad c_3(C)\ge\tfrac14\ \text{for }C\ge1.$$

## C4. Minor arc

$$\sum_{h\notin\mathfrak M_C}|\widehat\mu(h)|\ \le\ \sum_{a\notin\mathfrak M_C}e^{-\frac{16}9Q_{\rm ctrl}(a)}\ \le\ \Big(C_{\rm glob}e^{-F_0}+C_1e^{-C^2}\Big)\frac1{\sigma_{\rm ctrl}}$$
by C2, $Q_E\ge Q_{\rm ctrl}$, the CRT bijection $h\leftrightarrow a$, and **G7**
(with $c=16/9$). With $\sigma_E\asymp\sigma_{\rm ctrl}$: choose $k_0$ large
(kills $C_{\rm glob}e^{-F_0}$), then $C$ large (kills the tail), so that the
minor arc is $\le\tfrac12\,c_3(C)/\sigma_E$.

## C5. Positivity and extraction (closes the sorry)

$LW=\sum_{\mathfrak M_C}+\sum_{\rm minor}\ \ge\ \tfrac{c_3}{\sigma_E}-\tfrac{c_3}{2\sigma_E}>0$
⟹ $W>0$ ⟹ ∃$S\subseteq E$: $\sum_{e\in S}1/\mathrm{val}(e)=1/b$, all values
distinct squarefree semiprimes, each $>\max T$ (initial scale; gadget values
$rs_r>s_r>\max T$) ⟹
**`fourier_positivity_unconditional T b hb hbsf : HasEgyptianSemiprimeReprAvoiding T (1/b)`.**
Then `erdos_306` is sorry-free via the already-verified
`reduction_to_unit_numerator_avoiding`.

## W. Wiring & cleanup

1. Implement C0–C5 (files: `GlobalControl.lean` for note 34, `CircleMethod.lean`
   for C0–C5), closing the `FourierPositivity.lean` sorry.
2. Check `erdos_306` end-to-end sorry-free; `#print axioms erdos_306`.
3. Deprecate/delete the superseded placeholders: old `SBEE.lean` chain lemmas,
   `SingleBlockCounting.lean` abstract `sbee_nondominant`, `BlockCRTEnergy.lean`
   `*_uniform` stubs (or derive them from the new results where statements match).
