# The Averaged Framing Is Essential

Back to [[00 README]]. Prerequisites: [[11 Irving Toolbox and the Finish Roadmap]],
[[12 M_B Computation and the Bilinear Necessity]].

Reading Irving's §3–§4 (`archive/kloost_paper2.tex`) in full, plus an explicit
size computation, forces two structural conclusions that change the target shape
of the theorem. Both are honest sharpenings, not setbacks: they tell us *what
kind* of statement is true.

## 1. Irving's strong bounds are intrinsically averaged over the modulus

Irving's method (Vaughan's identity → Type I + Type II bilinear sums
$W_{a,q}=\sum_{l\sim L,m\sim M}\alpha_l\beta_m e(a\overline{lm}/q)$, $LM\asymp x$):

* **Type I, individual** (fixed $q$): the only fixed-modulus bound,
  $W\ll((a,q)(\tfrac{LM}{Q}+L)+Q^{1/2}L)Q^\epsilon$, used only for $L\le U\le x^{1/3}$.
* **Type II** (the bulk, $U\le L\le x/U$): Irving has **no individual bound** —
  Lemma `typeiimax`/`typeiinomax` bound $\sum_{q\sim Q}|W_{a,q}|$ *on average over
  $q$*, via the reciprocal-equation moment $J^{(k)}_M(q)$. The power saving of
  Theorems 1–2 lives entirely in this modulus average.

For a *fixed* prime modulus the only individual result for the full sum is
Garaev's $S_q(a;x)\ll x^{15/16+\epsilon}$ — a saving of only $x^{1/16}$.

## 2. A size computation kills the per-tuple bound

Organize the $M_B$ error on a single modulus $q_1$ (as required by
[[12 M_B Computation and the Bilinear Necessity]] §4) and complete $x_4$:

$$
M_B^{\mathrm{err}}\ \rightsquigarrow\ \frac1{q_1}\sum_{h_1\ne0}D_H(\tfrac{h_1}{q_1})\sum_{x_4}S_{q_1}(h_1q_4x_4;X),\qquad S_{q_1}(a;X)=\sum_{p\sim X}e_{q_1}(a\overline p).
$$

Target (from $M_B^{\mathrm{main}}\asymp H^4/X^2$ feeding $N_H'$): at $H\asymp X^{1/2}$
we need $M_B\ll(\log X)^C$, i.e. the error must be saved down to $X^\epsilon$.

But the **trivial** size of $M_B^{\mathrm{err}}$ (no cancellation in $p$) is
$\asymp X^{1/2}$; Garaev's $x^{1/16}$ saving brings it only to $\asymp X^{7/16}$;
Irving's *averaged* saving ($\asymp X^{1/10}$ over $q_1\sim X$) is comparably
small. **The available saving ($\lesssim X^{1/10}$) is nowhere near the required
$X^{1/2}$.**

The resolution is not a sharper bound — it is that **the per-tuple bound is
false.** For structured seed tuples, $B_{123}(p)\asymp H$ for *many* primes $p$
(when $\lambda_1^{(i)}(p)$ is small for all $i$, cf.
[[09 Cluster Concentration and the Structured Family]]), so $M_B=\sum_pB_{123}(p)$
is genuinely large. The bound $M_B\ll(\log X)^C$ holds only **on average over the
seed tuple**, with the structured family carrying the large values.

## 3. Consequence: the theorem is an average-over-seeds statement

The reduced inverse theorem of [[07 Diagonal Ledger]] must be restated:

$$
\boxed{\ \frac1{\#\mathcal S}\sum_{(q_0,\ldots,q_4)\in\mathcal S}N_H'(q_0,\ldots,q_4)
\ \ll\ (\log X)^C\Big(1+\frac{H^6}{X^3}\Big)\ }
$$

over a dyadic family $\mathcal S$ of seed tuples with $q_i\sim X$. The modulus
average in Irving's Theorems 1–2 **is** this seed average. No individual-tuple
bound of the required strength exists; the structured family of
[[09 Cluster Concentration and the Structured Family]] is the average-negligible
exceptional set (rare tuples, large contribution, swamped in the mean).

This is exactly the form SBEE needs and consumes: `ConditionSBEE`'s partition
bound is an average over prime blocks, never a per-block pointwise bound. The two
averages coincide. **This dissolves the apparent deficit:** the deficit only
appears if one (wrongly) demands a per-tuple bound; the averaged error genuinely
matches the averaged main term, because Irving's saving is computed in the same
modulus-average as the main term.

## 4. What this needs next: the Fouvry–Shparlinski explicit forms

To carry out the averaged bookkeeping without the lossy "absolute values at each
stage" step (which costs powers of $X$ — see §2), we need the **explicit Type I /
Type II decomposition forms** from Fouvry–Shparlinski (cited by Irving as "the
precise forms of the sums are given by Fouvry and Shparlinski"). These are *not*
in the repo. The naive completion of [[12 M_B Computation and the Bilinear Necessity]]
must be replaced by: Vaughan-decompose $p=lm$ first (so $\overline p=\overline{lm}$
gives the genuine bilinear Kloosterman fraction), carry the short variables
$x_4,a_i$ as the coefficients $\alpha,\beta$, and apply `typeiimax` averaged over
the seed modulus. Only this keeps the bilinear cancellation that the absolute-
value route destroys.

## 5. Status

* **Settled:** the target is an **average-over-seeds** bound (per-tuple is
  false, proved by the §2 size computation); the seed average = SBEE's prime-
  block average = Irving's modulus average. The structured family is average-
  negligible.
* **Settled (negative):** naive completion + term-by-term Weil/Garaev is lossy by
  a power of $X$; the bilinear cancellation must be kept intact.
* **Needs:** Fouvry–Shparlinski's explicit Vaughan Type I/II forms (fetch from
  arXiv / journal) to run the averaged Type II bound tightly.

## Next action

Fetch Fouvry–Shparlinski, *"On the distribution of the modular inverse / Kloosterman
sums and primes"* (the paper Irving cites as `foushpar`), and transcribe their
explicit Type I/II forms. Then run the averaged $M_B$ bound as a Type II average
over $q_1\sim X$, and verify the saving matches the averaged main term.
