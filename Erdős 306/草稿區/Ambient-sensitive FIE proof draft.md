# Ambient-sensitive FIE proof draft

Back to [[CP 00 Navigation]] and [[SBEE dyadic proof draft]].

This is the focused working note for the current final route:

$$
\text{ambient-sensitive FIE}
\Longrightarrow
\text{BCE}
\Longrightarrow
\text{SBEE}.
$$

The older [[SBEE dyadic proof draft]] remains the historical scratch file. This note starts from the corrected state after Sections 75--78 there.

---

# 1. Parameters

Fix one dyadic non-dominant substantial profile.

Let

$$
N=|P|\asymp \frac X{\log X},
\qquad
D=sL_X,
$$

where $s=|\mathcal L|$ is the short-list size and $L_X$ is the logarithmic substantiality scale.

A residual state is a pair

$$
(W,Y),
$$

where:

- $W$ is the residual labelled mass;
- $Y$ is the current ambient universe size from which the residual labelled vertices may be chosen.

Initially,

$$
W_0\asymp N,
\qquad
Y_0\asymp Ns\asymp \frac{ND}{L_X}.
$$

In a saturated state, put

$$
M=\frac WD.
$$

The Lean-supported finite infrastructure gives, after dyadic losses, a fingerprint step with:

$$
|F|\ll \frac WD(\log X)^B,
$$

capturing mass

$$
W_1=\alpha W,
\qquad
\alpha\ge(\log X)^{-B},
$$

inside a fingerprint-determined ambient container of size

$$
Y_1
\ll
\left(N+\frac{W^2}{D^2}\right)(\log X)^B.
$$

The complement branch is

$$
W_2=(1-\alpha)W,
\qquad
Y_2=Y.
$$

---

# 2. Entropy algebra

Define the crude ambient entropy

$$
H(W,Y)=W\log\frac{eY}{W}.
$$

For the split

$$
(W,Y)\to(\alpha W,Y_1),((1-\alpha)W,Y),
$$

we have the exact identity

$$
H(W,Y)
-
H(\alpha W,Y_1)
-
H((1-\alpha)W,Y)
$$

$$
=
\alpha W\log\frac{Y}{Y_1}
+
W\left(\alpha\log\alpha+(1-\alpha)\log(1-\alpha)\right).
$$

Since

$$
\alpha\log\alpha+(1-\alpha)\log(1-\alpha)
\ge
-C\alpha\log\frac1\alpha
$$

for $0<\alpha\le1/2$, the entropy drop is useful when

$$
\log\frac{Y}{Y_1}
\gg
\log\frac1\alpha.
$$

The fingerprint cost at this node is

$$
E_{\rm fp}(W,Y)
\ll
\frac WD(\log X)^B\log Y.
$$

Thus the net entropy saving is positive if

$$
\alpha W
\left(
\log\frac{Y}{Y_1}
-C\log\frac1\alpha
\right)
\gg
\frac WD(\log X)^B\log Y.
$$

After dividing by $W$, this requires

$$
\alpha
\left(
\log\frac{Y}{Y_1}
-C\log\frac1\alpha
\right)
\gg
\frac{(\log X)^B\log Y}{D}.
$$

Since $\alpha\ge(\log X)^{-B}$, the right side is harmless whenever $D$ is a positive power of $N$.

---

# 3. Energy-dominated range

The initial bucket-capacity scale is

$$
R_0
\asymp
\frac{N^4}{D^2X^2}
\asymp
\frac{X^2}{D^2(\log X)^4}.
$$

The initial crude entropy is

$$
H(N,Y_0)
\ll
N\log s
\ll
N\log D+O(N\log\log X).
$$

Thus crude entropy is already paid if

$$
\frac{X^2}{D^2(\log X)^4}
\gg
\frac X{\log X}\log D.
$$

Equivalently, up to fixed logarithmic losses,

$$
D\ll N^{1/2}(\log X)^{-C}.
$$

In this range, no delicate ambient recursion is needed. The non-saturated energy or the base bucket-capacity lower bound already pays the profile entropy.

---

# 4. Ambient-saving range

Assume now

$$
D\gg N^{1/2}(\log X)^{-C}.
$$

At the root,

$$
Y_0\asymp \frac{ND}{L_X}.
$$

For $W\asymp N$, the captured branch has ambient size

$$
Y_1
\ll
\left(N+\frac{N^2}{D^2}\right)(\log X)^B.
$$

Since $D\gg N^{1/2}(\log X)^{-C}$,

$$
\frac{N^2}{D^2}\ll N(\log X)^{2C},
$$

and therefore

$$
Y_1\ll N(\log X)^{B+2C}.
$$

Hence

$$
\frac{Y_0}{Y_1}
\gg
\frac{D}{(\log X)^{B+2C+1}}.
$$

So one first capture of a typical unit of mass saves about

$$
\log D-O(\log\log X)
$$

bits of entropy, exactly the scale needed to pay the original label-list entropy.

This is the key improvement over one-parameter peeling.

---

# 5. First-capture accounting

Run the saturated exposure recursively on the complement branch until either:

1. the remaining mass enters an energy-dominated small-mass regime;
2. a non-saturated deficit forces energy;
3. essentially all mass has been captured into fingerprint-determined containers.

Each unit of mass is charged at the first node where it enters a reduced ambient container.

If the parent ambient is still comparable with $Y_0$, the saving per unit is

$$
\gg
\log D-O(\log\log X).
$$

The total saving over captured mass $\asymp N$ is therefore

$$
\gg
N\log D-O(N\log\log X),
$$

which matches the initial crude label entropy.

The remaining complement mass after repeated captures is small. Since each step captures at least

$$
\alpha W,
\qquad
\alpha\ge(\log X)^{-B},
$$

after

$$
O((\log X)^B\log N)
$$

steps the complement mass is negligible. The accumulated fingerprint cost is

$$
\sum_j
\frac{W_j}{D}(\log X)^B\log Y_0
\ll
\frac{N}{\alpha D}(\log X)^B\log Y_0.
$$

Since $D\gg N^{1/2}(\log X)^{-C}$, this is

$$
o(N\log D)
$$

provided the logarithmic slack in the fingerprint bound is fixed first and the final overlap constant is chosen afterward.

Thus in the ambient-saving range, fingerprint costs are lower order and the first-capture entropy saving pays the initial label entropy.

---

# 6. Remaining lemma to prove

The focused final lemma is now:

**First-capture saving lemma.**  
In the range

$$
D\gg N^{1/2}(\log X)^{-C},
$$

the recursive saturated exposure algorithm either forces non-saturated energy, or captures all but $o(N)$ mass into fingerprint-determined containers, with total encoding entropy

$$
o(R)+O(N\log\log X)
$$

after subtracting the first-capture ambient savings. The remaining $O(N\log\log X)$ is harmless in the final SBEE sum because the overlap constants are chosen so that either the base-list lower bound for $R$ or the non-saturated energy ledger absorbs fixed logarithmic losses.

Together with the energy-dominated range

$$
D\ll N^{1/2}(\log X)^{-C},
$$

this gives a genuine logarithmic overlap around $D\asymp N^{1/2}(\log X)^{-C}$, rather than a gap. This would prove ambient-sensitive FIE once the first-capture counting tree is written rigorously.

---

# 7. Current status

The signs are positive.

The problem is now a finite container-saving proof:

$$
\boxed{
\text{first-capture ambient entropy saving}
}
$$

rather than a search for a new Kloosterman or large-sieve input.

The only remaining delicate points are:

1. making "typical unit of mass is first-captured from ambient $Y_0$" precise in a labelled-transversal counting tree;
2. proving that small leftover complements are energy-paid before their crude entropy matters;
3. summing dyadic profiles and logarithmic losses.

This note should be the active working file for the next pass.

---

# 8. Critical audit: the leftover polylog ambient entropy

The first-capture saving pays the main label-list entropy

$$
N\log D
$$

in the ambient-saving range. But after first capture the branch ambient is only known to be

$$
Y_1\ll N(\log X)^K
$$

in the critical case $D\asymp N^{1/2}$, for some fixed $K$.

Crude counting inside this ambient leaves

$$
H(N,Y_1)
\ll
N\log\log X.
$$

This is not automatically harmless.

Indeed the base-list lower bound gives only

$$
R
\gg
\frac{D^2}{L_X^2(\log X)^2}.
$$

At the central scale

$$
D\asymp N^{1/2},
$$

this is roughly

$$
R\gg \frac{N}{(\log X)^{O(1)}},
$$

which is smaller than $N\log\log X$.

Thus the first-capture argument is a major saving, but not the full SBEE proof. The remaining logarithmic entropy must be removed by an additional argument.

This is an important correction to the optimistic reading of Section 6.

---

# 9. Second-stage target: polylog-ambient compression

After first capture, the residual branch has ambient size

$$
Y\le N(\log X)^K.
$$

Equivalently, each prime has only polylogarithmically many possible labels on average. The remaining entropy is

$$
O(N\log\log X).
$$

The next required lemma is:

**Polylog-ambient compression lemma.**
In a non-dominant substantial residual state with

$$
W\asymp N,
\qquad
Y\le N(\log X)^K,
$$

either:

1. the non-saturated energy ledger contributes at least
   $$
   \gg N\log\log X;
   $$
2. or a further saturated exposure step reduces the average label multiplicity from $(\log X)^K$ to $(\log X)^{K-\kappa}$ for some $\kappa>0$;
3. or the residual becomes structurally near-dominant / rank-one and exits the non-dominant substantial SBEE case.

Iterating this lemma $O_K(1)$ times would reduce the ambient entropy from

$$
N\log\log X
$$

to $O(N)$ or less. A final sharper version must reduce it to $o(R)$ in the central range, so either the last step needs a stronger structural conclusion or the energy ledger must improve once the average label multiplicity is bounded.

This is now the honest local problem:

$$
\boxed{
\text{polylog-ambient compression after first capture}
}
$$

It is much smaller than the original SBEE because:

- the large label-list entropy has already been removed;
- all finite exposure tools are available;
- the ambient has only polylogarithmic multiplicity per prime;
- rank-one rigidity is available for coherent low-defect rectangles.

But it is still a real mathematical step.

---

# 10. Revised status

The route now has two nested savings:

1. **First-capture saving:** removes the main $N\log D$ entropy when $D$ is large.
2. **Polylog-ambient compression:** still needed to remove the leftover $N\log\log X$ entropy in the central range.

This means the signs are still positive, but the proof is not yet down to a purely formal bookkeeping lemma.

The next mathematical work should focus on Section 9, not on further global restructuring.

---

# 11. Possible route for polylog-ambient compression

Suppose after first capture we are in a branch with

$$
Y\le N(\log X)^K.
$$

Write the effective average label multiplicity as

$$
L_{\rm eff}=\frac YN\le(\log X)^K,
$$

and set the effective bucket profile size

$$
D_{\rm eff}=L_{\rm eff}L_X.
$$

Since $D_{\rm eff}$ is only polylogarithmic, the non-saturated deficit scale becomes very large:

$$
R_{\rm cap}^{\rm eff}(N,D_{\rm eff})
\asymp
\frac{N^4}{D_{\rm eff}^2X^2}
\asymp
\frac{X^2}{D_{\rm eff}^2(\log X)^4}.
$$

For fixed $K$, this is much larger than

$$
N\log\log X
$$

once the logarithmic constants are ordered correctly. Therefore, in the polylog-ambient state:

- non-saturation immediately pays the remaining entropy;
- only deeply saturated configurations need to be counted.

In the saturated case, the relevant typical degree is

$$
M_{\rm eff}=\frac{W}{D_{\rm eff}}.
$$

Thus a fingerprint has size roughly

$$
|F|\ll \frac{W}{D_{\rm eff}}(\log X)^B.
$$

For $W\asymp N$ and $D_{\rm eff}=(\log X)^{K+O(1)}$, this is

$$
|F|\ll \frac{N}{(\log X)^{K-O(B)}}.
$$

If $K$ is chosen much larger than all fingerprint and dyadic loss exponents, then the entropy of one such fingerprint is

$$
|F|\log Y
\ll
\frac{N}{(\log X)^{K-O(B)}}\log X
=
o(R)
$$

in the central range.

This suggests the following compression mechanism.

**Polylog saturated compression principle.**
In a residual state with $Y\le N(\log X)^K$, either non-saturation pays the remaining entropy, or a saturated fingerprint of size $N/(\log X)^{K-O(1)}$ determines a positive polylogarithmic fraction of the remaining choices. Iterating this for $O((\log X)^{O(1)})$ rounds has total fingerprint entropy $o(R)$ if $K$ was initially chosen large enough.

The point is that the first-capture step should leave not just an arbitrary polylog ambient, but a polylog ambient with an exponent $K$ that we are free to make large by reserving logarithmic slack in the earlier thresholds.

This may remove the $N\log\log X$ residue without needing a new analytic estimate.

The proof still needs a precise finite statement:

1. define $D_{\rm eff}$ for a non-product ambient container;
2. show the non-saturated deficit lemma still applies with $D_{\rm eff}$ replacing the original $D$;
3. show saturated fingerprints can be iterated without losing the container structure;
4. bound the total number of rounds by the repeated-exposure budget.

This is a good candidate for the next paper-side proof block.
