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

---

# 12. Correction: average multiplicity is not the bucket parameter

The definition

$$
L_{\rm eff}=\frac YN
$$

is useful for crude transversal entropy, but it is not by itself the correct
parameter for the bucket-capacity side of the proof.

The issue is that a non-product ambient set

$$
A\subset P\times\mathcal L
$$

may have only polylogarithmically many labels per prime on average while still
having a large occupancy in a special bucket. Thus the non-saturated deficit
cannot safely use

$$
D_{\rm eff}=L_{\rm eff}L_X
$$

unless an additional bucket-regularity statement is proved.

The right residual state should therefore record not only

$$
(W,Y),
$$

but also a new-bucket capacity parameter.

For a set of already exposed buckets $\mathcal C$ define

$$
\Delta_{\rm new}(A;\mathcal C)
=
\sup_{n\notin\mathcal C}
\#\{v\in A:n\in\mathcal B_\tau(v)\}.
$$

The entropy term

$$
W\log\frac{eY}{W}
$$

counts choices inside the ambient, while the cheap-pair deficit uses

$$
\Delta_{\rm new}(A;\mathcal C)
$$

rather than $Y/N$.

This is a tightening of Section 11. The polylog ambient is still valuable, but
only after it is coupled to a bound for new bucket occupancies or to a structural
alternative when such a bound fails.

---

# 13. New-bucket capacity after one generated core

The generated-core container has an important extra property that was implicit
in the old high-common-neighbour discussion.

Let $\mathcal C$ be a bucket core and put

$$
A_h(\mathcal C)
=
\{v:d_{\mathcal C}(v)\ge h\}.
$$

Assume the marked dual uniqueness property:
for every two distinct buckets $n\ne n'$, there is at most one labelled vertex
incident to both $n$ and $n'$.

Then for every new bucket $n\notin\mathcal C$,

$$
\#\{v\in A_h(\mathcal C): n\in\mathcal B_\tau(v)\}\cdot h
\le
|\mathcal C|.
$$

Indeed, every such vertex contributes at least $h$ pairs

$$
(v,c),\qquad c\in\mathcal C,\quad c\in\mathcal B_\tau(v).
$$

For each fixed $c\in\mathcal C$, the pair of buckets $(n,c)$ is incident to at
most one labelled vertex. Hence the total number of pairs is at most
$|\mathcal C|$.

Thus

$$
\Delta_{\rm new}(A_h(\mathcal C);\mathcal C)
\le
\frac{|\mathcal C|}{h}.
$$

In the saturated first-capture regime,

$$
|\mathcal C|\ll M^2(\log X)^B,
\qquad
h\gg \frac{M}{(\log X)^B},
\qquad
M=\frac WD,
$$

so the captured ambient has new-bucket capacity

$$
\Delta_{\rm new}
\ll
M(\log X)^{O(B)}.
$$

This is a real structural gain over an arbitrary ambient set of size
$N(\log X)^K$. But it is not yet the full polylog compression. At the central
scale

$$
D\asymp M\asymp N^{1/2},
$$

the new-bucket capacity remains of the same order as the original saturated
scale. Therefore the leftover $N\log\log X$ entropy cannot be removed merely by
replacing $D$ with an average label multiplicity.

The new-bucket capacity lemma is still valuable because it makes the next
saturated step highly constrained relative to the first core.

---

# 14. Two-core density from a second saturated exposure

Suppose the first saturated exposure gives a core $\mathcal C_0$ and the
residual branch lies in

$$
A_0=A_{h_0}(\mathcal C_0).
$$

Assume a second saturated exposure occurs inside this residual branch, producing
a new core $\mathcal C_1$ with threshold $h_1$ and residual set $\Gamma$ of mass
$W$ such that every $v\in\Gamma$ has

$$
d_{\mathcal C_0}(v)\ge h_0,
\qquad
d_{\mathcal C_1}(v)\ge h_1.
$$

Define a bipartite graph

$$
G_\Gamma(\mathcal C_0,\mathcal C_1)
\subset
\mathcal C_0\times\mathcal C_1
$$

by putting an edge $(c_0,c_1)$ whenever some $v\in\Gamma$ is incident to both
$c_0$ and $c_1$.

By the same marked dual uniqueness, a fixed pair $(c_0,c_1)$ is generated by at
most one labelled vertex. Hence the pairs contributed by distinct vertices are
disjoint, and

$$
e(G_\Gamma(\mathcal C_0,\mathcal C_1))
\ge
W h_0h_1.
$$

Since

$$
|\mathcal C_i|\ll M^2(\log X)^B,
\qquad
h_i\gg \frac{M}{(\log X)^B},
$$

the edge density satisfies

$$
\delta
\ge
\frac{W h_0h_1}{|\mathcal C_0||\mathcal C_1|}
\gg
\frac{W}{M^2}(\log X)^{-O(B)}
=
\frac{D^2}{W}(\log X)^{-O(B)}.
$$

Thus in the central range

$$
D^2\asymp W,
$$

the two-core graph is polylogarithmically dense. If $D^2\gg W(\log X)^C$, this
density bound is too large unless the second saturated scenario has already
collapsed; if $D^2\ll W(\log X)^{-C}$, the quartic bucket-capacity energy is the
dominant ledger. Therefore the only genuinely delicate case is exactly the
polylog-dense two-core graph at the central scale.

This reframes the residual entropy problem:

$$
\boxed{
\text{persistent saturation}
\Longrightarrow
\text{polylog-dense two-core bucket-pair graph}.
}
$$

This is stronger than saying that the residual ambient has size
$N(\log X)^K$.

---

# 15. Rectangle-to-rank-one inverse target

A polylog-dense bipartite graph between the two bucket cores contains many
rectangles:

$$
(c_0,c_0';c_1,c_1')
\in
\mathcal C_0^2\times\mathcal C_1^2.
$$

Quantitatively, the standard convexity bound gives

$$
\#C_4(G_\Gamma)
\gg
\delta^4|\mathcal C_0|^2|\mathcal C_1|^2
$$

once the minimum side sizes dominate the inverse-density losses.

Each such rectangle corresponds to four labelled vertices, one for each bucket
pair:

$$
(c_0,c_1),\quad
(c_0,c_1'),\quad
(c_0',c_1),\quad
(c_0',c_1').
$$

This is precisely where the rank-one infrastructure can become relevant. But
the connection is not automatic. One still has to prove an arithmetic inverse
statement converting many low-energy bucket rectangles into either:

1. a nonzero rectangle-defect contribution that is charged to the energy
   ledger; or
2. a large subconfiguration with vanishing rectangle defect, hence additive
   rank one by the Lean-formalized rank-one rigidity theorem; or
3. a near-dominant / low-entropy structural exception, which exits the
   non-dominant substantial SBEE case.

The sharpened local target is therefore:

**Two-core rectangle inverse.**
Let $\mathcal C_0,\mathcal C_1$ be two disjoint saturated generated bucket cores
arising along one residual branch. If

$$
G_\Gamma(\mathcal C_0,\mathcal C_1)
$$

has density at least $(\log X)^{-A}$ and the divisor-energy ledger has not
already paid the residual entropy, then the bucket-pair residue map on a large
subrectangle has zero or negligible mixed second defect. Consequently the
configuration is rank-one / near-dominant, or belongs to a separately
low-entropy structural family.

This is now a more precise version of the polylog-ambient compression problem.
It uses exactly the finite tools Aristotle has already formalized:

- marked dual uniqueness / Fisher counting;
- high-multiplicity containers;
- repeated exposure budgets;
- common-neighbour and rectangle counting;
- rank-one rigidity from zero rectangle defect;
- tree telescoping for the final recursion.

What remains on the paper side is the arithmetic bridge from bucket rectangles
to the rectangle-defect dichotomy above.

---

# 16. Current assessment after the two-core refinement

The signs are still positive, but the bottleneck is sharper than before.

The incorrect optimistic statement was:

$$
Y\le N(\log X)^K
\quad\Rightarrow\quad
\text{effective }D\text{ is polylogarithmic}.
$$

The corrected statement is:

$$
Y\le N(\log X)^K
\quad\text{plus one generated core}\quad
\Rightarrow
\Delta_{\rm new}\ll M(\log X)^{O(1)}.
$$

If a second saturated core still exists, the residual set generates a
polylog-dense two-core graph. That density creates many bucket rectangles, and
the last real mathematical step is to prove that those rectangles cannot remain
low-energy and non-dominant unless they become rank-one structured.

So the remaining internal route is now:

$$
\text{first-capture saving}
\Longrightarrow
\text{one-core new-bucket capacity}
\Longrightarrow
\text{two-core density}
\Longrightarrow
\text{rectangle-to-rank-one inverse}
\Longrightarrow
\text{polylog-ambient compression}.
$$

The first three arrows are finite counting/bookkeeping and are good Aristotle
targets. The fourth arrow is the current paper-side mathematical heart.

---

# 17. Seed-generated strengthening

There is one more important guardrail.

The two-core graph

$$
G_\Gamma(\mathcal C_0,\mathcal C_1)
$$

should not be treated as an arbitrary dense graph between two arbitrary bucket
sets. Random-looking bucket sets of size about $M^2$ inside an interval of
length about $MX$ can already have polylogarithmic divisibility density. Such
random density alone need not force rank-one structure.

The actual saturated cores are better than arbitrary bucket sets:

$$
\mathcal C_i=N(F_i),
$$

where $F_i$ is a fingerprint of labelled vertices and $N(F_i)$ is the union of
their bucket neighbourhoods.

This seed-generated origin must remain part of the inverse statement.

If

$$
v\in A_h(N(F)),
$$

then $v$ is incident to at least $h$ buckets generated by $F$. Since two labelled
vertices share at most one bucket when $2\tau<X^2$, these $h$ bucket incidences
come from at least $h$ distinct fingerprint vertices. Thus

$$
v\in A_h(N(F))
\quad\Longrightarrow\quad
\#\{f\in F:v\sim_\tau f\}\ge h.
$$

So a residual vertex surviving two saturated exposures is not merely an edge in
a graph between bucket cores. It is a high common-neighbour of two seed
fingerprints:

$$
d_{F_0}(v)\ge h_0,
\qquad
d_{F_1}(v)\ge h_1.
$$

This recovers the high-common-neighbour language from the old draft, but now
with the ambient-sensitive entropy ledger and the two-core density bookkeeping
available.

The corrected inverse target is therefore:

**Two-fingerprint common-neighbour inverse.**
Let $F_0,F_1\subset\Gamma$ be saturated fingerprints of size $\asymp M$ along
one residual branch. If a residual set $\Gamma'$ of mass $\asymp W$ satisfies

$$
d_{F_0}(v),d_{F_1}(v)\gg \frac{M}{(\log X)^A}
\qquad (v\in\Gamma'),
$$

and the divisor-energy ledger has not already paid the entropy of $\Gamma'$,
then the cheap-edge equations between $\Gamma'$ and the two fingerprints force
one of the structural exits:

1. a near-dominant label fibre;
2. a rank-one / zero-rectangle-defect subconfiguration;
3. a low-entropy exceptional family;
4. or an energy contribution large enough to pay the residual entropy.

The cheap-edge equations have the form already isolated in the old draft:

$$
p\alpha-q\beta=p_0(t'-t).
$$

The missing arithmetic bridge is to show that a vertex cannot satisfy
polylogarithmically many such independent seed equations on two unrelated
fingerprints unless the resulting rectangle defects vanish on a large
substructure or the nonzero defects produce enough energy.

Thus Section 15 should be read with this seed-generated strengthening:

$$
\text{two-core rectangles}
\quad\text{are the counting shadow of}\quad
\text{two-fingerprint common-neighbour structure}.
$$

This distinction matters. The finite two-core bookkeeping is still useful and
formalizable, but the paper-side inverse theorem must remember the fingerprints,
not merely the bucket sets.
