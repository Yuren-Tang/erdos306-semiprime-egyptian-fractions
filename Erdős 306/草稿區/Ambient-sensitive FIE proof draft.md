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

---

# 18. Framework audit: seeded witness matrices

The right framework now seems to be a seeded inverse theorem, not a pair of
loose interfaces.

External tools suggest the following division of labour.

- Dependent random choice is the correct generic language for turning dense
  common-neighbour information into fixed small seed tuples with a large common
  neighbourhood; see Fox--Sudakov,
  [Dependent Random Choice](https://arxiv.org/abs/0909.3271).
- Hypergraph/container methods explain the fingerprint/container bookkeeping,
  but only after the relevant forbidden or costly configurations have been
  identified; see Saxton--Thomason,
  [Hypergraph containers](https://arxiv.org/abs/1204.6595).
- Sum-product/incidence inverse philosophy says that persistent bilinear
  incidence without expansion should force algebraic structure; see
  Bourgain--Katz--Tao,
  [A sum-product estimate in finite fields, and applications](https://arxiv.org/abs/math/0301343).

None of these is a black-box theorem that directly proves the present inverse.
But together they point to a clean framework:

$$
\boxed{
\text{seeded witness-matrix inverse}
}
$$

## 18.1 Two-sided DRC extraction

Suppose a residual set $\Gamma'$ satisfies

$$
d_{F_0}(v),d_{F_1}(v)\ge \eta M,
\qquad
\eta=(\log X)^{-A},
$$

for all $v\in\Gamma'$, with

$$
|F_0|,|F_1|\asymp M.
$$

Choose $r$ seeds independently from $F_0$ and $r$ seeds independently from
$F_1$, where $r$ is a fixed integer chosen after the logarithmic losses.

For each $v\in\Gamma'$, the probability that $v$ is cheap to every chosen seed
is at least

$$
\eta^{2r}.
$$

Therefore there exist fixed seed tuples

$$
S_0\in F_0^r,\qquad S_1\in F_1^r,
$$

with a common residual neighbourhood

$$
\Gamma(S_0,S_1)
=
\{v\in\Gamma':v\sim_\tau f\text{ for every seed }f
\text{ appearing in either tuple}\}
$$

satisfying

$$
|\Gamma(S_0,S_1)|
\ge
\eta^{2r}|\Gamma'|.
$$

Thus it is enough to prove a fixed-seed inverse theorem, losing only a fixed
power of $\log X$.

This is the useful DRC input. It is generic and finite.

## 18.2 The witness matrix

For a residual vertex

$$
v=(p,t)
$$

and a seed

$$
f=(q,u),
$$

write the unique cheap bucket witness as

$$
n_{v,f}.
$$

Uniqueness holds in the range $2\tau<X^2$: two labelled vertices cannot share
two distinct buckets.

The witness satisfies

$$
n_{v,f}=m_t+p\alpha_{v,f}=m_u+q\beta_{v,f},
$$

with

$$
|\alpha_{v,f}|,|\beta_{v,f}|
\ll
M_\tau:=1+\frac{\tau}{X}.
$$

Equivalently,

$$
p\alpha_{v,f}-q\beta_{v,f}=p_0(u-t).
$$

For fixed seed tuples $S=S_0\cup S_1$, the data

$$
\mathcal N=(n_{v,f})_{v\in\Gamma(S),\,f\in S}
$$

is a rectangular integer matrix with small entries and strong congruence
constraints.

The natural mixed defect is

$$
\Delta(v,v';f,f')
=
n_{v,f}-n_{v,f'}-n_{v',f}+n_{v',f'}.
$$

If all such defects vanish on a large subrectangle, then the matrix has additive
rank one:

$$
n_{v,f}=a_v+b_f.
$$

This is exactly the rank-one rigidity already formalized by Aristotle.

## 18.3 The missing inverse theorem

The current mathematical heart can now be stated more concretely.

**Seeded witness-matrix inverse.**
Let $S$ be a fixed seed tuple of bounded size and let $\Gamma_S$ be a large
residual set such that every $v\in\Gamma_S$ is cheap to every $f\in S$. If the
divisor-energy ledger has not already paid the entropy of $\Gamma_S$, then one
of the following holds:

1. many mixed defects
   $$
   \Delta(v,v';f,f')
   $$
   are nonzero and can be charged to the cross-energy ledger;
2. after discarding an energy-paid exceptional set, the witness matrix has
   vanishing mixed defect on a large subrectangle, hence additive rank one;
3. the rank-one alternative forces near-dominance or a low-entropy structural
   family.

The crucial paper-side lemma is item 1:

$$
\boxed{
\text{nonzero witness-matrix defects produce energy}
}
$$

This is where the arithmetic of

$$
p\alpha-q\beta=p_0(u-t)
$$

must be used. The finite tools can organize defects and rectangles, but they do
not by themselves identify the energy charge.

## 18.4 Why this is better than the previous target

The previous phrase "two-core rectangle inverse" was close but slightly too
coarse. It could be misread as a theorem about arbitrary dense bipartite graphs
between bucket sets.

The seeded witness-matrix version preserves all relevant structure:

- the cores are generated by fingerprints;
- common-neighbour density is converted to fixed seed tuples by DRC;
- every edge has a unique short bucket witness;
- rectangles become mixed defects of a concrete integer matrix;
- zero defect is exactly the rank-one structure already formalized;
- nonzero defect is the precise place where the remaining energy charge must be
  proved.

This is probably the framework that was missing.

---

# 19. Row-difference reduction: large prime gcd in a seed progression

The seeded witness matrix has an even more concrete arithmetic form.

Fix one seed

$$
f_\ast=(q_\ast,u_\ast)\in S
$$

as a reference. For every other seed

$$
f=(q,u)\in S\setminus\{f_\ast\}
$$

and residual vertex

$$
v=(p,t)\in\Gamma(S),
$$

define the row difference

$$
D_v(f)=n_{v,f}-n_{v,f_\ast}.
$$

Since both witnesses are congruent to $m_t$ modulo $p$, we have

$$
p\mid D_v(f).
$$

Also

$$
D_v(f)
=
p(\alpha_{v,f}-\alpha_{v,f_\ast}),
$$

so

$$
|D_v(f)|\ll X M_\tau\ll \tau+X.
$$

Using the seed congruences, the same difference is

$$
D_v(f)
=
p_0(u-u_\ast)+q\beta_{v,f}-q_\ast\beta_{v,f_\ast},
$$

with

$$
|\beta_{v,f}|,|\beta_{v,f_\ast}|\ll M_\tau.
$$

Thus the vector

$$
\mathbf D_v
=
\bigl(D_v(f)\bigr)_{f\in S\setminus\{f_\ast\}}
$$

lies in the short seed-generated progression

$$
\mathcal P_S
=
\left\{
\bigl(p_0(u_f-u_\ast)+q_f b_f-q_\ast b_\ast\bigr)_{f\ne f_\ast}
:
|b_\ast|,|b_f|\ll M_\tau
\right\}.
$$

At the same time, every coordinate of $\mathbf D_v$ is divisible by the same
large prime $p\sim X$.

So the fixed-seed inverse can be rephrased as:

$$
\boxed{
\text{count vectors in }\mathcal P_S
\text{ with a common prime divisor }p\sim X.
}
$$

This is sharper than the matrix-defect language.

## 19.1 Easy exits

There are two immediate structural exits.

First, if

$$
D_v(f)=0
$$

for many seeds $f$, then $v$ shares the same bucket with many seed vertices.
This is a low-entropy bucket-star configuration and should be paid by the
new-bucket capacity / seed-neighbour budget.

Second, if for two residual vertices $v,v'$ we have

$$
\mathbf D_v=\mathbf D_{v'},
$$

then every nonzero coordinate is divisible by both $p_v$ and $p_{v'}$. In the
range

$$
|D_v(f)|<X^2
$$

this forces the shared nonzero coordinates to vanish unless $p_v=p_{v'}$.
Therefore the row-difference vector is essentially injective on residual primes
outside the zero-star exception.

Thus entropy can only remain high if the seed progression $\mathcal P_S$
contains many distinct vectors with a large common prime divisor.

## 19.2 Candidate arithmetic lemma

The missing arithmetic statement can now be formulated as follows.

**Large-prime gcd in a seed progression.**
Let $S$ be a bounded seed tuple with primes $q_f\sim X$ and labels $u_f$. Let
$\mathcal P_S$ be the progression above with parameter size $M_\tau$. Then the
number of pairs

$$
(p,\mathbf D),
\qquad
p\sim X,\quad \mathbf D\in\mathcal P_S,\quad p\mid D_f\ \forall f,
$$

is small enough to pay the residual entropy, unless the seed data

$$
(q_f,u_f)_{f\in S}
$$

satisfy a rank-one / low-entropy relation.

For a random seed tuple, one expects a saving roughly

$$
X^{-(|S|-1)}
$$

from the common divisibility constraints after the first coordinate. Taking
$|S|$ large but fixed should beat any fixed polylogarithmic loss.

If this random heuristic fails for many seed tuples, the failure should mean
that the affine forms

$$
p_0(u_f-u_\ast)+q_f b_f-q_\ast b_\ast
$$

have an unexpected common large-prime divisor pattern. That is precisely the
kind of inverse phenomenon where the sum-product/incidence philosophy should
force algebraic structure.

## 19.3 Relation to mixed defects

For two residual vertices,

$$
\Delta(v,v';f,f_\ast)
=
D_v(f)-D_{v'}(f).
$$

Thus the mixed-defect problem is equivalent to understanding collisions and
differences among the row-difference vectors $\mathbf D_v$.

- Many zero defects mean many repeated row-difference coordinates; by the
  injectivity observation, this forces zero-star or rank-one structure.
- Many nonzero defects mean the row-difference vectors are spread through
  $\mathcal P_S$; then the large-prime gcd counting lemma should give the
  entropy saving directly.

So the active bottleneck is now:

$$
\boxed{
\text{large-prime gcd bound for bounded seed progressions}
}
$$

This is a concrete arithmetic-combinatorial lemma. It may be the right place to
try a fresh proof rather than add more container bookkeeping.

---

# 20. After Aristotle TwoCoreBookkeeping: lattice-sieve shape of the last step

The Aristotle run proving `TwoCoreBookkeeping.lean` changes the risk profile.

The following finite implications are now safe to treat as formalized:

1. one generated core gives the new-bucket capacity bound;
2. two saturated cores give a dense two-core bucket-pair graph;
3. high degree into a generated core gives many seed neighbours.

In particular, the combinatorial path

$$
\text{persistent saturation}
\Longrightarrow
\text{many seed common-neighbours}
\Longrightarrow
\text{seeded witness matrix}
$$

is no longer the main uncertainty.

The remaining uncertainty is the arithmetic counting of row-difference vectors.

## 20.1 Lattice formulation

Fix a seed tuple

$$
S=\{f_\ast,f_1,\ldots,f_k\},
\qquad
f_i=(q_i,u_i),
$$

and put

$$
A_i=p_0(u_i-u_\ast).
$$

Let $I=[-M_\tau,M_\tau]\cap\mathbb Z$. A residual prime $p\sim X$ contributes
to the fixed-seed common neighbourhood only if there exists

$$
\mathbf b=(b_\ast,b_1,\ldots,b_k)\in I^{k+1}
$$

such that

$$
q_i b_i-q_\ast b_\ast + A_i\equiv0\pmod p
\qquad (1\le i\le k).
$$

For each $p$, define the affine lattice slice

$$
\Lambda_p(S)
=
\left\{
\mathbf b\in\mathbb Z^{k+1}:
q_i b_i-q_\ast b_\ast + A_i\equiv0\pmod p
\quad(1\le i\le k)
\right\}.
$$

Then the desired fixed-seed count is bounded by

$$
\sum_{p\sim X}
\#\bigl(\Lambda_p(S)\cap I^{k+1}\bigr),
$$

up to the already recorded zero-star and rank-one exceptions.

The congruences have codimension $k$, so the expected determinant is $p^k$.
A first-pass lattice heuristic would give

$$
\#\bigl(\Lambda_p(S)\cap I^{k+1}\bigr)
\ll
\frac{M_\tau^{k+1}}{p^k}
+O(1),
$$

or a dyadic-logarithmic variant. If $M_\tau\asymp X^{1/2}$ and $k\ge2$, the
main term summed over $p\sim X$ is far below $N$:

$$
\sum_{p\sim X}
\frac{M_\tau^{k+1}}{p^k}
\ll
\frac{X}{\log X}\cdot \frac{X^{(k+1)/2}}{X^k}
=
\frac{X^{(3-k)/2}}{\log X}.
$$

Thus already $k=2$ gives only $O(X^{1/2}/\log X)$ regular solutions, which is
much smaller than the polylogarithmic residual mass left after the DRC
extraction.

Section 21 below improves the regular side further: for the actual entropy
problem, it is enough to prove uniqueness per residual prime outside the
short-kernel singular set.

## 20.2 The short-kernel obstruction

The only reason the lattice estimate can fail is that the homogeneous kernel

$$
q_i x_i-q_\ast x_\ast\equiv0\pmod p
\qquad (1\le i\le k)
$$

has an unexpectedly short nonzero vector

$$
\mathbf x=(x_\ast,x_1,\ldots,x_k),
\qquad
\|\mathbf x\|_\infty\ll M_\tau.
$$

Equivalently, $p$ is a common large prime divisor of

$$
q_i x_i-q_\ast x_\ast
\qquad (1\le i\le k).
$$

This is the homogeneous version of the same large-prime gcd problem.

Therefore the last step should be stated as a dichotomy:

**Seed lattice sieve dichotomy.**
For a bounded seed tuple $S$ with $k\ge2$, either

1. for most residual primes $p$, the affine slice $\Lambda_p(S)$ has the
   regular determinant-size count;
2. or many $p$ admit a short homogeneous kernel vector, in which case the seed
   tuple satisfies a low-entropy rational relation and is charged as a
   structured exception.

This is exactly the kind of framework the earlier "two-core rectangle inverse"
was missing.

## 20.3 What remains to prove on paper

The regular case is a geometry-of-numbers / larger-sieve estimate for the
affine slices $\Lambda_p(S)$.

The singular case must be shown to be low entropy. Concretely, short kernel
vectors satisfy

$$
q_i x_i-q_\ast x_\ast=p\,y_i,
\qquad
|x_i|,|x_\ast|,|y_i|\ll M_\tau.
$$

For fixed short data $(x_\ast,x_i,y_i)$, the seed primes obey

$$
q_i x_i-q_\ast x_\ast=p\,y_i.
$$

If this happens for several independent seeds $i$, the primes $q_i$ lie in a
bounded-complexity rational family controlled by $(q_\ast,p)$ and short
coefficients. The expected entropy is far below free fingerprint entropy unless
the family is rank-one / near-dominant.

Thus the paper proof should now target:

$$
\boxed{
\text{regular affine-lattice count}
\quad+\quad
\text{short-kernel structured entropy bound}.
}
$$

This is more concrete than the previous witness-matrix formulation and seems
like the next place to try an actual proof.

---

# 21. Regular case is uniqueness per residual prime

There is a simpler way to state the regular side of the lattice sieve.

Fix $S$ and $p$. Suppose two parameter vectors

$$
\mathbf b,\mathbf b'\in I^{k+1}
$$

both lie in the same affine slice $\Lambda_p(S)$. Then their difference

$$
\mathbf x=\mathbf b-\mathbf b'
$$

satisfies the homogeneous congruences

$$
q_i x_i-q_\ast x_\ast\equiv0\pmod p
\qquad(1\le i\le k),
$$

and

$$
\|\mathbf x\|_\infty\le 2M_\tau.
$$

Therefore:

**Regular uniqueness lemma.**
If the homogeneous kernel has no nonzero vector with

$$
\|\mathbf x\|_\infty\le 2M_\tau,
$$

then

$$
\#(\Lambda_p(S)\cap I^{k+1})\le1.
$$

This is stronger and cleaner than the determinant-count phrasing. In the
transversal setting, one candidate vector for a fixed residual prime $p$ means
one candidate witness pattern and hence at most one candidate label $t$, up to
the already separated tiny exceptions. Thus the polylogarithmic label
multiplicity is removed in the regular case.

So the real problem is exactly the singular case:

$$
\exists\,\mathbf x\ne0,\qquad
\|\mathbf x\|_\infty\le 2M_\tau,\qquad
q_i x_i-q_\ast x_\ast\equiv0\pmod p
\quad(1\le i\le k).
$$

## 21.1 Anatomy of a singular prime

Since $M_\tau<X$ in the central range, a short kernel vector cannot have
$x_\ast=0$ unless it is zero. Indeed, if $x_\ast=0$, then

$$
p\mid q_i x_i.
$$

For $p\ne q_i$ and $|x_i|<p$, this forces $x_i=0$ for every $i$.

Thus a singular vector has $x_\ast\ne0$. Writing the congruence as an integer
identity gives

$$
q_i x_i-q_\ast x_\ast=p\,y_i,
\qquad
|y_i|\ll M_\tau.
$$

Equivalently,

$$
q_i
=
\frac{q_\ast x_\ast+p\,y_i}{x_i}.
$$

So, once $q_\ast$, $p$, and the short coefficients $(x_\ast,x_i,y_i)$ are fixed,
the seed prime $q_i$ is determined.

This is the promised low-entropy shape. A seed tuple admitting many singular
residual primes must lie in a bounded-complexity rational family controlled by
short coefficients. The remaining task is to show that this family is either:

1. small enough to pay as a structured seed exception; or
2. coherent enough to imply the rank-one / near-dominant alternative.

## 21.2 Revised final local lemma

The polylog-compression bottleneck can now be stated as:

**Seed singularity lemma.**
Let $S=\{f_\ast,f_1,\ldots,f_k\}$ be a bounded seed tuple with $k\ge2$ and
$M_\tau<X^{1-o(1)}$. Assume moreover that $k$ is chosen so that

$$
M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}.
$$

For all but a low-entropy family of seed tuples and residual primes $p\sim X$,
the homogeneous kernel

$$
q_i x_i-q_\ast x_\ast\equiv0\pmod p
$$

has no nonzero vector with $\|\mathbf x\|_\infty\le2M_\tau$.

Consequently the affine slice for each regular $p$ has at most one point, so
the residual ambient has $O(1)$ label multiplicity per prime. The singular seed
tuples are charged to the structured exception ledger.

This is the arithmetic core of the remaining local statement. It is no longer a
general container lemma; it is a short-coefficient rational parametrization
problem for prime tuples, followed by the selection/covering step in Sections
22--23.

The condition on $k$ is not cosmetic. For $k=1$, Dirichlet approximation can
often produce a nonzero short solution to

$$
q_1x_1\equiv q_\ast x_\ast\pmod p
$$

when $M_\tau\asymp X^{1/2}$. Thus one non-reference seed is not enough. The
two-sided DRC extraction should choose enough seed vertices that the family of
seed tuples admitting simultaneous short kernels has lower entropy than the
free seed-tuple family.

In the central case $M_\tau\asymp X^{1/2}$, the displayed condition is

$$
X^{(k+1)/2}\ll X^{k-1}(\log X)^{-C},
$$

so one needs

$$
k>3.
$$

Thus four non-reference seeds are enough at the central scale, up to fixed
logarithmic slack.

## 21.3 Direct entropy count for singular seed tuples

Here is the promised entropy count.

Ignore the labels $u_i$ for the moment; for a bounded seed tuple they contribute
only fixed powers of the current polylog ambient. Count the prime parts

$$
(q_\ast,q_1,\ldots,q_k).
$$

For a singular tuple there are

$$
p\sim X,\qquad q_\ast\sim X,\qquad 0<|x_\ast|\le 2M_\tau
$$

and, for each $i$,

$$
0<|x_i|\le2M_\tau,\qquad |y_i|\ll M_\tau,
$$

such that

$$
q_i x_i-q_\ast x_\ast=p\,y_i.
$$

For fixed

$$
p,\ q_\ast,\ x_\ast,\ x_i,\ y_i,
$$

the prime $q_i$ is determined:

$$
q_i=\frac{q_\ast x_\ast+p\,y_i}{x_i}.
$$

Therefore, for fixed $(p,q_\ast,x_\ast)$, there are at most

$$
O(M_\tau^2)^k
$$

raw coefficient choices, and hence at most that many seed prime tuples. This is
too crude by one power of $M_\tau$ per seed. A sharper count uses the congruence
form: for fixed $(p,q_\ast,x_\ast)$ and fixed $x_i$, the prime $q_i$ must lie in
one residue class modulo $p$:

$$
q_i\equiv q_\ast x_\ast x_i^{-1}\pmod p.
$$

Since $q_i\in[X,2X]$ and $p\sim X$, each residue class contributes $O(1)$
possible integers, hence $O(1)$ possible primes. Thus each seed coordinate has
only

$$
O(M_\tau)
$$

choices, not $O(M_\tau^2)$.

The number of singular prime seed tuples, averaged over seed tuples and residual
primes, is therefore bounded by

$$
\ll
N^2 M_\tau^{k+1}(\log X)^{O(1)},
$$

where $N\asymp X/\log X$ accounts for $p$ and $q_\ast$, and $M_\tau$ accounts for
$x_\ast$.

By contrast, a free seed prime tuple has entropy

$$
\asymp N^{k+1}.
$$

Thus singular seed tuples save a factor

$$
\frac{N^{k+1}}{N^2M_\tau^{k+1}}
\asymp
\frac{X^{k-1}}{M_\tau^{k+1}}(\log X)^{-O(1)}.
$$

This is a genuine logarithmic or power saving precisely under

$$
M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}.
$$

This proves that singular seed tuples are sparse on average in the full prime
universe. It does **not** by itself finish the fixed-configuration argument,
because the DRC seed tuple is chosen from a fingerprint pool $F$. It remains
possible, a priori, that a special fingerprint pool contains mostly singular
tuples.

Thus the seed singularity lemma is reduced to a selection/structure statement:

1. either the available fingerprint pool contains at least one seed tuple that
   is regular for all but a negligible set of residual primes;
2. or the pool is concentrated inside the sparse singular-tuple hypergraph and
   is therefore a low-entropy / rank-one structured exception.

The prime-coordinate count above supplies the global sparsity input for this
selection lemma. The remaining issues are:

1. the diagonal exceptions $p=q_\ast$ or $p=q_i$, which are $O(1)$ per seed tuple
   and should be absorbed by the already finite seed/fingerprint ledger;
2. zero-star cases $D_v(f)=0$, already marked as seed-neighbour capacity
   exceptions;
3. polylog label choices for the bounded seed tuple;
4. checking that the DRC seed tuple is sampled from the residual fingerprint
   pool in a way compatible with charging a low-entropy seed family.

The fourth point is the only remaining combinatorial issue. It is much smaller
than the original FIE problem: it is a bounded-uniformity hypergraph selection
problem on the fingerprint pool, with the singular tuples already globally
sparse.

---

# 22. Selection form of the remaining singular case

The current endpoint is therefore the following statement.

**Good-seed selection lemma.**
Let $F$ be a fingerprint pool of size $\asymp M$ and let $\mathcal H_{\rm sing}$
be the $k$-uniform hypergraph of seed tuples that admit many singular residual
primes. Suppose the global singular-tuple count satisfies

$$
|\mathcal H_{\rm sing}|
\ll
N^2M_\tau^{k+1}(\log X)^{O(1)}.
$$

Then either:

1. $F^k$ contains a tuple outside $\mathcal H_{\rm sing}$, giving a good seed
   tuple and hence regular uniqueness per residual prime; or
2. $F$ is contained in a low-entropy container generated by the sparse hypergraph
   $\mathcal H_{\rm sing}$.

The second alternative should correspond to the structured exception already
allowed in the SBEE ledger.

At this point the proof route is:

$$
\text{HA finite incidence}
\Longrightarrow
\text{two-sided DRC}
\Longrightarrow
\text{seeded witness matrix}
\Longrightarrow
\text{singular tuple sparsity}
\Longrightarrow
\text{good-seed selection or structured exception}.
$$

The first three arrows are now formalized or formalization-ready. The fourth is
the direct arithmetic count above. The fifth is the remaining local
combinatorial packaging step.

---

# 23. Singular hypergraph as reciprocal-progression clusters

The sparse hypergraph $\mathcal H_{\rm sing}$ has additional structure.

Fix the reference seed

$$
f_\ast=(q_\ast,u_\ast)
$$

and a residual prime $p\sim X$. For a nonzero short reference coefficient

$$
0<|x_\ast|\le 2M_\tau,
$$

define the reciprocal cluster

$$
\mathcal A(p,q_\ast,x_\ast)
=
\left\{
q\in[X,2X]\cap\mathbb P:
\exists\,0<|x|\le2M_\tau,\quad
q x\equiv q_\ast x_\ast\pmod p
\right\}.
$$

Equivalently,

$$
q\equiv q_\ast x_\ast x^{-1}\pmod p
$$

for some short $x$. Since $p\sim X$ and $q\in[X,2X]$, each short $x$ gives
$O(1)$ possible primes $q$. Hence

$$
|\mathcal A(p,q_\ast,x_\ast)|
\ll M_\tau.
$$

A non-reference seed tuple $(q_1,\ldots,q_k)$ is singular for this
$(p,q_\ast,x_\ast)$ only if

$$
q_i\in\mathcal A(p,q_\ast,x_\ast)
\qquad(1\le i\le k).
$$

Thus the singular hypergraph is contained in a union of complete $k$-uniform
hypergraphs on reciprocal clusters:

$$
\mathcal H_{\rm sing}(q_\ast)
\subset
\bigcup_{p,x_\ast}
\mathcal A(p,q_\ast,x_\ast)^k.
$$

This is stronger than mere global sparsity.

The remaining selection problem becomes:

**Reciprocal-cluster selection lemma.**
Let $F$ be the available seed pool. Either:

1. there is a $k$-tuple in $F^k$ not contained in any cluster
   $\mathcal A(p,q_\ast,x_\ast)$, giving a good seed tuple; or
2. $F$ is efficiently covered by a small number of reciprocal clusters, in which
   case $F$ has low entropy / arithmetic structure.

The second alternative is plausible because each cluster is parametrized by
only

$$
(p,x_\ast)
$$

and then each element of the cluster is parametrized by a short $x$. Encoding a
fingerprint inside one cluster costs roughly

$$
|F|\log M_\tau
$$

instead of

$$
|F|\log N.
$$

At the central scale $M_\tau\asymp N^{1/2}$, this gives a saving

$$
\frac12 |F|\log N
$$

before logarithmic losses, enough for the bounded seed-selection step.

The only way this cluster-cover argument could fail is if many reciprocal
clusters have large mutual intersections and together cover a large unstructured
pool. Such large intersections should themselves impose equations

$$
q_\ast x_\ast x^{-1}
\equiv
q_\ast x_\ast' (x')^{-1}
\pmod p
$$

or the analogous equation for two different residual primes. These are again
short-coefficient rational relations, hence part of the same structured
exception ledger.

This is now a very concrete final local problem:

$$
\boxed{
\text{container/covering for reciprocal clusters}
}
$$

It is finite and arithmetic, but no longer Fourier-analytic.
