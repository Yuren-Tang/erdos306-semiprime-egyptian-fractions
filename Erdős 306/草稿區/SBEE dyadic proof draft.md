# SBEE dyadic proof draft

This is the scratch area for the only remaining condition: [[CP 02 The single remaining condition|SBEE]].

Back to [[CP 00 Navigation]].

---

# 1. Target

We need to prove that in one prime block
\[
P\subset[X,2X],\qquad N=|P|\asymp X/\log X,
\]
the non-dominant substantial-label case contributes only
\[
\ll_\varepsilon e^{\varepsilon R}
\]
to the level set
\[
Q_P(a)\le R.
\]

The existing ingredients are:

- base-list reduction;
- Irving-good majority correction;
- [[Cross-label divisor-energy lemma]];
- tiny classes as exceptions.

The missing bookkeeping is to show that substantial multi-label entropy is paid by substantial cross-label energy.

---

# 2. Notation

Let the short list be
\[
\mathcal L,\qquad s=|\mathcal L|\ll 1+\log X\sqrt R.
\]
Covered vertices split into classes
\[
C_m=\{p:a_p\equiv m\pmod p\},\qquad m\in\mathcal L.
\]
Fix \(\rho>0\). We are in the case:
\[
\max_m |C_m|<(1-\rho)N.
\]
Let
\[
L_X=1+\frac{\log(B+X^2+2)}{\log X}.
\]
Substantial classes satisfy
\[
|C_m|\ge C_0L_X.
\]

For substantial labels \(m\ne m'\), define
\[
E_{m,m'}
=
\sum_{p\in C_m,q\in C_{m'}}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2.
\]
The divisor-energy lemma gives
\[
E_{m,m'}
\gg
M_{m,m'}
\min\left(1,\frac{M_{m,m'}^2}{X^4L_X^4}\right),
\qquad
M_{m,m'}=|C_m||C_{m'}|.
\]

---

# 3. Dyadic profile

Dyadically partition substantial class sizes:
\[
\mathcal C_j=\{m:2^j\le |C_m|<2^{j+1}\}.
\]
Here
\[
C_0L_X\le 2^j\le N.
\]
Let
\[
r_j=|\mathcal C_j|,
\qquad
V_j=\sum_{m\in\mathcal C_j}|C_m|\asymp r_j2^j.
\]
The substantial mass condition is
\[
\sum_j V_j\ge \rho N.
\]
No dominance gives
\[
\max_j 2^j\le (1-\rho)N
\]
unless one class is dominant and we are out of this case.

For two dyadic levels \(i,j\), the total number of cross ordered pairs is
\[
\asymp r_ir_j2^{i+j}
\]
when \(i\ne j\), and
\[
\asymp r_j^2 2^{2j}
\]
inside one level after excluding equal labels.

---

# 4. Energy lower bound by dyadic levels

For a pair of classes of sizes \(u,v\), put
\[
\Phi(u,v)
=
uv\min\left(1,\frac{u^2v^2}{X^4L_X^4}\right).
\]
Then the cross-label energy in a dyadic pair of levels should satisfy
\[
S_{i,j}
\gg
r_ir_j\Phi(2^i,2^j)
\]
for \(i\ne j\), and
\[
S_{j,j}
\gg
r_j(r_j-1)\Phi(2^j,2^j).
\]

First useful reduction:

Since
\[
\sum_j V_j\ge \rho N
\]
and there is no dominant class, one should be able to find dyadic levels \(i,j\) such that cross mass between them is
\[
\gg_\rho \frac{N^2}{(\log N)^2}
\]
after losing at most logarithmic factors. This is enough if the energy per pair dominates the entropy loss of choosing the profile.

Need make this exact:

1. prove
   \[
   \sum_{\substack{i,j\\{\rm substantial}}}
   r_ir_j2^{i+j}
   \gg_\rho N^2;
   \]
2. split into the range \(2^{i+j}\ge X^2L_X^2\) and its complement;
3. in the large-pair range, \(\Phi(2^i,2^j)\asymp2^{i+j}\);
4. in the small-pair range,
   \[
   \Phi(2^i,2^j)
   =
   \frac{2^{3i+3j}}{X^4L_X^4}.
   \]

The danger zone is the small-pair range with many medium-small classes. This is where entropy comparison must be sharp.

---

# 5. Entropy budget

For a fixed dyadic profile \((r_j)\), rough vertex partition entropy is bounded by
\[
\exp\left(
\sum_j V_j\log\frac{N}{2^j}
+O\left(\sum_j r_j\log s\right)
\right).
\]
Label choice contributes at most
\[
\exp\left(O\left(\sum_j r_j\log s\right)\right).
\]
Residue choice inside a labelled substantial class is already fixed by \(a_p\equiv m\pmod p\), so there is no extra \(X^{|C_m|}\) factor for covered substantial vertices.

Tiny vertices and uncovered vertices are moved to the exception ledger. Each such vertex costs \(\gg N\) by majority Irving once a positive-density majority/substantial reference class is present, while its entropy is \(O(\log X+\log s)\).

Thus the substantial entropy to pay is essentially
\[
H_{\rm sub}
\lesssim
\sum_j V_j\log\frac{N}{2^j}
+\sum_j r_j\log s.
\]

Target inequality:
\[
H_{\rm sub}
\le
\varepsilon S_{\rm sub}
+O_\varepsilon(R)
\]
for every non-dominant substantial profile compatible with \(Q_P(a)\le R\).

---

# 6. Possible route through a profile inequality

It may be enough to prove the deterministic inequality:

For all class sizes \(n_1,\dots,n_t\ge C_0L_X\) with
\[
\sum_\alpha n_\alpha\ge \rho N,
\qquad
\max_\alpha n_\alpha\le (1-\rho)N,
\]
one has
\[
\sum_{\alpha\ne\beta}
n_\alpha n_\beta
\min\left(1,\frac{n_\alpha^2n_\beta^2}{X^4L_X^4}\right)
\gg_\rho
\sum_\alpha n_\alpha\log\frac{N}{n_\alpha}
\]
unless the left-hand side is already \(\gg R/\varepsilon\), in which case the contribution is killed by \(e^{-cR}\).

This exact inequality is probably false at the very bottom scale \(n_\alpha\asymp L_X\) without using the exception alternative. Therefore split:

1. If classes with \(n_\alpha\ge X^{1/2}L_X\) carry positive mass, the cubic energy term should dominate entropy easily.
2. If almost all substantial classes have \(n_\alpha<X^{1/2}L_X\), then there must be many classes. Treat these vertices as exceptions against a largest class if one exists; if no positive-density largest class exists, the cross mass among many classes should still be large enough after summing all pairs.

This split needs to be made clean and mutually exhaustive.

---

# 7. Clean case split to try

Let \(G\) be the largest class.

## Case 1: \(|G|\ge c_\rho N\)

If \(G\) is not dominant, then the complement has size \(\ge c'_\rho N\). Every vertex outside \(G\) not carrying the label of \(G\) is an exception relative to \(G\). Irving-good majority correction gives cost
\[
\gg |G|\gg N
\]
per such vertex. This should pay all entropy. This case may avoid divisor-energy entirely.

## Case 2: \(|G|< c_\rho N\)

No large class exists. Then the number of substantial classes is large, and
\[
\sum_{\alpha\ne\beta}n_\alpha n_\beta
\gg_\rho N^2.
\]
Use divisor-energy over all substantial pairs.

Need show:

\[
\sum_{\alpha\ne\beta}
n_\alpha n_\beta
\min\left(1,\frac{n_\alpha^2n_\beta^2}{X^4L_X^4}\right)
\]
dominates the entropy of partitioning \(N\) vertices into classes of sizes \(n_\alpha\).

This is the main remaining numerical inequality.

---

# 8. Immediate checks

Since
\[
N\asymp X/\log X,
\]
the largest possible entropy is \(O(N\log s)\) if all labels are tiny/medium.

For balanced classes of size \(u\), number \(t\asymp N/u\):

Energy lower bound is roughly
\[
t^2 u^2\min\left(1,\frac{u^4}{X^4L_X^4}\right)
=
N^2\min\left(1,\frac{u^4}{X^4L_X^4}\right).
\]
Entropy is roughly
\[
N\log(N/u).
\]

Thus energy dominates entropy once
\[
N\min\left(1,\frac{u^4}{X^4L_X^4}\right)
\gg
\log(N/u).
\]
For \(u\) very small this fails, so those vertices must be handled by exception payment rather than by divisor-energy alone.

This confirms that the final proof should not try to make divisor-energy pay all substantial classes down to \(C_0L_X\). It should first identify a genuinely substantial threshold, perhaps
\[
u\ge X^{3/4+\eta}
\]
or another optimized scale, and send lower classes into the exception mechanism whenever a positive-density reference class exists.

---

# 9. Next concrete task

Find the correct threshold \(U_0\) such that:

1. classes below \(U_0\) can be safely treated as exceptions, or their total mass forces many-pair energy;
2. classes above \(U_0\) are paid by divisor-energy;
3. the resulting case split is exhaustive.

Candidate thresholds to test:

\[
U_0=X^{1/2}L_X,\qquad
U_0=X^{2/3}L_X,\qquad
U_0=X^{3/4}L_X.
\]

The balanced-class calculation in Section 8 should decide which one gives the cleanest proof.

---

# 10. Audit: pairwise energy alone is not enough

The first serious check shows that the naive inequality

$$
\sum_{\alpha\ne\beta}
n_\alpha n_\beta
\min\left(1,\frac{n_\alpha^2n_\beta^2}{X^4L_X^4}\right)
\gg
\sum_\alpha n_\alpha\log\frac{N}{n_\alpha}
$$

cannot be the whole proof at the bottom and middle class scales.

Consider the balanced profile

$$
t\asymp N/u,\qquad n_\alpha\asymp u.
$$

The available pointwise divisor-energy lower bound gives only

$$
S_{\rm div}(u)
\asymp
N^2\min\left(1,\frac{u^4}{X^4L_X^4}\right).
$$

The corresponding partition entropy is roughly

$$
H(u)\asymp N\log(N/u).
$$

Since $N\asymp X/\log X$, divisor-energy alone dominates entropy only once

$$
u^4 \gtrsim X^3(\log X)L_X^4\log(N/u),
$$

so morally

$$
u\gtrsim X^{3/4}\cdot \text{logs}.
$$

Therefore the current cross-label divisor-energy lemma is strong enough for genuinely large classes, but not for all classes merely satisfying

$$
u\ge C_0L_X.
$$

This means SBEE should be attacked as a **counting/container statement**, not as a direct deterministic profile inequality.

The missing extra information is not visible in the crude lower bound. For small or medium classes, low total energy forces the selected pairs

$$
(p,q)\in C_m\times C_{m'}
$$

to lie in a sparse weighted incidence structure where

$$
|H_{pq}^{m,m'}|
$$

is unusually small. The divisor bound controls the number of such low-weight edges, but to pay entropy we must count vertex-labelled configurations with small weighted edge boundary. This is closer to a weighted graph container or Peierls counting problem inside one block.

---

# 11. Better formulation of the SBEE attack

For fixed short label list $\mathcal L$, form the labelled vertex set

$$
\Omega=P\times\mathcal L.
$$

For two distinct labels $m\ne m'$, define a weighted bipartite graph between $P\times\{m\}$ and $P\times\{m'\}$ by

$$
w_{m,m'}(p,q)
=
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2.
$$

A labelled assignment corresponds to choosing exactly one label above each prime:

$$
\Gamma=\{(p,m(p)):p\in P\}\subset\Omega.
$$

The substantial non-dominant part has no label fibre of size $(1-\rho)N$ and has many occupied fibres. Its cross energy is

$$
S_{\rm sub}(\Gamma)
=
\sum_{\substack{p\ne q\\m(p)\ne m(q)}}
w_{m(p),m(q)}(p,q),
$$

up to tiny/exception bookkeeping.

So the desired SBEE can be recast as:

> Count transversals $\Gamma\subset P\times\mathcal L$ with no dominant fibre and small weighted cross energy.

The cross-label divisor-energy lemma gives a weighted supersaturation statement for every pair of occupied fibres:

$$
\sum_{p\in A,q\in B}w_{m,m'}(p,q)
\gg
|A||B|
\min\left(1,\frac{|A|^2|B|^2}{X^4L_X^4}\right).
$$

But a container proof should also use the stronger distributional statement:

$$
\#\{(p,q)\in A\times B:w_{m,m'}(p,q)\le \tau^2/X^4\}
\ll
\tau L_X^2+(|A|+|B|)L_X.
$$

This controls not only the average energy but the number of low-cost incidences available to an adversarial partition.

---

# 12. Possible container route

For a threshold $\tau$, call a cross-label edge cheap if

$$
|H_{pq}^{m,m'}|\le \tau.
$$

The divisor bound gives

$$
e_{\rm cheap}(A,B)
\ll
\tau L_X^2+(|A|+|B|)L_X.
$$

If $A,B$ are both medium sized and $\tau$ is much smaller than $|A||B|/L_X^2$, then most cross edges are expensive. Hence a low-energy configuration must arrange that for most cross-label pairs, selected vertices have very few expensive incidences. This should force one of:

1. a dominant fibre;
2. many vertices becoming exceptions;
3. a small container for the allowed labelled transversals.

The next step is to make this quantitative by choosing a dyadic energy threshold $\tau_j$ depending on class sizes $u,v$ and proving a container bound of the schematic form

$$
\#\{\Gamma:\ S_{\rm sub}(\Gamma)\le T,\ \text{profile fixed}\}
\le
\exp(O_\varepsilon(T)+o(N)).
$$

The $o(N)$ term must either be absorbed by the exception ledger or shown to be $O_\varepsilon(R)$ under $Q_P\le R$.

This is the actual heart of SBEE.

---

# 13. Proposed subcondition CEC

The next useful reduction is to isolate a purely combinatorial statement.

Fix:

- a prime block $P\subset[X,2X]$;
- a short label list $\mathcal L$ with $s=|\mathcal L|$;
- weights
  $$
  w_{m,m'}(p,q)
  =
  \left(\frac{H_{pq}^{m,m'}}{pq}\right)^2
  \qquad(m\ne m');
  $$
- a transversal $\Gamma=\{(p,m(p)):p\in P\}$.

Let

$$
S(\Gamma)
=
\sum_{\substack{p\ne q\\m(p)\ne m(q)}}
w_{m(p),m(q)}(p,q).
$$

Call $\Gamma$ $\rho$-non-dominant if no label fibre has size $\ge(1-\rho)N$.

**CEC, Cheap-Edge Container target.**  
For every $\varepsilon>0$ and fixed $\rho>0$, the number of $\rho$-non-dominant transversals $\Gamma$ with

$$
S(\Gamma)\le T
$$

is at most

$$
\exp\{\varepsilon T+O_\varepsilon(R_{\rm base})\}
$$

after removing vertices in tiny fibres to the exception ledger. Here $R_{\rm base}$ denotes the internal energy already spent in producing the base list.

If CEC is proved uniformly for all short lists arising from the base construction, then SBEE follows.

The advantage of CEC is that it separates the problem into:

1. geometric/arithmetic input: divisor bounds for cheap edges;
2. combinatorial output: containers for low-weight labelled transversals;
3. exception ledger: tiny/uncovered vertices.

---

# 14. Cheap-edge incidence bound to feed CEC

For $m\ne m'$ and $\tau\le X^2$, define

$$
G_{m,m'}(\tau)
=
\{(p,q)\in P^2:\ |H_{pq}^{m,m'}|\le \tau\}.
$$

The divisor argument gives, for all $A,B\subset P$,

$$
e_{G_{m,m'}(\tau)}(A,B)
\ll
\tau L_X^2+(|A|+|B|)L_X.
$$

This is stronger than a global edge count because it is uniform in $A,B$. It says every induced bipartite subgraph of the cheap-edge graph is sparse unless $\tau$ is comparable to $|A||B|/L_X^2$.

Consequences worth proving:

## 14.1 No large bicliques of very cheap edges

If $A,B$ satisfy

$$
|A||B|\gg \tau L_X^2+(|A|+|B|)L_X,
$$

then $A\times B$ cannot be mostly $\tau$-cheap. Thus any assignment with $A=C_m$, $B=C_{m'}$ and low pair energy must pay either:

- many expensive edges, or
- entropy through the small number of possible cheap neighborhoods.

## 14.2 Degree form

For a fixed $A\subset P$, the number of $q$ with many cheap neighbors in $A$ is small. Indeed, if

$$
d_A(q)=|\{p\in A:(p,q)\in G_{m,m'}(\tau)\}|,
$$

then

$$
\#\{q:d_A(q)\ge D\}
\ll
\frac{\tau L_X^2+|A|L_X}{D}
+\frac{L_X}{D}|B|
$$

after applying the induced bound with this exceptional set as $B$.

This may be the route to containers: high cheap-degree vertices are few; low cheap-degree vertices cannot support large opposite fibres without producing expensive energy.

---

# 15. Candidate proof skeleton for CEC

For each ordered label pair $(m,m')$ and each dyadic threshold $\tau$, split cross pairs into:

$$
|H_{pq}^{m,m'}|\le \tau
\quad\text{and}\quad
|H_{pq}^{m,m'}|>\tau.
$$

If $S(\Gamma)\le T$, then the number of expensive cross pairs for this threshold is at most

$$
\ll \frac{T X^4}{\tau^2}.
$$

Therefore, except for a set of pairs whose entropy should be paid by $T$, most cross pairs must lie in the sparse cheap-edge graphs $G_{m,m'}(\tau)$.

The container plan:

1. Pick $\tau$ as a function of the profile, probably
   $$
   \tau\asymp \frac{|C_m||C_{m'}|}{L_X^2}
   $$
   at each dyadic level.
2. Use the degree form in Section 14.2 to show that once one fibre is chosen, the opposite fibre is confined to a small container plus an expensive exception set.
3. Iterate over labels in decreasing fibre size.
4. Charge every expensive exception to $T$.
5. Sum containers over all dyadic profiles.

This would turn the weak pointwise lower bound into an entropy-sensitive counting proof.

---

# 16. Two-fibre counting as the atomic lemma

Before proving CEC for all labels, isolate the two-label problem.

Fix two distinct labels $m\ne m'$ and write

$$
w(p,q)=
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2.
$$

For $A,B\subset P$, define

$$
E(A,B)=\sum_{p\in A,q\in B}w(p,q).
$$

The divisor-energy lemma gives the supersaturation lower bound

$$
E(A,B)
\gg
uv\min\left(1,\frac{u^2v^2}{X^4L_X^4}\right),
\qquad
u=|A|,\quad v=|B|.
$$

But for counting we need a stronger statement.

**Two-fibre counting target.**  
For fixed $m\ne m'$ and dyadic sizes $u,v$, estimate

$$
\mathcal N_{m,m'}(u,v;T)
=
\#\{(A,B): |A|=u,\ |B|=v,\ E(A,B)\le T\}.
$$

The target form is

$$
\mathcal N_{m,m'}(u,v;T)
\le
\exp\{O_\varepsilon(T)+{\rm lower\ order}(u,v)\},
$$

where the lower order term must be absorbable in one of:

1. the exception ledger;
2. the energy from interactions with other fibres;
3. $O_\varepsilon(R)$ after summing dyadic profiles.

This target is more honest than trying to force the pointwise lower bound to dominate

$$
\binom Nu\binom Nv.
$$

---

# 17. Quantile formulation for two-fibre counting

For fixed $A$, define weighted degrees

$$
d_A(q)=\sum_{p\in A}w(p,q).
$$

For any $B$ of size $v$,

$$
E(A,B)=\sum_{q\in B}d_A(q).
$$

The divisor-energy lemma applied to arbitrary $B$ implies a quantile lower bound:

$$
\sum_{q\in B}d_A(q)
\gg
uv\min\left(1,\frac{u^2v^2}{X^4L_X^4}\right)
$$

for every substantial $B$.

Equivalently, if $d_A^{(1)}\le d_A^{(2)}\le\cdots$ are the ordered degrees, then

$$
\sum_{j\le v}d_A^{(j)}
\gg
uv\min\left(1,\frac{u^2v^2}{X^4L_X^4}\right).
$$

This is a useful upgrade: it says not merely that one chosen $B$ has energy, but that low-degree choices for $B$ are limited.

Potential counting lemma:

If every $v$-set has total degree at least $\Lambda(u,v)$, then the number of $v$-sets with total degree at most $T$ should be bounded using the degree sequence by

$$
\#\{B:|B|=v,\ \sum_{q\in B}d_A(q)\le T\}
\le
\exp\{O(v)\}\exp\{O(T/\lambda)\}
$$

where $\lambda$ is a typical quantile scale. This is still crude, but it gives a way to make the entropy depend on low-degree structure rather than on $\binom Nv$.

Need prove an actual combinatorial bound here. This may be the right immediate subproblem.

---

# 18. Largest-fibre strategy, corrected

Let $G$ be the largest label fibre, $g=|G|$.

## Case A: $g\ge (1-\rho_0)N$

This is the genuine majority case. If $\rho_0$ is smaller than the Irving-good constant loss, every vertex outside $G$ is nonconforming relative to a dense reference class. Irving-good majority correction gives cost

$$
\gg N
$$

per outside vertex.

Entropy per outside vertex is at most

$$
O(\log X+\log s).
$$

Thus for large $X$, this case is paid without divisor-energy. This suggests that the hard case is only:

$$
g<(1-\rho_0)N.
$$

This is exactly why the dominant threshold in the single-block theorem must be chosen close to $1$, not merely positive density.

## Case B: $g<(1-\rho_0)N$

This includes both:

1. several positive-density fibres;
2. many medium/small fibres.

In this entire range, Irving-good majority correction is **not** directly legal for a single exceptional vertex, because the reference set is not dense enough. The full Irving estimate gives

$$
\sum_{p\in P}\left\|\frac{d\bar p}{q}\right\|^2\gg N,
$$

but passing to a subset $G$ loses as much as

$$
|P\setminus G|/4,
$$

so a positive-density $G$ is not enough unless its density is very close to $1$.

Thus the true hard case is all non-near-dominant configurations. If substantial fibres carry at least $\rho N$ vertices and no fibre is near-dominant, then

$$
\sum_{\alpha\ne\beta}n_\alpha n_\beta
\gg_\rho N^2.
$$

This is the genuine multi-fibre case. Here no single fibre can act as a majority reference. The correct tool must be CEC/two-fibre counting rather than Irving correction.

This case is now the narrowed core of SBEE.

---

# 19. Tiny-only non-dominant case is not hard

Suppose no dominant label exists, but substantial classes do **not** carry positive mass. Then most covered vertices lie in tiny classes:

$$
|C_m|<C_0L_X.
$$

Since the number of labels is

$$
s=|\mathcal L|\ll 1+\log X\sqrt R,
$$

the total number of vertices that can lie in tiny classes is at most

$$
\ll L_Xs
\ll L_X(1+\log X\sqrt R).
$$

If this is $\gg N$, then

$$
\sqrt R
\gg
\frac{N}{L_X\log X},
$$

so

$$
R
\gg
\frac{N^2}{L_X^2(\log X)^2}
\asymp
\frac{X^2}{L_X^2(\log X)^4}.
$$

This is much larger than the crude entropy scale

$$
N\log s+N
\ll
X
$$

for large $X$. Hence the entire tiny-only non-dominant case is absorbed by $e^{\varepsilon R}$ without Irving majority correction.

Conclusion:

SBEE may legitimately assume that substantial classes carry at least $\rho N$ vertices. The remaining hard case is:

1. no near-dominant class;
2. substantial classes carry positive mass;
3. no dense reference set is available;
4. one must use labelled weighted-container counting.

---

# 20. Degree-quantile lemma for one opposite fibre

This is the first genuinely useful counting primitive.

Fix two distinct labels $m\ne m'$. Fix $A\subset P$ with

$$
|A|=u\ge C_0L_X.
$$

For $q\in P$, define the weighted degree from $q$ to $A$ by

$$
d_A(q)
=
\sum_{p\in A}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2.
$$

Let

$$
d_A^{(1)}\le d_A^{(2)}\le\cdots\le d_A^{(N)}
$$

be the increasing rearrangement of these degrees.

Because the cross-label divisor-energy lemma applies to every subset $B\subset P$ of size $v\ge C_0L_X$, we get

$$
\sum_{j\le v}d_A^{(j)}
\gg
uv\min\left(1,\frac{u^2v^2}{X^4L_X^4}\right).
$$

In the unsaturated range

$$
v\le \frac{X^2L_X^2}{u},
$$

this gives

$$
\sum_{j\le v}d_A^{(j)}
\gg
\frac{u^3v^3}{X^4L_X^4}.
$$

Since the degrees are increasing, for $k\ge 2C_0L_X$,

$$
d_A^{(k)}
\ge
\frac1k\sum_{j\le k}d_A^{(j)}
\gg
\frac{u^3k^2}{X^4L_X^4}
$$

up to harmless constants in the same unsaturated range.

Thus the low-degree counting function satisfies

$$
\#\{q:d_A(q)\le \lambda\}
\ll
C_0L_X+
\frac{X^2L_X^2}{u^{3/2}}\lambda^{1/2}
$$

for $\lambda\ll u$.

This is much stronger than the raw divisor-energy lower bound: it says that, relative to a fixed substantial fibre $A$, low-energy choices for the opposite fibre live in a small degree container.

---

# 21. Chernoff count for choosing the opposite fibre

For fixed $A$ and target size $v$, define

$$
\mathcal B_A(v;T)
=
\{B\subset P:|B|=v,\ \sum_{q\in B}d_A(q)\le T\}.
$$

For any $\beta>0$,

$$
|\mathcal B_A(v;T)|
\le
e^{\beta T}
\prod_{q\in P}(1+e^{-\beta d_A(q)}).
$$

Using the degree quantile estimate from Section 20,

$$
\sum_{q\in P}e^{-\beta d_A(q)}
\ll
L_X+
\int_0^\infty
\exp\left(
-c\beta\frac{u^3t^2}{X^4L_X^4}
\right)\,dt
+Ne^{-c\beta u}.
$$

Hence

$$
\sum_{q\in P}e^{-\beta d_A(q)}
\ll
L_X+
\frac{X^2L_X^2}{u^{3/2}\beta^{1/2}}
+Ne^{-c\beta u}.
$$

Therefore

$$
|\mathcal B_A(v;T)|
\le
\exp\left(
\beta T
+C L_X
+C\frac{X^2L_X^2}{u^{3/2}\beta^{1/2}}
+CN e^{-c\beta u}
\right).
$$

Optimizing the first two main terms gives roughly

$$
\log |\mathcal B_A(v;T)|
\ll
L_X+
\left(\frac{X^2L_X^2}{u^{3/2}}\right)^{2/3}T^{1/3}
$$

provided $\beta u\gg\log N$ so that the saturated tail is negligible.

This is not yet SBEE, because it counts $B$ after $A$ has been fixed and ignores the entropy of choosing $A$. But it is the right kind of estimate: the entropy now depends sublinearly on the energy budget $T$, and improves rapidly when $u$ is large.

---

# 22. How this could feed multi-label counting

The sequential plan is:

1. Order label fibres by decreasing size.
2. Choose the largest fibre by crude entropy.
3. For each next fibre $B$, count choices using the weighted degrees to the already chosen larger fibres.

If the already chosen union is a single large fibre, Section 21 applies directly with $u$ equal to that fibre size. If the already chosen union has several labels, define

$$
d_{\rm prev}^{m'}(q)
=
\sum_{m\in\mathcal L_{\rm prev}}
\sum_{p\in C_m}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2.
$$

For every candidate fibre $B$ of label $m'$, its cross energy to previous fibres is

$$
\sum_{q\in B}d_{\rm prev}^{m'}(q).
$$

The needed extension of Section 20 is a quantile lower bound for $d_{\rm prev}^{m'}$ in terms of the previous profile:

$$
\sum_{j\le v}(d_{\rm prev}^{m'})^{(j)}
\gg
\sum_{m\in\mathcal L_{\rm prev}}
u_m v
\min\left(1,\frac{u_m^2v^2}{X^4L_X^4}\right).
$$

This follows by applying divisor-energy to each previous fibre and summing. The difficulty is that if all previous fibres are small, the right side involves $\sum u_m^3$, not $(\sum u_m)^3$.

Thus the next mathematical task is to find an ordering or grouping that keeps

$$
\sum_{\rm previous}u_m^3
$$

large enough at each step, or else proves that a profile with small $\sum u_m^3$ already has such many fibres that the total pair energy/container entropy works globally.

---

# 23. Extra structure from the base list

One arithmetic feature has not yet been used in the container discussion.

The labels in the base list all satisfy

$$
m\equiv a_{p_0}\pmod {p_0}.
$$

Therefore, for two labels $m\ne m'$,

$$
D=m'-m
$$

is a nonzero multiple of the base prime $p_0\asymp X$:

$$
D=p_0 r,
\qquad
|r|\ll \log X\sqrt R.
$$

Cheap edges between labels $m,m'$ can be written more explicitly. If

$$
|H_{pq}^{m,m'}|\le \tau,
$$

then there is an integer $n$ with

$$
|n|\le\tau,\qquad
n=m+p\alpha=m'+q\beta
$$

for some integers $\alpha,\beta$. Hence

$$
p\alpha-q\beta=D.
$$

The ranges are

$$
|\alpha|,|\beta|
\ll
\frac{B+\tau}{X}.
$$

Thus the cheap-edge graph is contained in the set of prime solutions to

$$
p\alpha-q\beta=p_0r
$$

with $p,q\sim X$ and relatively short $\alpha,\beta$ ranges.

This may improve the raw divisor bound

$$
e_{\rm cheap}(A,B)\ll \tau L_X^2+(|A|+|B|)L_X
$$

in the ranges relevant to SBEE. In particular, when $\tau<X^2$ and $B$ is not too large, the auxiliary variables have length

$$
M_\tau\asymp \frac{B+\tau}{X}.
$$

Counting cheap incidences becomes closer to a bilinear linear-equation problem than to an arbitrary sparse graph.

Potential use:

1. If $M_\tau$ is small, cheap neighborhoods have strong additive structure.
2. A vertex $p$ cannot have large cheap degree to many labels unless many equations
   $$
   p\alpha-q\beta=p_0r
   $$
   hold with small $\alpha,\beta,r$.
3. This could provide the missing entropy saving for medium fibres, where the crude divisor-energy bound is too weak.

This should be checked before committing fully to an abstract container proof.

---

# 24. Functional decomposition of cheap graphs

Continue with two labels

$$
m=m_0+t p_0,\qquad m'=m_0+t'p_0,
$$

so

$$
D=m'-m=p_0r,\qquad r=t'-t.
$$

For a threshold $\tau$, every $\tau$-cheap edge satisfies

$$
p\alpha-q\beta=p_0r,
\qquad
|\alpha|,|\beta|\ll M_\tau:=\frac{B+\tau}{X}.
$$

For fixed nonzero $\alpha,\beta,r$, the equation determines $q$ from $p$:

$$
q=\frac{p\alpha-p_0r}{\beta}.
$$

Thus, for fixed $(\alpha,\beta,r)$, the corresponding cheap edges form a partial matching / partial graph of a function from $p$ to $q$. In particular, between arbitrary subsets $A,B\subset P$ it contributes at most

$$
\min(|A|,|B|)
$$

edges.

Therefore the whole $\tau$-cheap graph also satisfies the functional bound

$$
e_{\rm cheap}(A,B)
\ll
M_\tau^2\min(|A|,|B|)
$$

for a fixed label pair. Here the number of possible $(\alpha,\beta)$ is $O(M_\tau^2)$; $r$ is fixed once the two labels are fixed.

We now have two independent cheap-edge bounds:

$$
e_{\rm cheap}(A,B)
\ll
\tau L_X^2+(|A|+|B|)L_X
$$

and

$$
e_{\rm cheap}(A,B)
\ll
\left(\frac{B+\tau}{X}\right)^2\min(|A|,|B|).
$$

The first is strong for large $\tau$ because it is essentially divisor-counting by the small representative $n$.

The second is strong when $M_\tau$ is small, i.e. when

$$
\tau\ll X
$$

or when $B$ is still small relative to $X$.

The hope is to combine them in the container proof:

$$
e_{\rm cheap}(A,B)
\ll
\min\left\{
\tau L_X^2+(|A|+|B|)L_X,\,
\left(\frac{B+\tau}{X}\right)^2\min(|A|,|B|)
\right\}.
$$

This may improve the medium-fibre regime where the pure divisor-energy quantile is too weak.

Important caveat: if $\beta=0$ or $\alpha=0$, the equation degenerates. These correspond to $n=m'$ or $n=m$ special terms already handled by the divisor-exception part. They contribute only

$$
O((|A|+|B|)L_X)
$$

and can be kept in the cheap-edge exceptional ledger.

---

# 25. A concrete two-fibre container lemma

Fix labels $m\ne m'$ and a threshold $\tau$. Let $G_\tau=G_{m,m'}(\tau)$ be the cheap-edge graph

$$
G_\tau=\{(p,q): |H_{pq}^{m,m'}|\le \tau\}.
$$

For $A\subset P$, define its cheap neighborhood

$$
N_\tau(A)=\{q\in P:\exists p\in A,\ (p,q)\in G_\tau\}.
$$

By the functional decomposition in Section 24, ignoring the already controlled degenerate special terms,

$$
|N_\tau(A)|
\ll
M_\tau^2|A|,
\qquad
M_\tau=\frac{B+\tau}{X}.
$$

Now suppose $B\subset P$ and

$$
E(A,B)=
\sum_{p\in A,q\in B}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2
\le T.
$$

Every pair $(p,q)\notin G_\tau$ contributes at least

$$
\frac{\tau^2}{X^4}
$$

to the energy. Hence the number of non-cheap pairs in $A\times B$ is at most

$$
\frac{T X^4}{\tau^2}.
$$

If $q\notin N_\tau(A)$, then all $|A|$ pairs $(p,q)$ are non-cheap. Therefore

$$
|B\setminus N_\tau(A)|
\le
\frac{T X^4}{\tau^2|A|}.
$$

Thus we have a genuine container:

$$
B\subset N_\tau(A)\cup E_B,
\qquad
|E_B|\le \frac{T X^4}{\tau^2|A|},
$$

with

$$
|N_\tau(A)|\ll \left(\frac{B+\tau}{X}\right)^2|A|.
$$

For fixed $A$, $u=|A|$, $v=|B|$, this gives the counting bound

$$
\#\{B:|B|=v,\ E(A,B)\le T\}
\le
\sum_{r\le T X^4/(\tau^2u)}
\binom{N}{r}
\binom{C M_\tau^2u}{v-r}.
$$

This is the most concrete two-fibre container found so far.

---

# 26. Optimizing the two-fibre container

The bound in Section 25 has two costs:

1. container size:
   $$
   C M_\tau^2u
   =
   C\left(\frac{B+\tau}{X}\right)^2u;
   $$
2. exception size:
   $$
   r_\tau
   =
   \frac{T X^4}{\tau^2u}.
   $$

If $\tau\gg B$, these become

$$
{\rm container}\sim \frac{\tau^2}{X^2}u,
\qquad
r_\tau\sim \frac{T X^4}{\tau^2u}.
$$

Their product is roughly

$$
({\rm container})\cdot r_\tau
\sim
T X^2,
$$

so increasing $\tau$ makes the container larger but the exception set smaller.

To make the container comparable to $v$, choose

$$
\frac{\tau^2}{X^2}u\asymp v,
\qquad
\tau\asymp X\sqrt{\frac vu}.
$$

Then

$$
r_\tau
\asymp
\frac{T X^2}{v}.
$$

This is useful if

$$
T\ll \frac{v^2}{X^2},
$$

because then only a small fraction of $B$ lies outside the cheap container.

For balanced fibres $u=v$, this threshold is $\tau\asymp X$ and

$$
r_\tau\asymp \frac{T X^2}{u}.
$$

Thus the functional container is strongest in the very-low-energy regime. In higher-energy regimes, $e^{\varepsilon T}$ may itself pay more of the entropy.

This suggests a two-regime proof:

1. **Very low pair energy:** use the cheap-neighborhood container.
2. **Moderate/high pair energy:** let the energy term $e^{\varepsilon T}$ pay the relevant choices.

The remaining challenge is to make this compatible with the global energy budget, because pair energies are distributed over many label pairs.

---

# 27. Star cheap-degree bound from the short label list

There is a stronger local fact than the two-fibre container, and it uses the shortness of the base list directly.

Fix a labelled set

$$
\Gamma_0=\{(p,m_p):p\in A_0\}\subset P\times\mathcal L.
$$

Fix a candidate vertex $q\in P$ and a candidate label $m'\in\mathcal L$. For a threshold $\tau$, say that $p\in A_0$ is $\tau$-cheap to $(q,m')$ if

$$
|H_{pq}^{m_p,m'}|\le\tau.
$$

Then there exists an integer $n$ such that

$$
|n|\le\tau,\qquad n\equiv m'\pmod q,\qquad n\equiv m_p\pmod p.
$$

The number of possible $n$ is

$$
\ll 1+\frac{\tau}{X}.
$$

For a fixed such $n$, count possible $p$. Since every label in $\mathcal L$ has the form

$$
m=m_0+p_0t
$$

with $t$ in an interval of length $s=|\mathcal L|$, the condition $p\mid n-m_p$ implies

$$
p\mid n-m_0-p_0t
$$

for some admissible $t$. For each fixed $t$, the integer $n-m_0-p_0t$ has size $\ll B_{\rm list}+\tau$, so it has at most

$$
\ll L_X
$$

prime divisors in $[X,2X]$. Summing over $t$ gives

$$
\#\{p\in P:\ p\mid n-m_p\}
\ll sL_X.
$$

Therefore

$$
\#\{p\in A_0:\ |H_{pq}^{m_p,m'}|\le\tau\}
\ll
\left(1+\frac{\tau}{X}\right)sL_X.
$$

Call this quantity

$$
D_\tau
:=
C\left(1+\frac{\tau}{X}\right)sL_X.
$$

This bound is uniform in:

- the previously chosen labelled set $\Gamma_0$;
- the candidate vertex $q$;
- the candidate label $m'$.

This is stronger than the previous cheap-neighborhood bound when the previous set is large.

---

# 28. Star lower bound for adding a new fibre

Let $\Gamma_0$ be a previously chosen labelled set of size

$$
U=|\Gamma_0|.
$$

For a candidate labelled vertex $(q,m')$, its cross energy to $\Gamma_0$ is

$$
d_{\Gamma_0}^{m'}(q)
=
\sum_{(p,m_p)\in\Gamma_0}
\left(\frac{H_{pq}^{m_p,m'}}{pq}\right)^2.
$$

By the star cheap-degree bound, at most $D_\tau$ terms have

$$
|H_{pq}^{m_p,m'}|\le\tau.
$$

All other terms contribute at least $\tau^2/X^4$. Hence

$$
d_{\Gamma_0}^{m'}(q)
\ge
(U-D_\tau)_+\frac{\tau^2}{X^4}.
$$

Choose $\tau$ so that

$$
D_\tau\le U/2.
$$

For instance, if $U\gg sL_X$, we may take

$$
\tau\asymp \frac{UX}{sL_X}
$$

up to the natural cap $\tau\le X^2$. Then

$$
d_{\Gamma_0}^{m'}(q)
\gg
U\frac{\tau^2}{X^4}
\asymp
\frac{U^3}{s^2L_X^2X^2}.
$$

Thus every vertex in the next fibre pays at least

$$
\lambda(U)
:=
c\frac{U^3}{s^2L_X^2X^2}
$$

energy to the previously chosen labelled set, as long as $sL_X\ll U\ll sL_XX$ and $\tau\le X^2$. If the formula gives $\tau>X^2$, then the trivial cap gives instead a lower bound $\gg U$.

This is exactly the kind of estimate missing from the pure pairwise divisor-energy approach: it uses the short list to prevent one new vertex from being cheap to too many previously labelled vertices.

---

# 29. Sequential entropy-energy estimate from the star bound

Order substantial fibres arbitrarily, and let $U_j$ be the total number of vertices in earlier fibres before choosing the $j$-th fibre.

If the $j$-th fibre has size $v_j$, then Section 28 gives cross energy at least

$$
v_j\lambda(U_j)
\asymp
v_j\frac{U_j^3}{s^2L_X^2X^2}
$$

whenever $U_j\gg sL_X$.

The entropy of choosing this fibre is at most

$$
\binom{N}{v_j}
\le
\exp\left(v_j\log\frac{eN}{v_j}\right).
$$

Hence this step is energy-paid if

$$
\frac{U_j^3}{s^2L_X^2X^2}
\gg
\log\frac{eN}{v_j}.
$$

Once

$$
U_j
\gg
\left(s^2L_X^2X^2\log N\right)^{1/3},
$$

all later fibres are paid automatically by the star bound.

So the only remaining initial segment to handle is before the accumulated previous mass reaches

$$
U_\ast
:=
\left(s^2L_X^2X^2\log N\right)^{1/3}.
$$

The entropy of choosing this initial segment is at most roughly

$$
U_\ast\log N.
$$

If this is $\ll \varepsilon R$, then SBEE closes.

Using

$$
s\ll \log X\sqrt R,
$$

we get

$$
U_\ast
\ll
X^{2/3} R^{1/3}(\log X)^{O(1)}.
$$

Thus the initial entropy is

$$
\ll
X^{2/3}R^{1/3}(\log X)^{O(1)}.
$$

This is absorbed by $\varepsilon R$ provided

$$
R\gg X(\log X)^{O(1)}.
$$

Therefore:

- for large $R$, the star-bound sequential argument plausibly closes SBEE;
- for small $R\ll X\operatorname{polylog}X$, the threshold $U_\ast$ may exceed the available energy budget, and one needs a sharper argument.

This is a substantial reduction: the difficult SBEE range may now be only

$$
R\lesssim X\operatorname{polylog}X.
$$

But in that range the short list size is

$$
s\ll X^{1/2}\operatorname{polylog}X,
$$

and the number of substantial classes is correspondingly limited. The next task is to combine this with the two-fibre container from Sections 25-26.

---

# 30. Star-energy integral and the critical window

The star lower bound also gives a deterministic energy lower bound for any non-dominant substantial configuration.

Let $W$ be the number of vertices lying in substantial non-dominant fibres. In SBEE we may assume

$$
W\ge \rho N.
$$

Expose these vertices one by one in any order that respects their final labels. When $U$ vertices have already been exposed, Section 28 gives the next vertex cost at least

$$
c\frac{(U-C sL_X)_+^3}{s^2L_X^2X^2}.
$$

Therefore the total substantial cross energy satisfies

$$
S_{\rm sub}
\gg
\frac1{s^2L_X^2X^2}
\int_0^W (U-C sL_X)_+^3\,dU.
$$

If

$$
sL_X\le c_\rho N,
$$

then, since $W\ge\rho N$,

$$
S_{\rm sub}
\gg_\rho
\frac{N^4}{s^2L_X^2X^2}.
$$

Using

$$
N\asymp \frac{X}{\log X},
\qquad
s\ll \log X\sqrt R,
$$

we obtain

$$
S_{\rm sub}
\gg
\frac{X^2}{R(\log X)^{O(1)}}.
$$

Thus any configuration with $Q_P(a)\le R$ must satisfy

$$
R
\gg
\frac{X}{(\log X)^{O(1)}}.
$$

So the non-dominant substantial case is impossible in the genuinely small-energy range

$$
R\ll X/(\log X)^C
$$

for a sufficiently large fixed $C$.

On the other hand, Section 29 suggests that once

$$
R\gg X(\log X)^C,
$$

the sequential star-bound entropy can be absorbed by $e^{\varepsilon R}$.

Therefore the hard range is plausibly only the logarithmic critical window

$$
X/(\log X)^C
\lesssim
R
\lesssim
X(\log X)^C.
$$

This is a major narrowing. In this window

$$
s\ll X^{1/2}(\log X)^{O(1)},
$$

and substantial non-dominant configurations must have:

1. positive substantial mass $\rho N$;
2. no near-dominant fibre;
3. energy $S_{\rm sub}\asymp X$ up to logarithms;
4. label list length about at most $X^{1/2}$ up to logarithms.

The next step should target exactly this critical window. The two-fibre container from Section 25 and the star-degree bound from Section 27 are both naturally scaled for this regime.

---

# 31. Critical-window obstruction to the naive star strategy

In the critical window, the largest substantial fibre has size at least

$$
u_{\max}\ge \frac{\rho N}{s}
\gg
X^{1/2}(\log X)^{-O(1)}.
$$

Let $G$ be such a largest fibre. Although $G$ is not dense enough for Irving majority correction, it is large enough to seed the two-fibre container.

For any other fibre $B$ of size $v$, the two-fibre container with $A=G$ says:

$$
B\subset N_\tau(G)\cup E_B,
\qquad
|E_B|\le \frac{T_{G,B}X^4}{\tau^2u_{\max}}.
$$

Choose

$$
\tau\asymp X
$$

in the critical window. Then

$$
M_\tau
=
\frac{B_{\rm list}+\tau}{X}
\ll
X^{1/2}(\log X)^{O(1)}
\asymp s(\log X)^{O(1)}.
$$

The cheap neighborhood has size

$$
|N_\tau(G)|
\ll
s^2u_{\max}(\log X)^{O(1)}.
$$

Since $u_{\max}\ge N/s$, this may still be as large as $sN$, hence trivial. So the two-fibre container with only the largest fibre is not enough.

The improvement must come from using **many previous fibres simultaneously**, via the star bound:

for a candidate vertex to be cheap to the whole previous labelled set, it must be cheap to at most

$$
D_\tau\ll sL_X
$$

of the previous vertices. Once the previous mass is $\gg sL_X$, most previous edges are expensive.

Thus a tempting critical-window strategy would be:

1. choose an initial seed of total size about $sL_X$;
2. count that seed crudely;
3. use the star lower bound to force energy for all remaining substantial vertices;
4. refine the seed count using two-fibre containers if crude seed entropy is too large.

However this is too optimistic.

The seed size $sL_X$ only ensures that new vertices have a positive star-energy lower bound. To pay the entropy of choosing a new labelled vertex from about $Ns$ possibilities, we need

$$
\lambda(U)
\gg
\log(Ns),
$$

where

$$
\lambda(U)
\asymp
\frac{U^3}{s^2L_X^2X^2}.
$$

Thus the real entropy-paying threshold is

$$
U_\ast
\asymp
\left(s^2L_X^2X^2\log(Ns)\right)^{1/3}.
$$

In the critical window $R\asymp X(\log X)^{O(1)}$, we have

$$
s\asymp X^{1/2}(\log X)^{O(1)},
$$

so

$$
U_\ast
\asymp
X(\log X)^{O(1)},
$$

which is comparable to, or larger than, the whole block size $N\asymp X/\log X$.

Therefore the naive star strategy does **not** close the critical window. What it does prove is still useful:

1. very small $R$ is impossible by the star-energy integral;
2. very large $R$ is entropy-paid;
3. the remaining critical window requires a sharper counting mechanism.

In that window, one cannot pay entropy vertex-by-vertex. One must exploit correlations between the choices: low energy forces many vertices simultaneously to lie in structured cheap-incidence sets.

This brings the focus back to the two-fibre / multi-fibre container, but now with a better understanding:

- star bounds rule out too many cheap incidences to an already large labelled set;
- two-fibre containers describe the structure of a fibre with low energy to another fibre;
- the missing piece is a **multi-fibre seed container** that counts the initial segment up to size about $U_\ast$ more efficiently than crude entropy.

This is the current precise bottleneck.

---

# 32. New target: multi-fibre seed container

The remaining problem can be isolated as follows.

In the critical window, define

$$
U_\ast
=
\left(s^2L_X^2X^2\log(Ns)\right)^{1/3}.
$$

The star bound pays entropy only after the exposed substantial mass exceeds $U_\ast$. Therefore we need to count possible initial labelled seeds

$$
\Gamma_{\rm seed}\subset P\times\mathcal L,
\qquad
|\Gamma_{\rm seed}|\le U_\ast,
$$

under the assumption that this seed is part of a global non-dominant substantial configuration with low internal energy.

Crude entropy gives

$$
\log \#\Gamma_{\rm seed}
\lesssim
U_\ast\log(Ns),
$$

which is too large in the critical window.

The needed statement is:

**Seed container target.**  
For every $\varepsilon>0$, the number of possible low-energy labelled seeds of size up to $U_\ast$ is at most

$$
\exp\{\varepsilon R\}
$$

after accounting for their internal cross energy.

Equivalently, among the first $U_\ast$ substantial vertices, low energy must already impose enough two-fibre cheap-incidence structure to beat crude entropy.

---

# 33. Why a seed should already have structure

Suppose a seed has fibres of sizes $n_1,\ldots,n_t$ and total size $U\le U_\ast$. Its internal seed cross energy is at least, by divisor-energy,

$$
S_{\rm seed}
\gg
\sum_{\alpha\ne\beta}
n_\alpha n_\beta
\min\left(1,\frac{n_\alpha^2n_\beta^2}{X^4L_X^4}\right).
$$

This lower bound alone is too weak in the medium-fibre regime. But if the seed is low energy, then for many pairs of fibres $(A_\alpha,A_\beta)$, one of the following must hold:

1. their pair energy is not especially low, and can be charged directly;
2. one fibre lies mostly inside a cheap-neighborhood container of the other;
3. both fibres are part of a larger cheap-incidence cluster.

Thus the seed should decompose into clusters generated by iterated cheap-neighborhoods.

For labels $m\ne m'$ and threshold $\tau$, the cheap-neighborhood operation has branching factor roughly

$$
M_\tau^2
\asymp
\left(\frac{B_{\rm list}+\tau}{X}\right)^2.
$$

In the critical window, for $\tau\asymp X$,

$$
M_\tau^2\asymp s^2(\log X)^{O(1)}.
$$

This is large for one step, but iterated cheap neighborhoods must also satisfy different label equations

$$
p\alpha-q\beta=p_0(t'-t).
$$

A plausible route is to show that a long cheap-incidence chain has far fewer choices than the product of one-step branching factors, because consecutive linear equations constrain the intermediate primes and label differences.

This suggests a path-counting lemma.

---

# 34. Candidate path-counting lemma

Fix a sequence of labels

$$
t_0,t_1,\ldots,t_\ell
$$

and primes

$$
p_0',p_1',\ldots,p_\ell'\in P
$$

such that each consecutive edge is $\tau$-cheap:

$$
|H_{p_{i-1}'p_i'}^{m_{t_{i-1}},m_{t_i}}|\le\tau.
$$

Then there exist integers $\alpha_i,\beta_i$ with

$$
p_{i-1}'\alpha_i-p_i'\beta_i
=
p_0(t_i-t_{i-1}),
\qquad
|\alpha_i|,|\beta_i|\ll M_\tau.
$$

For fixed labels and auxiliary variables, the primes satisfy a chain of linear fractional relations. The hope is that the number of possible prime paths of length $\ell$ is

$$
\ll
N\cdot M_\tau^{O(\ell)}
$$

with an exponent strictly smaller than the naive $2\ell$, or with strong collision constraints when the path branches.

If such a path-counting lemma exists, then cheap-incidence clusters have small entropy, and the seed container may close.

This is now the most concrete mathematical subproblem:

> Count connected components in the graph generated by cheap edges across labels, using the linear equations from the base-list structure.

It may be easier than a full hypergraph container and more faithful to the arithmetic structure.

---

# 35. Stronger fixed-label cheap-degree bound

There is a simpler and stronger bound than the functional decomposition of Section 24 when the two labels are fixed.

Fix $m\ne m'$ and a threshold $\tau\le X^2$. For a fixed $p\in P$, count $q\in P$ such that

$$
|H_{pq}^{m,m'}|\le \tau.
$$

Such a $q$ gives an integer $n$ with

$$
|n|\le \tau,\qquad n\equiv m\pmod p,\qquad q\mid n-m'.
$$

The number of possible $n$ with $|n|\le\tau$ and $n\equiv m\pmod p$ is

$$
\ll 1+\frac{\tau}{X}.
$$

For each such $n$, the number of primes $q\in[X,2X]$ dividing $n-m'$ is

$$
\ll L_X.
$$

Therefore every left degree in the fixed-label cheap graph is bounded by

$$
\Delta_\tau
\ll
\left(1+\frac{\tau}{X}\right)L_X.
$$

The same argument with $p,q$ interchanged gives the right-degree bound.

Thus for all $A,B\subset P$,

$$
e_{\rm cheap}^{m,m'}(A,B)
\ll
\left(1+\frac{\tau}{X}\right)L_X\min(|A|,|B|).
$$

This is far stronger than the earlier functional bound

$$
\left(\frac{B_{\rm list}+\tau}{X}\right)^2\min(|A|,|B|)
$$

in the critical window, because it does **not** lose the full label-list length $s$ for a fixed label pair.

This is a positive sign: medium fibres may be controllable by ordinary graph containers with maximum degree $\Delta_\tau$.

---

# 36. Improved two-fibre container

Using Section 35, the cheap neighborhood of $A$ for a fixed opposite label satisfies

$$
|N_\tau(A)|
\ll
\Delta_\tau |A|,
\qquad
\Delta_\tau
=
C\left(1+\frac{\tau}{X}\right)L_X.
$$

If $E(A,B)\le T$, the same non-cheap pair argument gives

$$
B\subset N_\tau(A)\cup E_B,
\qquad
|E_B|
\le
\frac{T X^4}{\tau^2|A|}.
$$

Hence

$$
\#\{B:|B|=v,\ E(A,B)\le T\}
\le
\sum_{r\le T X^4/(\tau^2u)}
\binom{N}{r}
\binom{C\Delta_\tau u}{v-r},
\qquad
u=|A|.
$$

This is much more useful. In particular, for $\tau\asymp X$,

$$
\Delta_\tau\ll L_X,
$$

so, up to exceptions, the opposite fibre $B$ lies in a set of size only

$$
\ll uL_X.
$$

For balanced fibres $u=v$, the entropy of choosing $B$ after $A$ drops from

$$
v\log(N/v)
$$

to roughly

$$
v\log L_X
$$

plus the exception cost.

This is precisely the missing logarithmic saving in the critical window.

---

# 37. Consequence for balanced medium fibres

Consider a balanced profile with

$$
t\asymp N/u
$$

fibres of size $u$, where $u$ is medium, for example

$$
X^{1/2}(\log X)^{-C}\lesssim u\lesssim X^{3/4}.
$$

A crude partition count gives entropy

$$
N\log(N/u),
$$

which was too large for the divisor-energy lower bound.

But if we build fibres sequentially and use the improved two-fibre container with $\tau\asymp X$ against one previously chosen fibre, then each new fibre has entropy only

$$
u\log L_X
$$

provided its pair energy to the previous fibre is small enough that the exception set is negligible. Summing over $t$ fibres gives

$$
N\log L_X.
$$

In the critical window $R\asymp X(\log X)^{O(1)}$ and

$$
N\log L_X\ll X
$$

for large $X$, so this entropy is absorbable by $e^{\varepsilon R}$.

If the pair energy to the previous fibre is not small, then it is paid directly by $e^{\varepsilon T}$.

This suggests the following route may close the critical window:

1. group substantial fibres by dyadic size;
2. in each dyadic group, choose one seed fibre crudely;
3. build the rest of the group using the fixed-label two-fibre container with $\tau\asymp X$;
4. pay high pair-energy steps directly;
5. use cross-group interactions or repeat the same argument between adjacent dyadic groups.

The seed entropy per dyadic group is at most

$$
u\log(N/u),
$$

and there are only $O(\log N)$ dyadic groups. The total seed entropy should be

$$
\ll
\sum_{\rm groups}u_j\log(N/u_j),
$$

which is potentially much smaller than $N\log(N/u)$ if most mass lies in many fibres of the same size. This needs a careful worst-case check.

---

# 38. Updated prognosis

This fixed-label degree bound changes the outlook positively.

The earlier obstruction came from treating cheap neighborhoods as having branching factor about $s^2$. That was too pessimistic because it allowed the target label to vary. In the actual fibre-by-fibre construction, the target label is fixed while choosing a fibre, and the cheap graph degree is only polylogarithmic for $\tau\asymp X$.

The remaining technical problem is now combinatorial rather than mysterious:

> Can the substantial fibres be ordered/grouped so that all but a controlled seed entropy are counted through fixed-label cheap-neighborhood containers?

This looks more feasible than the path-counting approach.

---

# 39. Correcting the seed entropy scale

The pessimistic vertex-by-vertex seed entropy

$$
U_\ast\log(Ns)
$$

is often too crude. A seed that respects a dyadic fibre profile has entropy closer to a partition entropy.

For a balanced profile with fibre size $u$ and total mass $V$, the entropy of choosing the vertex fibres is roughly

$$
V\log\frac{N}{u}
$$

plus label-choice entropy

$$
\frac{V}{u}\log s.
$$

For $u\asymp X^{1/2}$ and $V\asymp N$, this is

$$
N\log(N/u)
\asymp
\frac{X}{\log X}\cdot \frac12\log X
\asymp X,
$$

not $X\log X$.

Thus the critical window $R\asymp X$ is not a scale disaster. The problem is a **constant/free-energy balance**:

- raw profile entropy is of order $X$;
- available energy is also of order $X$;
- we need enough arithmetic/container saving to make the entropy at most $\varepsilon R$ after weighted summation.

This is a more positive sign than Section 31 suggested.

---

# 40. Dyadic group entropy with fixed-label containers

Consider one dyadic group of fibres, all of size about $u$.

Let there be $r$ such fibres, so their total mass is

$$
V=ru.
$$

A crude count gives

$$
\exp\left(
V\log\frac{N}{u}
+r\log s
\right).
$$

Now choose one seed fibre $A_1$ crudely. Its entropy is

$$
u\log\frac{N}{u}+\log s.
$$

For another fibre $A_j$ of fixed label, if its pair energy to $A_1$ is very low, the improved two-fibre container with $\tau\asymp X$ puts most of $A_j$ inside a container of size

$$
\ll uL_X.
$$

Thus its low-energy entropy is reduced to roughly

$$
u\log L_X
$$

instead of

$$
u\log(N/u).
$$

If many fibres are low-energy relative to $A_1$, their non-exception parts all live in the same container of size $O(uL_X)$, so the total number of such fibres is at most $O(L_X)$ before the container saturates. Hence:

1. at most $O(L_X)$ fibres can be very low-energy to $A_1$ without using many exceptions;
2. the remaining fibres have nontrivial pair energy to $A_1$;
3. the low-energy fibres have only container entropy $O(uL_X\log s)$, not $O(r u\log(N/u))$.

This suggests a dyadic group argument:

- seed one fibre;
- collect all fibres low-energy to the seed into its cheap container;
- charge all other fibres by their pair energy to the seed;
- repeat with a new seed among the uncollected fibres.

The number of seed rounds is at most about

$$
\frac{r}{L_X}
$$

in the worst case, and the seed entropy is then

$$
\frac{r}{L_X}u\log\frac{N}{u}
=
\frac{V}{L_X}\log\frac{N}{u},
$$

which has an extra $L_X^{-1}$ saving.

This is potentially enough to turn the $O(X)$ critical entropy into $o(X)$, leaving the remaining part to be paid by pair energies.

---

# 41. Proposed dyadic group lemma

The following lemma would likely close SBEE when summed over dyadic groups.

**Dyadic group container lemma.**  
Fix a dyadic size $u\ge C_0L_X$ and a set of labels $\mathcal M\subset\mathcal L$. Consider disjoint fibres

$$
C_m\subset P,\qquad |C_m|\asymp u,\qquad m\in\mathcal M.
$$

Let

$$
S_{\mathcal M}
=
\sum_{\substack{m\ne m'\\m,m'\in\mathcal M}}
E(C_m,C_{m'}).
$$

Then the number of such fibre families with

$$
S_{\mathcal M}\le T
$$

is bounded by

$$
\exp\left(
\varepsilon T
+O_\varepsilon\left(
\frac{|\mathcal M|u}{L_X}\log\frac{N}{u}
+|\mathcal M|u\log L_X
+|\mathcal M|\log s
\right)
\right).
$$

The desired saving is the factor $L_X^{-1}$ in the seed entropy. Since $L_X$ is logarithmic, it is enough to make the remaining seed entropy lower order compared with the critical energy scale.

How to prove it:

1. Pick a seed fibre.
2. Use the fixed-label cheap-degree container to absorb all fibres with low energy to the seed.
3. Remove the absorbed cluster.
4. Repeat.
5. Pair-energy to seeds pays the fibres not absorbed.

This is now a concrete combinatorial lemma. It avoids path-counting and uses only:

- fixed-label cheap degree;
- disjointness of fibres;
- dyadic sizes;
- energy accounting.

This is the next best target to formalize.

---

# 42a. Risk model: one-dimensional degree bounds still leave a log gap

The fixed-label degree bound is positive, but by itself it still does not close SBEE.

Fix one label pair and one fibre $A$ of size $u$. For a fixed $q$, the number of $p\in A$ with

$$
|H_{pq}^{m,m'}|\le \tau
$$

is at most

$$
\ll 1+\frac{\tau}{X}.
$$

Equivalently, the ordered values of $|H_{pq}^{m,m'}|$ as $p$ varies over $A$ satisfy roughly

$$
H_j\gtrsim jX.
$$

Therefore the weighted degree has the lower bound

$$
d_A(q)
\gtrsim
\sum_{j\le u}\frac{(jX)^2}{X^4}
\asymp
\frac{u^3}{X^2}.
$$

For medium fibres $u\asymp X^{1/2}$, this gives

$$
d_A(q)\gtrsim X^{-1/2}.
$$

Thus a second fibre $B$ of size $v\asymp X^{1/2}$ has pair energy at least only

$$
E(A,B)\gtrsim 1.
$$

If a balanced profile has

$$
r\asymp \frac{N}{u}\asymp \frac{X^{1/2}}{\log X}
$$

fibres, summing this lower bound over all fibre pairs gives only

$$
\gtrsim r^2
\asymp
\frac{X}{(\log X)^2}.
$$

But the crude balanced-profile entropy is about

$$
N\log(N/u)\asymp X.
$$

So one-dimensional degree/order-statistic lower bounds alone leave a logarithmic gap.

This does **not** mean the route fails. It means the final proof must use global incompatibility:

> It should be impossible for many different fibre pairs, with many different label differences, to all realize the extremal order-statistic pattern simultaneously.

This is exactly where cheap-path or cheap-cluster counting re-enters.

---

# 43. The middle-energy issue

The dyadic group lemma in Section 41 is plausible, but a single-seed argument has a middle-energy gap.

For one seed fibre $A$ of size $u$ and another fibre $B$ of size $u$, the fixed-label container says:

$$
B\subset N_\tau(A)\cup E_B,
\qquad
|E_B|\le \frac{T X^4}{\tau^2u},
$$

where $T=E(A,B)$ and

$$
|N_\tau(A)|\ll \left(1+\frac{\tau}{X}\right)L_Xu.
$$

If $T$ is very small, taking $\tau\asymp X$ gives a tiny exception set and strong container entropy.

If $T$ is very large, then $e^{\varepsilon T}$ pays the crude entropy of $B$.

But for medium $T$, neither is obviously true:

- with small $\tau$, the exception set may be too large;
- with large $\tau$, the container may become nearly all of $P$;
- $T$ itself may still be smaller than $u\log(N/u)$.

Thus the correct group proof cannot classify a fibre using only its energy to one seed. It must use **energy to many seeds simultaneously**.

---

# 44. Multi-seed version

Let $A_1,\ldots,A_K$ be already chosen seed fibres, each of size about $u$, with labels distinct from the candidate label $m$.

For a candidate fibre $B$ of size $u$, define total energy to the seeds

$$
T_{\rm seed}(B)
=
\sum_{i=1}^K E(A_i,B).
$$

For each $q\in B$, the star cheap-degree bound says that $q$ can be $\tau$-cheap to at most

$$
D_\tau\ll \left(1+\frac{\tau}{X}\right)sL_X
$$

vertices across all seed fibres and labels. Since the seed union has size

$$
U=Ku,
$$

we get

$$
d_{\rm seed}(q)
\ge
(U-D_\tau)_+\frac{\tau^2}{X^4}.
$$

Therefore

$$
T_{\rm seed}(B)
\ge
u(U-D_\tau)_+\frac{\tau^2}{X^4}.
$$

Choose $\tau$ so that $D_\tau\le U/2$. Then

$$
T_{\rm seed}(B)
\gg
uU\frac{\tau^2}{X^4}.
$$

Taking the largest allowed such $\tau$,

$$
\tau\asymp \frac{UX}{sL_X},
$$

gives

$$
T_{\rm seed}(B)
\gg
\frac{uU^3}{s^2L_X^2X^2}.
$$

This is the same star lower bound, now applied fibre-by-fibre.

To make this pay the entropy of $B$,

$$
u\log\frac{N}{u},
$$

it suffices that

$$
\frac{U^3}{s^2L_X^2X^2}
\gg
\log\frac{N}{u}.
$$

So once the total seed mass exceeds

$$
U(u)
=
\left(s^2L_X^2X^2\log\frac{N}{u}\right)^{1/3},
$$

all further fibres of size $u$ are paid by energy to the seed collection.

This leaves only the entropy of building the seed collection up to mass $U(u)$.

---

# 45. Seed collection entropy by fibre size

For a dyadic group of fibre size $u$, the number of seed fibres needed is

$$
K(u)=\frac{U(u)}{u}.
$$

Their crude entropy is

$$
K(u)\,u\log\frac{N}{u}
=
U(u)\log\frac{N}{u}.
$$

Substitute

$$
U(u)
=
\left(s^2L_X^2X^2\log\frac{N}{u}\right)^{1/3}.
$$

The seed entropy becomes

$$
\left(s^2L_X^2X^2\right)^{1/3}
\left(\log\frac{N}{u}\right)^{4/3}.
$$

In the critical window $s\asymp X^{1/2}\operatorname{polylog}X$, this is

$$
X(\log X)^{O(1)}
\left(\frac{\log(N/u)}{\log X}\right)^{4/3}.
$$

So it is still of order $X$ up to logarithms, not obviously lower order. But crucially:

- this seed entropy is paid once per dyadic size group;
- the remaining fibres are energy-paid;
- dyadic groups contribute only logarithmically many such terms.

The constants/logs remain delicate. This is the current quantitative bottleneck.

Potential improvement:

Use the two-fibre fixed-label container to count the seed fibres themselves, instead of choosing them crudely. Even among seeds, low pair energies force cheap-neighborhood structure, and high pair energies pay entropy. This suggests applying the same multi-seed argument recursively.

This recursive seed-counting is now the natural next step.

---

# 46. Bucket representation of cheap edges

The cleanest way to see the global structure is not by paths but by buckets.

Fix a threshold $\tau$. For a labelled vertex $(p,t)$, where

$$
m_t=m_0+p_0t,
$$

define its $\tau$-bucket set

$$
\mathcal B_\tau(p,t)
=
\{n\in\mathbb Z:\ |n|\le\tau,\ n\equiv m_t\pmod p\}.
$$

Then

$$
|\mathcal B_\tau(p,t)|\ll 1+\frac{\tau}{X}.
$$

Two labelled vertices $(p,t)$ and $(q,t')$ are $\tau$-cheap exactly when

$$
\mathcal B_\tau(p,t)\cap \mathcal B_\tau(q,t')\ne\varnothing.
$$

Equivalently, the cheap graph is the intersection graph generated by integer buckets $n$:

$$
(p,t)\sim_\tau(q,t')
\quad\Longleftrightarrow\quad
\exists n,\ |n|\le\tau,\ n\equiv m_t\pmod p,\ n\equiv m_{t'}\pmod q.
$$

For fixed $n$ and fixed label $t$, the possible primes $p$ satisfy

$$
p\mid n-m_t.
$$

Since $|n-m_t|\ll B_{\rm list}+\tau$, the number of such primes in $[X,2X]$ is

$$
\ll L_X.
$$

Hence one bucket contains at most

$$
\ll sL_X
$$

labelled vertices, and at most $O(L_X)$ vertices from each label fibre.

This bucket model is stronger conceptually than the graph-degree picture. A low-energy multi-label configuration must have many cross pairs sharing buckets; but buckets have limited capacity per label.

---

# 47. A deterministic bucket lower bound and its log gap

Let $\Gamma$ be a labelled set of $W$ substantial vertices. The total number of bucket incidences is at most

$$
I_\tau(\Gamma)
\ll
W\left(1+\frac{\tau}{X}\right).
$$

Since each bucket has occupancy at most $O(sL_X)$, the number of $\tau$-cheap pairs in $\Gamma$ is at most

$$
E_{\rm cheap}(\Gamma;\tau)
\ll
sL_X\,I_\tau(\Gamma)
\ll
W sL_X\left(1+\frac{\tau}{X}\right).
$$

Every non-cheap cross pair has

$$
|H|>\tau
$$

and hence contributes at least

$$
\frac{\tau^2}{X^4}
$$

to $Q_P$.

Ignoring same-label pairs, a non-dominant substantial configuration has

$$
\gg_\rho W^2
$$

cross-label pairs. Therefore

$$
Q_P
\gg
\left(
c_\rho W^2
-CWsL_X\left(1+\frac{\tau}{X}\right)
\right)_+
\frac{\tau^2}{X^4}.
$$

Take $W\asymp N$ and the critical-window value

$$
s\asymp X^{1/2}\operatorname{polylog}X.
$$

The cheap-pair term becomes comparable to $W^2$ when

$$
\tau
\asymp
\frac{WX}{sL_X}
\asymp
\frac{X^{3/2}}{(\log X)^{O(1)}}.
$$

At this threshold the lower bound gives roughly

$$
Q_P\gg
\frac{W^2\tau^2}{X^4}
\asymp
\frac{X}{(\log X)^{O(1)}}.
$$

So the bucket-capacity argument nearly reaches the critical scale $X$, but loses logarithms.

This is very informative:

- the obstruction is not a power-scale obstruction;
- the remaining task is to remove logarithmic losses by using more than the crude maximum bucket occupancy $sL_X$.

The crude bound assumes every used bucket is nearly full across labels. That is the extremal scenario to rule out.

---

# 48. What a saturated bucket cluster would imply

Suppose many buckets are nearly saturated, each containing about $s$ labelled vertices, one or $O(1)$ from many labels. For a fixed bucket $n$, membership means

$$
p\mid n-m_0-p_0t.
$$

Thus each occupied incidence $(p,t,n)$ gives

$$
n=m_0+p_0t+p\alpha.
$$

If a configuration makes many cheap pairs, it must have many incidences concentrated into relatively few buckets.

But a single labelled vertex $(p,t)$ belongs to only

$$
O(1+\tau/X)
$$

buckets. For $\tau\asymp X^{3/2}/\operatorname{polylog}$, this is about

$$
X^{1/2}/\operatorname{polylog}.
$$

A saturated cluster of many buckets would therefore force many primes $p$ to divide many shifted values

$$
n-m_0-p_0t
$$

for many pairs $(n,t)$.

This is a bipartite incidence problem between:

- buckets $n$ with $|n|\le\tau$;
- labels $t$ in a short interval;
- primes $p\sim X$ dividing $n-m_0-p_0t$.

The crude upper bound treats each $(n,t)$ independently and allows $O(1)$ primes for each. To remove the log gap, we need exploit correlations between different $(n,t)$ sharing the same prime:

$$
p\mid n_1-m_0-p_0t_1,
\qquad
p\mid n_2-m_0-p_0t_2.
$$

Subtracting gives

$$
p\mid (n_1-n_2)-p_0(t_1-t_2).
$$

Since $p,p_0\asymp X$, this severely restricts repeated incidences for the same prime unless the bucket-label pairs lie on arithmetic lines

$$
n-p_0t=\text{constant mod }p.
$$

This points to a possible incidence-energy lemma:

> A large collection of bucket-label incidences with primes $p\sim X$ either has small total pair count, or it is concentrated on a structured family associated to a small set of primes/labels; such concentration should correspond to near-dominance or be energy-paid elsewhere.

This is the current candidate for removing the logarithmic gap.

---

# 49. Bucket occupancy as a sieve problem

For a fixed bucket $n$, define its full occupancy in the label-prime universe by

$$
\Omega(n)
=
\#\{(p,t):p\in P,\ t\in\mathcal L,\ p\mid n-m_0-p_0t\}.
$$

The crude deterministic bound is

$$
\Omega(n)\ll sL_X.
$$

This bound is too weak. It allows many buckets to be essentially saturated, which is exactly the scenario producing the logarithmic gap in Section 47.

But saturation should be rare. For fixed $n$, the condition can be written as

$$
n-m_0=p_0t+p\alpha,
$$

with

$$
p\sim X,\qquad |t|\le s,\qquad |\alpha|\ll \tau/X.
$$

Thus $\Omega(n)$ counts representations of $n-m_0$ by the binary form

$$
p_0t+p\alpha.
$$

Heuristically, for critical $\tau$ and $s$, the expected occupancy is much closer to

$$
\frac{s}{\log X}
$$

or smaller, not $s$. More importantly, the second moment over buckets should be small:

$$
\sum_{|n|\le\tau}\Omega(n)^2
$$

should be far below the trivial bound

$$
\tau(sL_X)^2.
$$

This is the natural arithmetic statement needed for the global cheap-cluster incompatibility.

---

# 50. Second moment expansion

Expand

$$
\sum_{|n|\le\tau}\Omega(n)^2.
$$

It counts pairs

$$
(p,t,\alpha),\quad(q,t',\beta)
$$

such that

$$
p_0t+p\alpha
=
p_0t'+q\beta,
$$

or

$$
p\alpha-q\beta
=
p_0(t'-t).
$$

This is exactly the cheap-edge equation.

The ranges are

$$
p,q\sim X,\qquad |t|,|t'|\le s,\qquad |\alpha|,|\beta|\ll M_\tau:=\tau/X.
$$

For fixed $\alpha,\beta,r=t'-t$, the equation is

$$
p\alpha-q\beta=p_0r.
$$

If $\alpha,\beta$ are both nonzero, then once $p$ is chosen, $q$ is determined up to divisibility by $\beta$:

$$
q=\frac{p\alpha-p_0r}{\beta}.
$$

Thus the number of prime pairs for fixed $(\alpha,\beta,r)$ is at most

$$
O(N)
$$

trivially, and often much less by congruence/divisibility. Summing this trivial bound gives

$$
\sum_{|n|\le\tau}\Omega(n)^2
\ll
M_\tau^2 s\,N,
$$

since there are $O(M_\tau^2s)$ choices of $(\alpha,\beta,r)$.

At the critical scale

$$
M_\tau\asymp X^{1/2}/\operatorname{polylog},
\qquad
s\asymp X^{1/2}\operatorname{polylog},
\qquad
N\asymp X/\log X,
$$

this gives roughly

$$
\ll X^{5/2}
$$

up to logarithms, which is not yet strong enough compared with the number of possible cross pairs $N^2\asymp X^2/\log^2X$ when used naively.

But this second moment counts the full universe of all labels and primes, whereas a transversal uses only one label per prime and only $N$ vertices out of $Ns$. A sharper bound should exploit the transversal restriction.

---

# 51. Transversal-restricted bucket second moment

Let $\Gamma\subset P\times\mathcal L$ be a transversal:

$$
|\Gamma\cap(\{p\}\times\mathcal L)|\le1
\qquad\text{for every }p.
$$

Define

$$
\Omega_\Gamma(n)
=
\#\{(p,t)\in\Gamma:p\mid n-m_0-p_0t\}.
$$

Cheap pairs in $\Gamma$ are controlled by

$$
\sum_n \Omega_\Gamma(n)^2.
$$

Expanding the second moment gives the same equation

$$
p\alpha-q\beta=p_0(t'-t),
$$

but now $t$ and $t'$ are functions of $p$ and $q$ inside the transversal.

This is where non-dominance and substantial fibres matter. A high second moment means many pairs of selected primes satisfy

$$
p\alpha-q\beta=p_0(t(q)-t(p))
$$

with small $\alpha,\beta$. Equivalently,

$$
\frac{p}{p_0}\alpha+t(p)
=
\frac{q}{p_0}\beta+t(q).
$$

So the selected graph has many collisions among the values

$$
\frac{p}{p_0}\alpha+t(p).
$$

This resembles additive energy of the set of labelled slopes $t(p)$ with multiplicative coefficients $p/p_0$.

Potential route:

Prove that unless $t(p)$ is almost constant on a large set, the transversal-restricted bucket second moment satisfies a saving over the trivial bucket-capacity bound.

That would directly rule out saturated cheap clusters while preserving the near-dominant case as the only extremal obstruction.

This is now the most conceptually clean target:

> A transversal bucket-energy theorem: high bucket collision energy forces near-constant label on many primes.

If true, it would close exactly the missing global incompatibility.

---

# 52. Layer-cake form of the energy

For a labelled transversal $\Gamma$, define the cheap-pair count at threshold $\tau$:

$$
C_\Gamma(\tau)
=
\#\{\{(p,t),(q,t')\}\subset\Gamma:
t\ne t',\ |H_{pq}^{m_t,m_{t'}}|\le\tau\}.
$$

Let

$$
P_\Gamma
=
\#\{\text{cross-label pairs in }\Gamma\}.
$$

Then the cross energy has the layer-cake representation

$$
S_\Gamma
\asymp
\frac1{X^4}
\int_0^{X^2}
2\tau\,
\bigl(P_\Gamma-C_\Gamma(\tau)\bigr)\,d\tau.
$$

Thus the whole problem is equivalent to controlling $C_\Gamma(\tau)$ for all $\tau$.

The bucket model gives

$$
C_\Gamma(\tau)
\le
\sum_{|n|\le\tau}\binom{\Omega_\Gamma(n)}2,
$$

where

$$
\Omega_\Gamma(n)
=
\#\{(p,t)\in\Gamma:n\equiv m_t\pmod p\}.
$$

The crude bound

$$
\Omega_\Gamma(n)\le sL_X
$$

gives

$$
C_\Gamma(\tau)
\ll
|\Gamma|sL_X\left(1+\frac{\tau}{X}\right),
$$

which yields only

$$
S_\Gamma\gg X/(\log X)^{O(1)}
$$

in the critical balanced case. To close SBEE, we need a stronger, entropy-sensitive statement:

> Either $C_\Gamma(\tau)$ is significantly smaller than the crude bucket-capacity bound on a positive measure set of thresholds $\tau$, or the high bucket occupancies force a structured near-dominant/low-entropy configuration.

This is perhaps the cleanest formulation of the remaining problem.

---

# 53. Candidate final SBEE sublemma

The following would be sufficient.

**Transversal bucket collision lemma.**  
Let $\Gamma\subset P\times\mathcal L$ be a labelled transversal with no near-dominant label fibre and with substantial mass $|\Gamma|\ge\rho N$. Then for every $\eta>0$,

$$
\#\{\Gamma:\ S_\Gamma\le R\}
\le
\exp(\eta R)
$$

uniformly in the critical range, provided $S_\Gamma$ is computed by the bucket layer-cake above.

More structurally, it would suffice to prove that any family of transversals with large collision counts

$$
C_\Gamma(\tau)
$$

for many $\tau$ can be covered by containers whose entropy is at most the energy saving obtained from the complementary thresholds.

Inputs available for proving it:

1. each labelled vertex has about $1+\tau/X$ buckets;
2. each bucket-label slice has size $O(L_X)$;
3. fixed-label cheap graphs have degree $O((1+\tau/X)L_X)$;
4. bucket collision equations have the form
   $$
   p\alpha-q\beta=p_0(t'-t);
   $$
5. the transversal condition allows only one label per prime.

This is now a sharply isolated mathematical problem. It is stronger and cleaner than the original SBEE wording, and it directly targets the only place where the logarithmic gap remains.

---

# 54. External-tool scan

A narrow scan of existing tools suggests the following.

## 54.1 Graph / hypergraph containers

The relevant container lineage is:

- Kleitman--Winston / Sapozhenko graph containers for independent sets;
- Saxton--Thomason and Balogh--Morris--Samotij hypergraph containers;
- later algorithmic and partition-container variants.

These tools provide useful language:

- fingerprints;
- containers;
- max-degree exposure algorithms;
- locally dense graphs;
- partition containers for coloured/transversal objects.

But the fit is not automatic. Our family is not simply an independent-set family in a fixed graph. It is a family of labelled transversals with a weighted objective

$$
S_\Gamma
=
\sum w_{m(p),m(q)}(p,q),
$$

and the low-energy condition is soft rather than forbidden. A direct hypergraph-container theorem would require building hyperedges for "too many expensive pairs" or "too many bucket collisions", and the co-degree hypotheses would essentially restate the hard arithmetic part.

Conclusion: container theory is good scaffolding, but not a black-box solution.

## 54.2 Large sieve / larger sieve

The bucket formulation looks closer to large-sieve language. For a labelled transversal, each prime $p$ selects one residue class

$$
r_p=m_0+p_0t(p)\pmod p.
$$

Bucket occupancy is

$$
\Omega_\Gamma(n)
=
\#\{p:n\equiv r_p\pmod p\}.
$$

This is exactly a "one selected residue class modulo each prime" incidence problem.

However, a generic large-sieve second moment for arbitrary selected residue classes seems to give roughly

$$
\sum_{|n|\le\tau}\Omega_\Gamma(n)^2
\lesssim
\tau\left(\sum_{p\in P}\frac1p\right)^2
+X\sum_{p\in P}1
$$

up to logarithmic normalization. In our range this is about

$$
\frac{\tau}{(\log X)^2}
+\frac{X^2}{\log X},
$$

which still has the same logarithmic loss that we already see in the crude bucket argument.

Conclusion: a generic large sieve is probably not enough. We need exploit the special form

$$
r_p=m_0+p_0t(p),
$$

where $t(p)$ is a low-entropy label function arising from a short list and substantial fibres.

## 54.3 What the scan changes

The existing tools suggest the right proof style:

1. use a graph-container/fingerprint exposure algorithm;
2. expose high bucket-degree or high collision vertices;
3. use an arithmetic second-moment / large-sieve-like input;
4. show that extremizers of the generic large-sieve bound are incompatible with non-dominant substantial fibres.

So the next target is not a standard theorem citation, but a custom "large-sieve with structured residues" lemma.

---

# 55. Generic large-sieve barrier

Let $P_\Gamma$ be the selected primes in a transversal, and write

$$
r_p=m_0+p_0t(p).
$$

For an interval $I=[-\tau,\tau]$, define

$$
\Omega(n)=\sum_{p\in P_\Gamma}1_{n\equiv r_p\pmod p}.
$$

Expanding,

$$
\sum_{n\in I}\Omega(n)^2
=
\sum_{p,q\in P_\Gamma}
\#\{n\in I:n\equiv r_p\pmod p,\ n\equiv r_q\pmod q\}.
$$

The diagonal contributes

$$
\sum_p\left(\frac{\tau}{p}+O(1)\right)
\ll
\frac{\tau}{\log X}+N.
$$

For $p\ne q$, CRT gives one residue class modulo $pq$, so the contribution is

$$
\frac{\tau}{pq}+O(1_{\text{small representative exists}}).
$$

The main term over all pairs is

$$
\tau\left(\sum_p\frac1p\right)^2
\asymp
\frac{\tau}{(\log X)^2}.
$$

The dangerous term is the $O(1)$ part: it is precisely the cheap-pair count. A black-box large sieve can bound its average, but only at the scale

$$
\ll XN
\asymp
\frac{X^2}{\log X},
$$

which is one logarithm larger than the natural cross-pair scale

$$
N^2\asymp \frac{X^2}{(\log X)^2}.
$$

This explains why generic large sieve cannot close the proof.

The special structure must save this last logarithm.

---

# 56. Structured-residue large sieve target

The missing arithmetic lemma can now be stated in a sharper way.

Let $t:P'\to\mathcal T$ be a label function on $P'\subset P$, where $\mathcal T$ is a short interval and no value of $t$ has near-dominant fibre. Define residues

$$
r_p=m_0+p_0t(p)\pmod p.
$$

For $\tau$ in the critical range, prove a collision estimate of the form

$$
\sum_{|n|\le\tau}
\left(
\sum_{p\in P'}1_{n\equiv r_p\pmod p}
\right)^2
\le
o_\rho(1)N^2
+\text{structured-container contribution}.
$$

The structured-container contribution should consist of transversals with much smaller entropy, for example those for which $t(p)$ is nearly constant on a large subset or lies in a small number of bucket-generated clusters.

If this structured large-sieve lemma is available, then the layer-cake formula from Section 52 should give SBEE.

This is the most promising current formulation of the final mathematical task.

---

# 57. Narrow literature verdict

The existing tools are relevant, but the missing estimate is not an off-the-shelf theorem.

Useful references:

- [Gallagher, *A larger sieve*](https://eudml.org/doc/205009), Acta Arithmetica 18 (1971), 77--81.
- [Saxton--Thomason, *Hypergraph containers*](https://arxiv.org/abs/1204.6595).
- [Balogh--Morris--Samotij, *The method of hypergraph containers*](https://arxiv.org/abs/1801.04584).
- [Green--Harper, *Inverse questions for the large sieve*](https://arxiv.org/abs/1311.6176).

The verdict is:

1. Gallagher's larger sieve controls sets of integers occupying few residue classes modulo many primes. Our buckets instead mark one special residue class modulo each prime and ask for unusually many incidences with that marked class. This is closer to a **dual marked-residue large sieve** than to the usual larger sieve.
2. Inverse large-sieve philosophy is relevant: extremizers should have algebraic/additive structure. But the structure here is not simply a small set of integers with few residues; it is the graph of a label function $t(p)$ through residues $m_0+p_0t(p)\pmod p$.
3. Hypergraph containers are the right language for the counting step, but the arithmetic co-degree estimates needed by a black-box container theorem are exactly the estimates still to be proved.

So the correct decision is to use the tools as a template, not as citations that close the proof. The next useful move is to prove the special dual marked-residue estimate available from the fact that all moduli are primes in one dyadic block.

---

# 58. A marked dual large-sieve lemma

Here is a deterministic estimate that does use the special bucket geometry.

Let

$$
P\subset[X,2X]
$$

be a set of primes, and remove the base prime $p_0$ from $P$ if it lies in the block. This loses only one vertex. Assume the label interval $\mathcal T$ has length

$$
s<X.
$$

For a bucket set

$$
\mathcal B\subset[-\tau,\tau]\cap\mathbb Z
$$

define

$$
d_{\mathcal B}(p,t)
=
\#\{n\in\mathcal B:n\equiv m_0+p_0t\pmod p\}.
$$

Assume also

$$
2\tau<X^2.
$$

Then

$$
\sum_{p\in P\setminus\{p_0\}}\sum_{t\in\mathcal T}
d_{\mathcal B}(p,t)^2
\le
|\mathcal B|\,|P|
+|\mathcal B|^2.
$$

**Proof.** Expanding the left side counts quadruples

$$
(n,n',p,t)
$$

with $n,n'\in\mathcal B$ and

$$
n\equiv n'\equiv m_0+p_0t\pmod p.
$$

If $n=n'$, then for each $p\ne p_0$ the congruence

$$
p_0t\equiv n-m_0\pmod p
$$

has at most one solution $t\in\mathcal T$, because $p_0$ is invertible modulo $p$ and $|\mathcal T|<p$. Thus the diagonal contributes at most $|\mathcal B||P|$.

If $n\ne n'$, then $p\mid n-n'$. Since

$$
|n-n'|\le2\tau<X^2,
$$

the integer $n-n'$ has at most one prime divisor in $[X,2X]$. For that prime, the same injectivity gives at most one label $t$. Hence the off-diagonal contribution is at most $|\mathcal B|^2$.

This proves the estimate.

Consequently, for any threshold $h\ge1$,

$$
\#\{(p,t):d_{\mathcal B}(p,t)\ge h\}
\le
\frac{|\mathcal B|\,|P|+|\mathcal B|^2}{h^2}.
$$

This is the first place where the bucket approach gains something real: a bucket core $\mathcal B$ with large repeated incidence cannot support many marked labelled vertices unless those vertices lie in a small candidate container.

---

# 59. What the marked dual lemma does and does not prove

Write

$$
M_\tau=1+\frac{\tau}{X}.
$$

Each labelled vertex has at most $O(M_\tau)$ bucket incidences. If a bucket core $\mathcal B$ of size $K$ catches at least $h$ incidences from a labelled vertex, then that vertex lies in the container

$$
\mathcal V_h(\mathcal B)
=
\{(p,t):d_{\mathcal B}(p,t)\ge h\},
$$

whose size is bounded by

$$
|\mathcal V_h(\mathcal B)|
\ll
\frac{KN+K^2}{h^2}.
$$

In the saturated critical picture one expects roughly

$$
h\asymp M_\tau,\qquad K\asymp M_\tau^2.
$$

Then

$$
|\mathcal V_h(\mathcal B)|
\ll
N+M_\tau^2.
$$

This is a large saving relative to the full labelled universe of size $Ns$: it removes most of the label entropy. This is positive.

However, it does not by itself finish SBEE. If one had to enumerate arbitrary bucket cores $\mathcal B$, the entropy

$$
\log\binom{2\tau+1}{K}
\asymp
K\log\frac{\tau}{K}
$$

could still be too large in the critical window. Therefore the missing combinatorial step is not another large-sieve inequality. It is an **exposure/fingerprint lemma** saying that the bucket cores needed for high collision are generated from a small part of the transversal, rather than chosen arbitrarily.

This matches the container philosophy exactly: the arithmetic lemma supplies small residual containers once a bucket core is known; the remaining task is to build the bucket core with low fingerprint entropy.

---

# 60. Sharper remaining condition: bucket-core exposure

The SBEE gap can now be narrowed further.

**Bucket-core exposure condition, BCE.**  
Fix a threshold $\tau$ with $2\tau<X^2$ and a non-dominant labelled transversal $\Gamma$. If the cheap-pair count

$$
C_\Gamma(\tau)
$$

is close to the crude bucket-capacity upper bound, then there is a container exposure algorithm producing:

1. a fingerprint $F\subset\Gamma$;
2. a controlled family of bucket cores $\mathcal B_1,\ldots,\mathcal B_J$ generated from $F$;
3. thresholds $h_1,\ldots,h_J$;
4. residual labelled containers
   $$
   \mathcal V_{h_j}(\mathcal B_j)
   =
   \{(p,t):d_{\mathcal B_j}(p,t)\ge h_j\},
   $$

such that:

$$
\Gamma
\subset
F\cup\bigcup_{j\le J}\mathcal V_{h_j}(\mathcal B_j)\cup E_{\rm paid},
$$

where $E_{\rm paid}$ is charged by the complementary energy, and the total encoding entropy of

$$
F,\quad \mathcal B_1,\ldots,\mathcal B_J,\quad E_{\rm paid}
$$

is at most an arbitrarily small multiple of the energy already forced by thresholds away from the cheap region.

Together with the marked dual large-sieve lemma, BCE would imply the transversal bucket collision lemma from Section 53, hence SBEE.

This is sharper than the previous statement of the missing part:

- the arithmetic input is now an explicit proved lemma, Section 58;
- generic large sieve/larger sieve is no longer the bottleneck;
- the only remaining unknown is a container-style exposure lemma for high bucket collision.

This is a positive sign. We have moved from "prove a mysterious structured large sieve" to "prove a bucket-core fingerprint lemma, using the marked dual large-sieve estimate as the residual container bound."

---

# 61. Bucket-core extraction

The exposure condition can be localized by an elementary dyadic decomposition.

Fix $\tau$ with $2\tau<X^2$, and put

$$
M=M_\tau=1+\frac{\tau}{X}.
$$

For a transversal $\Gamma$, write

$$
\Omega(n)=\Omega_\Gamma(n)
$$

and

$$
C=C_\Gamma(\tau)
\le
\sum_{|n|\le\tau}\binom{\Omega(n)}2.
$$

Let $D$ be the crude bucket-occupancy bound

$$
D\asymp sL_X.
$$

For dyadic $k\le D$, define the bucket layer

$$
\mathcal B_k
=
\{n:k\le\Omega(n)<2k\}.
$$

Then

$$
C
\ll
\sum_{k\le D} k^2|\mathcal B_k|.
$$

Hence for some dyadic $k$,

$$
k^2|\mathcal B_k|
\gg
\frac{C}{\log D}.
$$

Let

$$
K=|\mathcal B_k|,
\qquad
I=Kk.
$$

Here $I$ is the incidence mass of this bucket layer, up to absolute constants. For each labelled vertex $v=(p,t)\in\Gamma$, define

$$
d_k(v)
=
\#\{n\in\mathcal B_k:n\equiv m_0+p_0t\pmod p\}.
$$

Then

$$
\sum_{v\in\Gamma}d_k(v)\asymp I.
$$

Dyadically decompose the vertices by $h\le M$:

$$
\Gamma_{k,h}
=
\{v\in\Gamma:h\le d_k(v)<2h\}.
$$

For some dyadic $h$,

$$
h|\Gamma_{k,h}|
\gg
\frac{I}{\log M}.
$$

Moreover

$$
\Gamma_{k,h}\subset
\mathcal V_h(\mathcal B_k),
$$

so by Section 58,

$$
|\Gamma_{k,h}|
\le
|\mathcal V_h(\mathcal B_k)|
\ll
\frac{KN+K^2}{h^2}.
$$

Combining the last two estimates gives the necessary condition

$$
\frac{Kk}{h\log M}
\ll
\frac{KN+K^2}{h^2},
$$

or

$$
kh
\ll
(N+K)\log M.
$$

This inequality is a useful diagnostic. A high-collision layer must fit simultaneously into:

1. the bucket-side lower bound $k^2K\gg C/\log D$;
2. the vertex-incidence lower bound $h|\Gamma_{k,h}|\gg Kk/\log M$;
3. the marked dual large-sieve upper bound $|\Gamma_{k,h}|\ll(KN+K^2)/h^2$.

Thus every dangerous configuration has a localized core

$$
(\mathcal B_k,\Gamma_{k,h},k,h)
$$

with explicit numerical constraints.

---

# 62. The genuinely hard regime after extraction

The extraction lemma also identifies when the remaining container problem is nontrivial.

If $k$ is substantially below the crude bucket capacity $D$, then

$$
C\ll k\,|\Gamma|M
$$

is already below the worst-case cheap-pair count, and the complementary layer-cake energy improves.

If $h$ is substantially below $M$, then the high-collision bucket layer is spread thinly across vertices. Such vertices cannot keep all their bucket incidences cheap across many thresholds, so again the layer-cake complement should pay after summing over $\tau$.

The hard regime is therefore the near-saturated one:

$$
k\asymp D,
\qquad
h\asymp M,
\qquad
K\asymp \frac{C}{D^2}.
$$

In the critical picture where $C$ is comparable to $N^2$, this gives

$$
K\asymp \frac{N^2}{s^2L_X^2}.
$$

Since the crude deterministic argument becomes sharp when

$$
M\asymp \frac{N}{sL_X},
$$

one gets

$$
K\asymp M^2.
$$

This explains exactly why Section 58 gives the right scale:

$$
|\mathcal V_M(\mathcal B)|
\ll
N+M^2.
$$

The arithmetic part has reached the correct size. The remaining question is purely container-theoretic:

> Can a near-saturated bucket core $\mathcal B$ of size $M^2$ be exposed from a fingerprint of entropy $o_\rho(R)$, rather than chosen from all $\binom{2\tau}{M^2}$ possibilities?

This is now the most precise current form of the final condition.

---

# 63. A fingerprint lemma for one bucket core

The near-saturated bucket-core problem has a purely combinatorial sublemma.

Let $G=(U,\mathcal B,E)$ be the incidence graph between a set $U$ of labelled vertices and a bucket core $\mathcal B$. Assume:

1. every $u\in U$ has degree at most $M$;
2. every bucket $b\in\mathcal B$ has degree at least $k$;
3. the total incidence satisfies
   $$
   |E|\asymp |\mathcal B|k.
   $$

Then there is a fingerprint

$$
F\subset U
$$

with

$$
|F|\ll \frac{|U|}{k}
$$

such that the bucket neighbourhood

$$
\mathcal B(F)=N(F)
$$

carries a positive proportion of all incidences:

$$
e(U,\mathcal B(F))
\gg
e(U,\mathcal B).
$$

**Proof.** Choose each vertex of $U$ independently with probability $c/k$, where $c>0$ is a sufficiently small absolute constant. Then

$$
\mathbb E|F|=\frac{c|U|}{k}.
$$

For a bucket $b$ of degree at least $k$,

$$
\mathbb P(b\in N(F))
\ge
1-\left(1-\frac ck\right)^k
\ge
c'
$$

for an absolute $c'>0$. Therefore

$$
\mathbb E\,e(U,N(F))
=
\sum_{b\in\mathcal B}\deg(b)\mathbb P(b\in N(F))
\ge
c' e(U,\mathcal B).
$$

After discarding an exceptional outcome if necessary, there is a choice of $F$ with both

$$
|F|\ll\frac{|U|}{k}
$$

and

$$
e(U,N(F))\gg e(U,\mathcal B).
$$

This proves the lemma.

In the near-saturated SBEE core, one has heuristically

$$
|U|\asymp N,\qquad k\asymp D=sL_X,\qquad M\asymp\frac{N}{D}.
$$

Thus

$$
|F|\ll \frac{N}{D}\asymp M.
$$

This is exactly the right scale: the core $\mathcal B$ has size about $M^2$, but it can be exposed by only $O(M)$ labelled vertices.

---

# 64. From fingerprint to residual container

Let $F$ be the fingerprint from Section 63 and put

$$
\mathcal B_F=N(F).
$$

Since each labelled vertex has at most $O(M)$ buckets,

$$
|\mathcal B_F|\ll |F|M.
$$

In the near-saturated case $|F|\ll M$, hence

$$
|\mathcal B_F|\ll M^2.
$$

The fingerprint lemma says that a positive proportion of the original core incidences land in $\mathcal B_F$. Dyadically pigeonhole the vertices again. There is a subfamily

$$
U_F\subset U
$$

and a threshold $h_F\gg M$ up to constants, in the saturated case, such that

$$
U_F\subset\mathcal V_{h_F}(\mathcal B_F)
$$

and $U_F$ carries a positive proportion of the core mass.

By the marked dual large-sieve lemma,

$$
|U_F|
\le
|\mathcal V_{h_F}(\mathcal B_F)|
\ll
\frac{|\mathcal B_F|N+|\mathcal B_F|^2}{h_F^2}.
$$

With

$$
|\mathcal B_F|\ll M^2,\qquad h_F\asymp M,
$$

this becomes

$$
|U_F|\ll N+M^2.
$$

Thus a positive chunk of the dangerous labelled vertices is covered by a residual container generated from only $O(M)$ fingerprint vertices.

Iterating this argument covers the near-saturated core by containers generated from total fingerprint size

$$
O(M\log N)
$$

if one insists on deterministic full coverage, and plausibly $O_\delta(M)$ if one allows a fixed uncovered proportion to be paid by the complementary energy at each stage.

This is a major improvement over arbitrary bucket-core enumeration:

$$
\log\binom{2\tau}{M^2}
\asymp
M^2\log\frac{\tau}{M^2}
$$

is replaced by roughly

$$
M\log(Ns)
$$

per exposed core.

---

# 65. Updated proof route for BCE

The preceding two sections suggest that BCE may be provable by the following deterministic-probabilistic container algorithm.

For each dyadic $\tau$:

1. extract a dangerous bucket layer $(\mathcal B_k,\Gamma_{k,h})$ as in Section 61;
2. if $k$ or $h$ is not near-saturated, charge the deficit through the layer-cake energy;
3. if $k\asymp D$ and $h\asymp M$, apply the fingerprint lemma to choose $F$ with $|F|\ll M$;
4. replace the arbitrary bucket core by the generated core $\mathcal B_F=N(F)$;
5. cover the corresponding vertex chunk by the residual container $\mathcal V_{cM}(\mathcal B_F)$ using Section 58;
6. iterate on the uncovered part.

The only quantitative point still to check is the entropy budget:

$$
M\log(Ns)
\stackrel{?}{\ll_\varepsilon}
\varepsilon R_{\rm forced}
$$

after summing over dyadic thresholds, profiles, and iterations.

This is much smaller than the previous missing budget

$$
M^2\log\frac{\tau}{M^2},
$$

so the sign is now genuinely positive. The remaining work is no longer to invent a new analytic number theory theorem; it is to close the energy-accounting inequality for the fingerprint iterations.

In other words, the final condition has been narrowed again:

> **FIE, fingerprint iteration entropy.** The iterative exposure scheme above has total encoding entropy $o_\varepsilon(R)$ in every non-dominant substantial SBEE profile.

The chain is now:

$$
\text{FIE}
\Longrightarrow
\text{BCE}
\Longrightarrow
\text{transversal bucket collision lemma}
\Longrightarrow
\text{SBEE}.
$$

Sections 58, 61, and 63 are unconditional components toward this chain.

---

# 66. Entropy budget check for the saturated regime

Now check the scale of the remaining FIE entropy.

Let

$$
W=|\Gamma|\asymp_\rho N,
\qquad
D=sL_X.
$$

In the hard saturated regime,

$$
M\asymp \frac{W}{D}.
$$

The bucket-capacity lower bound from Section 47 becomes effective at threshold

$$
\tau\asymp MX\asymp \frac{WX}{D}.
$$

At a fixed small constant fraction of this threshold, the cheap-pair capacity is still bounded away from all cross pairs, so the layer-cake energy forced at this scale is

$$
R_{\rm cap}
\asymp_\rho
\frac{W^2\tau^2}{X^4}
\asymp_\rho
\frac{W^4}{D^2X^2}.
$$

The fingerprint exposure from Sections 63--64 costs, per saturated core,

$$
E_{\rm fp}
\ll
M\log(Ns)
\asymp
\frac{W}{D}\log(Ns).
$$

Thus

$$
\frac{E_{\rm fp}}{R_{\rm cap}}
\ll_\rho
\frac{D X^2\log(Ns)}{W^3}.
$$

Using

$$
W\asymp N\asymp \frac{X}{\log X}
$$

gives

$$
\frac{E_{\rm fp}}{R_{\rm cap}}
\ll_\rho
\frac{D(\log X)^3\log(Ns)}{X}
\ll
\frac{D(\log X)^4}{X}.
$$

Therefore the **fingerprint/core-generation entropy** is absorbed by the forced bucket-capacity energy whenever

$$
D=sL_X=o\left(\frac{X}{(\log X)^4}\right).
$$

This includes the critical range

$$
s\asymp X^{1/2}\operatorname{polylog}X.
$$

If instead

$$
D\gg \frac{X}{(\log X)^4},
$$

then the label list is already enormous. Since

$$
s\ll \log X\sqrt R,
$$

we get

$$
R\gg \frac{s^2}{(\log X)^2}
\gg
\frac{X^2}{L_X^2(\log X)^{10}}.
$$

This is much larger than the crude entropy

$$
N\log s\ll X
$$

for large $X$, so the large-list regime is already paid without delicate bucket containers.

Hence the fingerprint-generation budget appears to close in all relevant regimes, up to harmless powers of $\log X$ from dyadic thresholds, profiles, and iteration. Those logarithms can be absorbed by replacing the displayed $(\log X)^4$ margin with a larger fixed power in the large-list split.

This is a strong positive sign, but it is not yet the whole FIE proof. The estimate above pays for generating the bucket core from a fingerprint. It does **not** automatically pay for freely choosing an arbitrary large subset of the residual container

$$
\mathcal V_{cM}(\mathcal B_F),
$$

whose size may still be $O(N)$ in the critical range.

The next formal task is to write the iteration carefully:

1. define the saturated-core extraction at each dyadic threshold;
2. apply the fingerprint lemma to cover a fixed positive fraction of the remaining saturated incidence mass;
3. avoid an $O(N)$ free-choice entropy inside the residual containers, either by recursively exposing further fingerprints or by proving a high-common-neighbour container bound relative to the fingerprint;
4. charge the discarded/non-saturated part by layer-cake energy;
5. sum the fingerprint and residual-container entropies over iterations and profiles using the estimate above.

So FIE has been narrowed, but not eliminated.

---

# 67. The remaining residual-container issue

The residual container supplied by Section 58 has size

$$
|\mathcal V_{cM}(\mathcal B_F)|\ll N+M^2.
$$

In the critical range, this can be as large as $O(N)$. Counting arbitrary transversals inside a set of $O(N)$ labelled vertices costs

$$
\exp(O(N)),
$$

which may be too large compared with

$$
R_{\rm cap}
\asymp
\frac{W^4}{D^2X^2}
$$

when $D$ is around $X^{1/2}\operatorname{polylog}X$.

Thus the next genuine obstacle is:

> Once a fingerprint $F$ has generated $\mathcal B_F=N(F)$, prove that low-energy residual choices inside $\mathcal V_{cM}(\mathcal B_F)$ are not arbitrary.

There are two plausible ways to do this.

## 67.1 Recursive exposure

Apply the same bucket-core extraction to the residual set inside $\mathcal V_{cM}(\mathcal B_F)$. If the residual choices still have high collision, expose another fingerprint. If not, the layer-cake complement pays.

This would make the container algorithm self-similar:

$$
\Gamma
\leadsto
F_1,\mathcal B_{F_1},\Gamma_1
\leadsto
F_2,\mathcal B_{F_2},\Gamma_2
\leadsto
\cdots.
$$

The required estimate is that the total fingerprint size remains

$$
o(R_{\rm cap}/\log(Ns)).
$$

## 67.2 High common-neighbour bound

Keep the incidence with the fingerprint itself, not just with its bucket union.

A vertex $v$ lying in $\mathcal V_{cM}(\mathcal B_F)$ has at least $cM$ bucket incidences with the union of bucket sets from $F$. Since two labelled vertices have at most one common bucket when $2\tau<X^2$, this says that $v$ is $\tau$-cheap to many members of $F$, up to bounded multiplicity.

So one should prove a common-neighbour estimate of the form

$$
\#\{v:v\text{ is }\tau\text{-cheap to at least }cM\text{ vertices of }F\}
\ll
o(N)
\text{energy-paid structured exceptions}.
$$

This would replace the crude residual container size $O(N)$ by a genuinely small or low-entropy set.

The high-common-neighbour estimate is now the sharpest local form of the remaining problem. It uses the same cheap-edge equation

$$
p\alpha-q\beta=p_0(t'-t),
$$

but with many fixed seed equations imposed simultaneously.

---

# 68. Recursive exposure scale

The residual-container issue can be attacked by recursion rather than by one-shot counting.

Suppose at some stage the remaining non-dominant substantial mass is

$$
W_j.
$$

Keep

$$
D=sL_X
$$

fixed for the dyadic profile. In the saturated regime for this residual mass,

$$
M_j\asymp \frac{W_j}{D}.
$$

The fingerprint needed at this stage has size

$$
\ll M_j,
$$

so its entropy is

$$
E_j
\ll
\frac{W_j}{D}\log(Ns).
$$

The bucket-capacity energy available at this residual scale is

$$
R_j
\asymp_\rho
\frac{W_j^4}{D^2X^2}.
$$

Thus

$$
\frac{E_j}{R_j}
\ll_\rho
\frac{D X^2\log(Ns)}{W_j^3}.
$$

Define the recursive stopping mass

$$
W_\ast
=
\left(DX^2\log(Ns)\right)^{1/3}.
$$

For every stage with

$$
W_j\gg W_\ast,
$$

the fingerprint entropy is a small fraction of the energy forced at that same scale. Since each successful exposure covers a fixed positive proportion of the saturated incidence mass, the total fingerprint entropy over a geometric iteration down to $W_\ast$ is controlled by the sum of the corresponding $R_j$.

At the stopping scale, encode the remaining seed crudely. Its entropy is

$$
E_\ast
\ll
W_\ast\log(Ns)
\asymp
\left(DX^2\log(Ns)\right)^{1/3}\log(Ns).
$$

Compare this with the initial saturated energy at $W\asymp N$:

$$
R_0
\asymp
\frac{N^4}{D^2X^2}
\asymp
\frac{X^2}{D^2(\log X)^4}.
$$

Thus

$$
E_\ast\ll o(R_0)
$$

provided

$$
D\ll \frac{X^{4/7}}{(\log X)^C}
$$

for a sufficiently large fixed $C$ absorbing the dyadic and iteration logarithms.

If

$$
D\gg \frac{X^{4/7}}{(\log X)^C},
$$

then the label list is already large. Since $D=sL_X$ and

$$
s\ll\log X\sqrt R,
$$

the base-list relation gives

$$
R
\gg
\frac{D^2}{L_X^2(\log X)^2}
\gg
\frac{X^{8/7}}{L_X^2(\log X)^{2+2C}},
$$

which dominates the crude entropy $N\log s\ll X$ for large $X$.

Therefore the recursive exposure scale appears to cover both:

1. the genuine short-list saturated regime $D\ll X^{4/7}/(\log X)^C$;
2. the large-list regime, paid directly by the base-list lower bound for $R$.

This substantially weakens the remaining FIE task. The high-common-neighbour estimate from Section 67 may not be necessary if the recursive exposure can be formalized with clean loss accounting.

The remaining formal bookkeeping is:

- define the residual mass $W_j$ and energy ledger after each exposure;
- prove that non-saturated layers at stage $j$ contribute enough layer-cake energy to pay their entropy;
- prove that saturated layers allow a fingerprint covering a fixed positive fraction of residual incidence mass;
- stop at $W_\ast$ and pay the residual seed crudely;
- sum over dyadic $\tau$, dyadic class-size profiles, and short lists.

At this point the route is no longer searching for a new external theorem. It is a finite, though delicate, container proof.

---

# 69. Formal FIE statement to prove next

The next pass should turn the preceding scale analysis into the following proposition.

**Proposition FIE, recursive fingerprint entropy.**  
Fix a dyadic substantial profile and a short list of size $s$. Put

$$
D=sL_X.
$$

After the large-list split

$$
D\gg \frac{X^{4/7}}{(\log X)^C},
$$

which is paid crudely by the base-list lower bound for $R$, assume

$$
D\le \frac{X^{4/7}}{(\log X)^C}.
$$

Let $\Gamma$ be a non-dominant substantial residual transversal of mass

$$
W\asymp_\rho N.
$$

Let

$$
R_{\rm cap}(W,D)
=
c_\rho\frac{W^4}{D^2X^2}
$$

be the bucket-capacity energy scale. Then the family of residual transversals whose cross energy is below this scale can be covered by containers with total encoding entropy

$$
o_\rho(R_{\rm cap}(W,D))
$$

plus terminal seed entropy

$$
O(W_\ast\log(Ns)),
\qquad
W_\ast=(DX^2\log(Ns))^{1/3}.
$$

Moreover,

$$
W_\ast\log(Ns)
=
o_\rho(R_{\rm cap}(N,D))
$$

in the above short-list range. Therefore the total entropy is

$$
o_\rho(R_{\rm cap}(N,D)).
$$

This proposition would imply FIE after summing dyadic thresholds and profiles, provided the non-saturated alternatives are charged by the layer-cake energy ledger.

## 69.1 Ingredients already available

The proof may use:

1. Section 58, marked dual large-sieve lemma;
2. Section 61, bucket-core extraction;
3. Section 63, one-core fingerprint lemma;
4. Section 68, recursive stopping scale.

These are unconditional at the level of the scratch argument.

## 69.2 Remaining bookkeeping lemmas

The proposition reduces to four finite lemmas.

**Lemma A, non-saturated deficit.**  
If, at residual mass $W_j$, every bucket layer has either

$$
k\le cD
$$

or every vertex layer has

$$
h\le cM_j,
\qquad
M_j=W_j/D,
$$

then the layer-cake complement contributes at least

$$
\gg_\rho
\frac{W_j^4}{D^2X^2}
$$

energy, up to dyadic logarithmic losses.

**Lemma B, saturated one-step exposure.**  
If a saturated layer exists, then there is a fingerprint

$$
F_j
$$

with

$$
|F_j|\ll M_j
$$

whose generated bucket core covers a fixed positive proportion of the saturated incidence mass.

**Lemma C, residual descent.**  
After exposing $F_j$, either the residual mass drops by a fixed factor

$$
W_{j+1}\le (1-c)W_j,
$$

or the part not captured by the generated core contributes the same scale of layer-cake energy.

**Lemma D, terminal seed.**  
When

$$
W_j\le W_\ast,
$$

the remaining residual choices can be encoded crudely with entropy

$$
O(W_\ast\log(Ns)).
$$

Lemmas B and D are essentially proved above. Lemmas A and C are the two pieces that still need to be written without handwaving.

---

# 70. Current assessment

The path is now positive but not closed.

Positive:

- the arithmetic obstruction has been replaced by the marked dual large-sieve lemma;
- arbitrary bucket-core entropy has been replaced by fingerprint entropy;
- the fingerprint entropy has the right scale;
- recursive exposure gives a plausible way to avoid the $O(N)$ residual-container entropy.

Still open:

- the exact layer-cake deficit inequality for non-saturated layers;
- the precise residual descent lemma after one fingerprint exposure;
- summing the dyadic logarithmic losses without damaging the $X^{4/7}$ split.

This is no longer a search problem. It is now a proof-engineering problem inside one custom container argument.
