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
