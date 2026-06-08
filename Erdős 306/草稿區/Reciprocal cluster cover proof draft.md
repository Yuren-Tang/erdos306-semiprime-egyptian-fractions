# Reciprocal cluster cover proof draft

Back to [[Ambient-sensitive FIE proof draft]] and [[CP 02 The single remaining condition]].

This is the focused working note for the current smallest bottleneck inside
ambient-sensitive FIE.

The large historical scratch notes should now be treated as route history. The
active local problem is:

$$
\boxed{
\text{reciprocal-cluster covering for singular seeds}
}
$$

---

# 1. What Aristotle has closed

The finite path from persistent saturation to the seed-matrix formulation is now
credible.

Aristotle has produced no-sorry Lean files for:

1. `TwoCoreBookkeeping.lean`:
   - one generated core gives new-bucket capacity;
   - two saturated cores give a dense two-core bucket-pair graph;
   - high degree into a generated core gives many seed neighbours.
2. `SeededWitnessMatrix.lean`:
   - two-sided dependent-random-choice averaging;
   - witness matrices and mixed-defect / additive-rank-one equivalence;
   - row differences and common-divisor bookkeeping.
3. `ClusterCoverBookkeeping.lean`:
   - if every one-point extension of a fixed set $T$ is covered by a cluster,
     then the seed pool lies in $T$ plus the union of clusters containing $T$;
   - cardinal form: if at most $R$ clusters contain $T$ and each has size at
     most $L$, then $|F|\le |T|+RL$;
   - $k$-subset corollary producing the extension-cover hypothesis.
4. `AdaptiveClusterSelection.lean`:
   - defines cluster codegree, good $k$-subsets, and the all-covered
     alternative;
   - proves that all-covered plus low codegree gives the same cardinal cover
     bound;
   - proves the high-codegree incidence ledger
     $$
     \sum_{\substack{T\subset F\\ |T|=m}}\operatorname{codeg}(T)
     \le
     \sum_{\mathcal A}
     \#\{T\subset F\cap\mathcal A:|T|=m\};
     $$
   - proves the cardinal upper bound by cluster intersections.
5. `ClusterLineIncidence.lean`:
   - formalizes reciprocal-cluster incidence as integer line incidence;
   - proves the three-point determinant identity;
   - proves the three- and four-point factorable relations;
   - packages paper-language aliases for same-line seed triples and factorable
     relations.
6. `ReciprocalCRTProduct.lean`:
   - formalizes the four-seed line witness;
   - proves the base-difference identities
     $q_i x_i-q_4x_4=p\,a_i$;
   - proves the divisibility and modular residue forms;
   - packages the three local CRT congruences as `CRTProductHit`.
7. `ValidCRTLattice.lean`:
   - formalizes valid CRT hits, not just bare CRT congruence hits;
   - proves the bridge between four-seed line witnesses and valid hits in both
     directions;
   - proves the homogeneous lattice and scaling/ray properties;
   - defines primitive CRT rays and proves the basic scaling obstruction.

This means the purely finite infrastructure is no longer the main risk.

The remaining work is arithmetic plus one selection/structure step for
reciprocal clusters.

---

# 2. Current variables

Fix a reference seed

$$
f_\ast=(q_\ast,u_\ast),
\qquad
q_\ast\sim X.
$$

Let

$$
M_\tau=1+\frac{\tau}{X}
$$

be the short witness range. In the central case,

$$
M_\tau\asymp X^{1/2}
$$

up to logarithmic factors.

Let $k$ be the number of non-reference seeds chosen by the DRC step. The
singular-count threshold is

$$
M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}.
$$

At the central scale this requires

$$
k>3.
$$

Thus four non-reference seeds should be enough, after reserving fixed
logarithmic slack.

---

# 3. Regular uniqueness

For a seed tuple

$$
S=\{f_\ast,f_1,\ldots,f_k\},
\qquad
f_i=(q_i,u_i),
$$

put

$$
A_i=p_0(u_i-u_\ast).
$$

For each residual prime $p\sim X$, define the affine slice

$$
\Lambda_p(S)
=
\left\{
\mathbf b=(b_\ast,b_1,\ldots,b_k):
q_i b_i-q_\ast b_\ast+A_i\equiv0\pmod p
\right\},
$$

with

$$
|b_\ast|,|b_i|\le M_\tau.
$$

If two points of $\Lambda_p(S)$ lie in this short box, their difference gives a
short homogeneous kernel:

$$
q_i x_i-q_\ast x_\ast\equiv0\pmod p,
\qquad
\|\mathbf x\|_\infty\le2M_\tau.
$$

Hence, if no nonzero short homogeneous kernel exists, then

$$
\#(\Lambda_p(S)\cap[-M_\tau,M_\tau]^{k+1})\le1.
$$

This removes the residual polylogarithmic label multiplicity in the regular
case.

---

# 4. Singular seed tuples

A singular tuple has

$$
0<|x_\ast|\le2M_\tau,
\qquad
0<|x_i|\le2M_\tau,
\qquad
|y_i|\ll M_\tau,
$$

such that

$$
q_i x_i-q_\ast x_\ast=p\,y_i.
$$

For fixed $p,q_\ast,x_\ast$ and $x_i$, the congruence form gives

$$
q_i\equiv q_\ast x_\ast x_i^{-1}\pmod p.
$$

Since $q_i\in[X,2X]$ and $p\sim X$, each short $x_i$ gives only $O(1)$ possible
integers $q_i$.

Therefore singular seed prime tuples obey the global count

$$
\#\{\text{singular seed prime tuples}\}
\ll
N^2M_\tau^{k+1}(\log X)^{O(1)}.
$$

The free count is

$$
N^{k+1}.
$$

Thus singular tuples are globally sparse if

$$
M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}.
$$

This is a real saving, but it is not yet a fixed-pool selection theorem.

---

# 5. Reciprocal clusters

For fixed

$$
(p,q_\ast,x_\ast),
$$

define

$$
\mathcal A(p,q_\ast,x_\ast)
=
\left\{
q\sim X:
\exists\,0<|x|\le2M_\tau,\quad
qx\equiv q_\ast x_\ast\pmod p
\right\}.
$$

Equivalently,

$$
q\equiv q_\ast x_\ast x^{-1}\pmod p.
$$

Each cluster has size

$$
|\mathcal A(p,q_\ast,x_\ast)|\ll M_\tau.
$$

A singular non-reference seed tuple is contained in one of these clusters:

$$
(q_1,\ldots,q_k)\in \mathcal A(p,q_\ast,x_\ast)^k.
$$

Thus the singular hypergraph is contained in a union of complete $k$-graphs on
reciprocal clusters.

---

# 6. What HA ClusterCover gives

Let $F$ be the current fingerprint seed pool.

If every $k$-subset of $F$ is contained in some reciprocal cluster, and if for
some fixed $(k-1)$-subset $T\subset F$ at most $R$ clusters contain $T$, then HA
gives

$$
|F|\le |T|+R\,L,
\qquad
L=\max_{\mathcal A}|\mathcal A|\ll M_\tau.
$$

Therefore:

- if $|F|\asymp M_\tau$ and $R=O(1)$, $F$ can be encoded inside $O(1)$ clusters;
- encoding inside one cluster costs about $|F|\log M_\tau$ rather than
  $|F|\log N$, giving a central saving of order $\frac12|F|\log N$;
- if no such $T$ has controlled cluster codegree, then the high codegree itself
  must be treated as arithmetic structure.

So the active paper problem is not the finite cover lemma. It is the
reciprocal-cluster codegree/structure estimate.

---

# 7. Cluster codegree equation

Let

$$
T=\{q_1,\ldots,q_t\}
$$

be a set of seed primes. A cluster $\mathcal A(p,q_\ast,x_\ast)$ contains $T$
iff for every $j$ there is a short $x_j$ such that

$$
q_jx_j\equiv q_\ast x_\ast\pmod p.
$$

Thus for every pair $j,\ell$,

$$
p\mid q_jx_j-q_\ell x_\ell.
$$

The crude coefficient count is too weak: choosing $(x_j,x_\ell)$ gives
$O(M_\tau^2)$ possible large primes. At the central scale this is too large for
the HA cardinal cover bound.

The needed arithmetic improvement is:

**Reciprocal cluster codegree principle.**
For a non-structured set $T$ of at least three or four seed primes, the number
of reciprocal clusters containing $T$ is $O((\log X)^C)$, or at least small
enough that HA's cover lemma gives low entropy.

If this fails for many $T$, then many short congruences

$$
q_jx_j\equiv q_\ast x_\ast\pmod p
$$

hold simultaneously. This should force $T$ into a low-entropy rational family,
which is the structured exception.

---

# 8. Next mathematical target

The next proof attempt should target one of the following equivalent forms:

1. **Good codegree form:** find a $(k-1)$-subset $T\subset F$ with small
   reciprocal-cluster codegree, unless $F$ is structured.
2. **Cluster cover form:** if every $k$-subset of $F$ is singular, then $F$ is
   covered by $O((\log X)^C)$ reciprocal clusters, unless $F$ is structured.
3. **Intersection form:** large intersections among many reciprocal clusters
   force short-coefficient rational relations among their parameters.

This is the current smallest honest bottleneck I see.

It is plausible, but not closed.

---

# 9. Codegree as short-dilate intersection

For a fixed seed set

$$
T=\{q_1,\ldots,q_t\},
$$

define the local multiplicity at a residual prime $p$ by

$$
C_p(T)
=
\#\left\{
x_\ast:
0<|x_\ast|\le 2M_\tau,
\forall q\in T\ \exists\,0<|x_q|\le2M_\tau,
q x_q\equiv q_\ast x_\ast\pmod p
\right\}.
$$

Equivalently, with

$$
a_q(p)\equiv q_\ast q^{-1}\pmod p,
$$

the condition is

$$
x_\ast\in[-2M_\tau,2M_\tau]
\quad\text{and}\quad
a_q(p)x_\ast\in[-2M_\tau,2M_\tau]\pmod p
$$

for every $q\in T$.

Thus, up to harmless duplicate indexing of identical clusters,

$$
\operatorname{codeg}(T)
\le
\sum_{p\sim X} C_p(T).
$$

This is the cleaner arithmetic form:

$$
\text{many clusters through }T
\quad\Longleftrightarrow\quad
\text{many primes }p\text{ for which several modular dilates of a short interval intersect.}
$$

For random-looking ratios $a_q(p)$ one expects

$$
C_p(T)
\approx
M_\tau\left(\frac{M_\tau}{X}\right)^t.
$$

At the central scale $M_\tau\asymp X^{1/2}$ and $t=3$ or $4$, this is already
tiny per prime. Hence high codegree should be a genuine structure signal, not a
generic event.

---

# 10. Codegree as short gcd energy

There is an equivalent divisor form which may be better for proofs. If a
cluster contains $T$, then there are short coefficients

$$
0<|x_\ast|,|x_q|\le2M_\tau
\qquad(q\in T)
$$

such that

$$
p\mid qx_q-q_\ast x_\ast
\qquad(q\in T).
$$

Therefore

$$
\operatorname{codeg}(T)
\le
\sum_{\substack{0<|x_\ast|\le2M_\tau\\0<|x_q|\le2M_\tau}}
\omega_X\!\left(
\gcd_{q\in T}(qx_q-q_\ast x_\ast)
\right),
$$

where $\omega_X(n)$ counts prime divisors $p\sim X$ of $n$.

The needed arithmetic estimate can now be stated as a short gcd-energy
principle:

**Short gcd-energy principle.**
For non-structured $T$ with $|T|=t\ge3$ or $4$,

$$
\sum_{\substack{0<|x_\ast|\le2M_\tau\\0<|x_q|\le2M_\tau}}
\omega_X\!\left(
\gcd_{q\in T}(qx_q-q_\ast x_\ast)
\right)
\ll(\log X)^C
$$

or at least is small enough that HA's low-codegree cover lemma gives entropy
saving.

If this estimate fails, then many short vectors satisfy simultaneous
congruences

$$
qx_q-q_\ast x_\ast\equiv0\pmod p.
$$

For fixed $p$ and one seed $q$, this is a two-dimensional lattice in the
$(x_\ast,x_q)$ box. A large number of points in that box forces a much shorter
nonzero lattice vector by pigeonholing. Thus large $C_p(T)$ gives stronger
short-rational relations. If many different $p$ contribute with small
$C_p(T)$, the same phenomenon appears after summing the short gcd energy.

So the structure alternative should be expressible as:

$$
\text{high reciprocal-cluster codegree}
\Longrightarrow
\text{many unusually short rational relations among the }q/q_\ast.
$$

This is a better final target than the earlier vague phrase
"large cluster intersections".

---

# 11. External-tool check

I checked the nearby literature direction. Results on modular hyperbolas and
short interval products, such as Cilleruelo--Garaev bounds for

$$
xy\equiv\lambda\pmod p
$$

in short boxes, are conceptually relevant. However, their strongest directly
quoted small-box regimes are far below the central scale
$M_\tau\asymp X^{1/2}$. The right local tool here is therefore probably not a
black-box modular-hyperbola estimate. It should be a bespoke inverse statement
using the fixed prime ratios $q/q_\ast$, the simultaneous nature of $t\ge4$
seeds, and the fact that the residual prime $p$ varies.

References checked:

- Cilleruelo--Garaev, "Concentration points on two and three dimensional
  modular hyperbolas and applications", arXiv:1007.1526.
- Cilleruelo--Garaev, "Congruences involving product of intervals and sets with
  small multiplicative doubling modulo a prime and applications",
  arXiv:1404.5070.
- Bourgain--Garaev--Konyagin--Shparlinski, "On Congruences with Products of
  Variables from Short Intervals and Applications", arXiv:1203.0017.
- Garaev--Pardo--Shparlinski, "Binary and ternary congruences involving
  intervals and sets modulo a prime", arXiv:2410.03991.

---

# 12. New finite task for HA

The next Aristotle task should not ask it to prove the short gcd-energy
principle. Instead it should formalize the finite dichotomy around it:

$$
\text{good }k\text{-tuple}
\quad\text{or}\quad
\text{low-codegree cover}
\quad\text{or}\quad
\text{high-codegree incidence mass}.
$$

This is recorded in [[HA adaptive cluster selection prompt]].

---

# 13. After AdaptiveClusterSelection

The latest Aristotle run closes the finite trichotomy:

$$
\text{good }k\text{-tuple}
\quad\text{or}\quad
\text{low-codegree cover}
\quad\text{or}\quad
\text{high-codegree incidence mass}.
$$

Therefore the remaining paper-side statement can be narrowed to one arithmetic
incidence estimate for reciprocal clusters:

**Reciprocal cluster incidence principle.**
Let $F$ be a fingerprint seed pool. Unless $F$ is efficiently covered by
low-entropy reciprocal clusters, the high-codegree incidence mass satisfies

$$
\sum_{\substack{T\subset F\\ |T|=m}}\operatorname{codeg}(T)
\ll
\binom{|F|}{m}(\log X)^C
$$

for $m=k-1$, with enough logarithmic slack.

Together with `AdaptiveClusterSelection.lean`, this would produce a good
$k$-tuple or a structured low-entropy seed container.

---

# 14. Line-incidence reformulation

The congruence form has a more rigid integer-geometric form. Put

$$
c=q_\ast x_\ast,
\qquad
|x_\ast|\le 2M_\tau.
$$

If a cluster $\mathcal A(p,q_\ast,x_\ast)$ contains $q$, then there is a short
$x$ such that

$$
qx\equiv c\pmod p.
$$

Since $q,p\sim X$ and $|x|,|x_\ast|\ll M_\tau$, this is equivalent to an
integer identity

$$
qx=p\,y+c,
\qquad
|y|\ll M_\tau.
$$

For each seed prime $q$, define the short point set

$$
P_q
=
\{(y,z)\in\mathbb Z^2:
|y|\ll M_\tau,\ z=qx,\ 0<|x|\le2M_\tau\}.
$$

Then a reciprocal cluster containing $T$ is a line

$$
\ell_{p,c}:\quad z=p\,y+c
$$

with slope $p\sim X$ and intercept $c=q_\ast x_\ast$, meeting every $P_q$ for
$q\in T$.

Thus high codegree is not merely many modular coincidences. It is many
large-slope lines which are simultaneously incident to several highly
structured short point sets $P_q$.

For three seeds $q_1,q_2,q_3$ in one cluster, there are short $x_i,y_i$ such
that the three points

$$
(y_i,q_i x_i)
$$

are collinear. Hence

$$
\det
\begin{pmatrix}
1&y_1&q_1x_1\\
1&y_2&q_2x_2\\
1&y_3&q_3x_3
\end{pmatrix}
=0,
$$

equivalently

$$
q_1x_1(y_2-y_3)
+q_2x_2(y_3-y_1)
+q_3x_3(y_1-y_2)
=0.
$$

The coefficients are not arbitrary coefficients of size $O(M_\tau^2)$. They
have the factorable form

$$
x_i(y_j-y_\ell),
\qquad
|x_i|,|y_j-y_\ell|\ll M_\tau.
$$

For four seeds, the same line condition gives simultaneous factorable
relations, for example

$$
(q_1x_1-q_2x_2)(y_3-y_4)
=
(q_3x_3-q_4x_4)(y_1-y_2).
$$

This suggests a sharper inverse target:

**Short factorable-collinearity principle.**
If many reciprocal-cluster lines meet $P_q$ for many $q\in F$, then either
$F$ is covered by few reciprocal clusters, or the primes in $F$ satisfy many
short factorable linear relations

$$
\sum_i q_i\,x_i\,\Delta y_i=0,
\qquad
|x_i|,|\Delta y_i|\ll M_\tau,
$$

which should be charged as a low-entropy rational structure.

This is probably the most concrete current formulation of the last arithmetic
problem.

---

# 15. Next proof route

The route now has four layers:

1. Use `AdaptiveClusterSelection.lean` to reduce failure of a good tuple to
   high reciprocal-cluster incidence.
2. Convert reciprocal-cluster incidence into large-slope line incidence among
   the point sets $P_q$.
3. Use collinearity determinants to turn rich lines into short factorable
   relations among the seed primes.
4. Prove an inverse lemma: many such factorable relations imply a low-entropy
   structured seed family, compatible with the existing FIE exception ledger.

The remaining uncertainty is concentrated in layer 4. Layer 2 is algebraic, and
layer 3 is exact determinant bookkeeping.

---

# 16. Are we merely deferring?

This is a real risk, so it should be monitored explicitly.

The reductions so far are not all of the same type:

- `TwoCoreBookkeeping`, `SeededWitnessMatrix`, `ClusterCoverBookkeeping`,
  `AdaptiveClusterSelection`, and `ClusterLineIncidence` close finite or
  algebraic plumbing. They remove places where a hidden logical gap could live.
- The current open step is not another formal-plumbing lemma. It is an
  arithmetic estimate or inverse theorem.

So the honest status is:

$$
\text{finite logic closed}
\quad+\quad
\text{algebraic translations closed}
\quad+\quad
\boxed{\text{one arithmetic concentration theorem open}}.
$$

If future work only renames the boxed theorem, that would be deferral. The next
step must therefore either prove the concentration theorem, find a usable
known theorem, or identify a genuine obstruction.

---

# 17. Four-seed CRT product concentration

The four-seed case gives the sharpest current formulation.

Fix

$$
T=\{q_1,q_2,q_3,q_4\},
\qquad
q_i\sim X
$$

and suppose one reciprocal-cluster line

$$
z=p\,y+c,
\qquad
c=q_\ast x_\ast,
$$

meets all four point sets $P_{q_i}$. Thus

$$
q_i x_i=p\,y_i+c
\qquad(1\le i\le4)
$$

with all $x_i,y_i$ short. Use $q_4$ as the base and put

$$
a_i=y_i-y_4
\qquad(1\le i\le3).
$$

Subtracting the fourth equation gives

$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3).
$$

If $a_i=0$, then $q_i x_i=q_4x_4$, impossible for distinct primes
$q_i,q_4$ when $0<|x_i|,|x_4|<X$. Hence $a_i\ne0$ and $a_i$ is invertible
modulo $q_i$.

Therefore

$$
p
\equiv
-q_4x_4a_i^{-1}
\pmod {q_i}
\qquad(1\le i\le3).
$$

Let

$$
Q=q_1q_2q_3.
$$

For each short quadruple

$$
(x_4,a_1,a_2,a_3),
\qquad
0<|x_4|,|a_i|\ll M_\tau,
$$

CRT gives at most one residue class

$$
p\equiv x_4 B(a_1,a_2,a_3)\pmod Q,
$$

where $B$ is the CRT combination of the three reciprocal residues

$$
-q_4a_i^{-1}\pmod {q_i}.
$$

Since $Q\asymp X^3$ and $p$ is required to lie in an interval $I=[X,2X]$ of
length $\asymp X$, the expected number of hits is

$$
\#\{x_4,a_1,a_2,a_3\}\frac{|I|}{Q}
\asymp
\frac{M_\tau^4X}{X^3}.
$$

At the central scale $M_\tau\asymp X^{1/2}$ this is

$$
O(1).
$$

Thus the actual four-seed codegree target is:

**Four-seed CRT concentration bound.**
For non-structured seed primes $q_1,q_2,q_3,q_4$,

$$
\#\left\{
(x,a_1,a_2,a_3):
0<|x|,|a_i|\ll M_\tau,\
xB(a_1,a_2,a_3)\bmod Q\in[X,2X]
\right\}
\ll(\log X)^C.
$$

This is no longer a vague inverse problem. It is an interval-product
concentration estimate modulo the squarefree composite modulus
$Q=q_1q_2q_3$.

High codegree means that the product of a short interval in $x$ with the CRT
reciprocal box

$$
\mathcal B_T
=
\{B(a_1,a_2,a_3):0<|a_i|\ll M_\tau\}
\subset\mathbb Z/Q\mathbb Z
$$

has abnormal concentration in the short interval $[X,2X]$ modulo $Q$.

This is now the precise sharp point.

---

# 18. Why four seeds matter

The same CRT count explains why two or three seeds are not enough.

With $r$ non-base seeds, the modulus is about $X^r$, while the raw variable
volume is

$$
X\,M_\tau^{r+1}
$$

including the residual interval length $X$. At $M_\tau\asymp X^{1/2}$, the
expected count is

$$
\frac{X\,M_\tau^{r+1}}{X^r}
=
X^{1+(r+1)/2-r}
=
X^{(3-r)/2}.
$$

Thus:

- $r=2$ gives expected size $X^{1/2}$, too large;
- $r=3$ gives expected size $O(1)$;
- equivalently, one needs four total seed primes in the cluster-codegree test.

This matches the earlier condition $k>3$ from the global singular-tuple count,
but now it appears from a local CRT product calculation.

---

# 19. New arithmetic endpoint

The next non-formal theorem should be stated as:

**Reciprocal CRT Product Inverse Theorem.**
Let $q_1,q_2,q_3,q_4\sim X$ be distinct seed primes and
$M\le X^{1/2}(\log X)^A$. Define $Q=q_1q_2q_3$ and
$\mathcal B_T$ as above. Then either

$$
\#\{(x,B):0<|x|\le M,\ B\in\mathcal B_T,\ xB\bmod Q\in[X,2X]\}
\ll(\log X)^C,
$$

or the quadruple $(q_1,q_2,q_3,q_4)$ lies in a low-entropy rational structured
family compatible with the FIE exception ledger.

This theorem would combine with the HA finite pipeline to finish the
reciprocal-cluster covering step.

Compared with the previous short gcd-energy statement, this is sharper because
it uses all four seeds at once and exposes the exact CRT product structure.

---

# 20. Valid CRT hits, not only product hits

The latest Aristotle run closes the algebraic bridge to local CRT product hits.
This exposed an important correction: a bare `CRTProductHit` is a necessary
condition, not yet the exact cluster-witness condition.

Given

$$
p\,a_i\equiv -q_4x_4\pmod {q_i},
$$

one must also define

$$
x_i=\frac{p\,a_i+q_4x_4}{q_i}
$$

and require

$$
0<|x_i|\le M_\tau.
$$

Thus the correct endpoint is a **valid CRT product hit**:

$$
\begin{aligned}
&0<|x_4|,|a_i|,|x_i|\le M_\tau,\\
&q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3),\\
&p\in[X,2X].
\end{aligned}
$$

This matters. A quick finite experiment showed that the bare CRT condition has
large false-positive families, for instance near the diagonal $p=q_4$. In that
case the short residue choice can give $a_i=-x_4$, but then

$$
x_i=\frac{q_4(-x_4)+q_4x_4}{q_i}=0,
$$

which is not a legal singular witness.

After enforcing $0<|x_i|\le M_\tau$, random dyadic tests at
$X=200,\ldots,20000$ gave non-diagonal counts of size $0,2,4,6$ in typical
samples, consistent with the expected $O(1)$ or polylogarithmic bound.

This is a useful warning: the arithmetic theorem should not be stated only for
the product set $x\mathcal B_T$. It should be stated for valid quotient hits,
or else the product-set theorem must explicitly exclude and charge the invalid
quotient fibres.

---

# 21. Homogeneous lattice and primitive rays

For fixed $p$, a valid hit is a short integer point in the homogeneous lattice

$$
L_p(T)
=
\left\{
(x_4,x_1,x_2,x_3,a_1,a_2,a_3):
q_i x_i-q_4x_4=p\,a_i,\ 1\le i\le3
\right\}.
$$

The equations are homogeneous in the short variables. Hence if

$$
(x_4,x_1,x_2,x_3,a_1,a_2,a_3)
$$

is a valid hit for $p$, then any integer multiple $\lambda$ is another hit as
long as all coordinates stay within the short box and remain nonzero.

This explains the small multiplicities seen in the experiments: hits often
come in sign pairs and sometimes in short scalar progressions, for example
primitive vector plus its double.

Therefore the next endpoint should count primitive rays:

**Primitive valid CRT concentration.**
For non-structured seed primes $q_1,q_2,q_3,q_4$, the number of primitive rays
in $L_p(T)$ meeting the short box, summed over residual primes $p\sim X$, is
$O((\log X)^C)$. The nonprimitive multiples then cost at most a divisor-type
factor, provided very small primitive rays are charged as structured
exceptions.

This is now a sharper and safer target than the bare product-concentration
statement.

---

# 22. New HA direction

The next HA task should be a larger interface package:

1. define valid CRT product hits with the quotient variables $x_i$;
2. prove equivalence between four-seed line witnesses and valid CRT hits;
3. prove valid CRT hits imply `CRTProductHit`;
4. define the homogeneous lattice predicate $L_p(T)$;
5. prove the integer-scaling/ray property;
6. optionally define primitive hits by absence of a common divisor and prove
   basic monotonicity under scaling.

This lets HA thicken the entire algebraic and lattice interface, while the
remaining human-side theorem is the primitive valid CRT concentration bound.

---

# 23. Reference anchor cannot be dropped

The latest Aristotle run closes the valid but **unanchored** lattice interface.
This revealed a further correction.

The original reciprocal cluster is not just an arbitrary line through four seed
point sets. Its intercept has the special form

$$
c=q_\ast x_\ast,
\qquad
0<|x_\ast|\le M_\tau.
$$

Equivalently, the line must also pass through the reference seed point. The
true equations are

$$
q_i x_i-q_\ast x_\ast=p\,y_i
\qquad(1\le i\le4).
$$

When we normalize by the fourth seed, putting

$$
a_i=y_i-y_4
\qquad(1\le i\le3),
$$

we get the valid base equations

$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3),
$$

but we must also keep the reference-anchor equation

$$
q_4x_4-q_\ast x_\ast=p\,y_4.
$$

Dropping this last equation gives a necessary condition, not an equivalent
cluster condition.

This also fixes the heuristic count. The unanchored valid lattice has constant
expected count at the central scale. The anchored lattice has volume heuristic

$$
X\left(M_\tau\left(\frac{M_\tau}{X}\right)^4\right)
=
\frac{M_\tau^5}{X^3}.
$$

At $M_\tau\asymp X^{1/2}$ this is

$$
X^{-1/2},
$$

which matches the original global singular-sparsity calculation.

A small numerical check supports this: once the reference anchor is enforced,
random dyadic samples at $X=500,\ldots,10000$ usually have no hits; the rare
hits appear as a single sign pair.

---

# 24. Anchored primitive lattice

The exact lattice target should therefore be the anchored lattice

$$
L_p^{\mathrm{anch}}(q_\ast;T)
=
\left\{
(x_\ast,x_1,x_2,x_3,x_4,y_4,a_1,a_2,a_3):
\begin{array}{l}
q_i x_i-q_4x_4=p\,a_i,\quad 1\le i\le3,\\
q_4x_4-q_\ast x_\ast=p\,y_4
\end{array}
\right\}.
$$

All variables are short, the $x$-coordinates are nonzero, and for distinct seed
primes the difference variables $a_i$ and $y_4$ are automatically nonzero in the
legal short range.

The final local theorem should be:

**Reference-anchored primitive lattice concentration.**
For non-structured

$$
(q_\ast,q_1,q_2,q_3,q_4),
\qquad
q_\ast,q_i\sim X,
$$

the number of primitive rays in

$$
L_p^{\mathrm{anch}}(q_\ast;T)
$$

meeting the short box, summed over residual primes $p\sim X$, is
$O((\log X)^C)$, with enough slack for the HA finite cover pipeline.

This is stronger and more faithful than the unanchored primitive-ray theorem.
It is now the best current statement of the remaining arithmetic problem.

---

# 25. Next HA direction

The next Aristotle task should formalize the anchored interface:

1. define the anchored cluster witness with reference seed $q_\ast$;
2. define the anchored normalized lattice with variables
   $(x_\ast,x_1,x_2,x_3,x_4,y_4,a_1,a_2,a_3)$;
3. prove the bidirectional bridge between the two formulations;
4. prove anchored hit implies the existing unanchored `ValidCRTProductHit`;
5. prove the four local CRT congruences, including the reference congruence
   modulo $q_4$;
6. prove homogeneous scaling and primitive-ray bookkeeping for the anchored
   lattice.

This is a good larger HA task: it is all exact algebra and logic, while the
remaining theorem is the anchored primitive concentration estimate.

---

# 26. Anchored short-dilate form

The anchored condition has a simpler direct form.

For fixed

$$
T=\{q_1,q_2,q_3,q_4\}
$$

and reference $q_\ast$, define

$$
C_p^{\mathrm{anch}}(T)
=
\#\left\{
x_\ast:
0<|x_\ast|\le M_\tau,\
\forall i\ \exists\,0<|x_i|\le M_\tau,\
q_i x_i\equiv q_\ast x_\ast\pmod p
\right\}.
$$

Equivalently,

$$
x_i
\equiv
q_\ast q_i^{-1}x_\ast
\pmod p
$$

and $x_i$ must be represented by a nonzero integer in the short interval.

Then the anchored cluster codegree is bounded by

$$
\operatorname{codeg}_{q_\ast}(T)
\le
\sum_{p\sim X} C_p^{\mathrm{anch}}(T).
$$

At the central scale, the random model gives

$$
C_p^{\mathrm{anch}}(T)
\approx
M_\tau\left(\frac{M_\tau}{X}\right)^4
=
X^{-3/2},
$$

so after summing over $p\sim X$ the expected count is $X^{-1/2}$.

This is the cleanest current formulation:

**Anchored short-dilate concentration theorem.**
For non-structured

$$
(q_\ast,q_1,q_2,q_3,q_4),
$$

one has

$$
\sum_{p\sim X} C_p^{\mathrm{anch}}(T)
\ll(\log X)^C.
$$

This theorem immediately implies the required reciprocal-cluster codegree
bound.

---

# 27. Anchored gcd-energy form

The same condition can be written as a short gcd-energy count. A solution is a
short vector

$$
\mathbf x=(x_\ast,x_1,x_2,x_3,x_4)
$$

such that a residual prime $p\sim X$ divides every

$$
n_i=q_i x_i-q_\ast x_\ast
\qquad(1\le i\le4).
$$

Since

$$
|n_i|\ll XM_\tau,
$$

and $M_\tau<X$, the integer $\gcd(n_1,n_2,n_3,n_4)$ has at most one prime
divisor in $[X,2X]$ up to harmless endpoint constants.

Thus the same theorem is:

**Anchored primitive gcd-energy theorem.**
For non-structured seed primes,

$$
\#\left\{
\text{primitive short }\mathbf x:
\exists p\sim X,
p\mid q_i x_i-q_\ast x_\ast\ (1\le i\le4)
\right\}
\ll(\log X)^C.
$$

If a common large prime exists, write

$$
q_i x_i-q_\ast x_\ast=p\,y_i.
$$

Eliminating $p$ between $i$ and $j$ gives the factorable relation

$$
q_i x_i y_j
-q_j x_j y_i
q_\ast x_\ast (y_i-y_j)
=0.
$$

All coefficients have factorable size $O(M_\tau^2)$. Hence failure of the
anchored gcd-energy theorem should force many short factorable ternary
relations among the seed primes. This is the likely structured exception.

---

# 28. Current proof avenues

There are now two plausible proof routes for the remaining arithmetic theorem:

1. **Short-dilate large sieve.** Bound the sum of
   $C_p^{\mathrm{anch}}(T)$ directly as an intersection of four modular dilates
   of a short interval.
2. **Primitive gcd energy.** Count primitive short vectors for which
   $\gcd_i(q_i x_i-q_\ast x_\ast)$ has a prime divisor in $[X,2X]$, and show
   that many such vectors force a low-entropy family of factorable ternary
   relations.

The first route is cleaner if a suitable large-sieve or modular-interval tool
exists. The second route is more bespoke but exposes the structured exception
explicitly.
