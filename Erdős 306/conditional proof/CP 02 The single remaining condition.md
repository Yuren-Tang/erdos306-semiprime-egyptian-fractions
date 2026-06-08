# The single remaining condition

Back to [[CP 00 Navigation]].

This note states the only unfinished mathematical input used in [[CP 01 Conditional theorem]]. The condition is deliberately local: it concerns one dyadic prime block and only the non-dominant substantial-label case inside the single-block counting theorem.

Everything outside this condition is treated in [[CP 03 Lemma bank]].

---

# 1. Local setup

Let
\[
P\subset [X,2X]
\]
be a pruned Irving-good block of primes, and put
\[
N=|P|,\qquad
\sigma_P^2=\sum_{\substack{p<q\\p,q\in P}}\frac1{p^2q^2}.
\]
For a residue assignment
\[
a_P=(a_p)_{p\in P},\qquad a_p\in\mathbb F_p,
\]
let \(H_{pq}(a)\in(-pq/2,pq/2]\) be the CRT representative satisfying
\[
H_{pq}(a)\equiv a_p\pmod p,\qquad
H_{pq}(a)\equiv a_q\pmod q.
\]
Define the internal energy
\[
Q_P(a)=
\sum_{\substack{p<q\\p,q\in P}}
\left(\frac{H_{pq}(a)}{pq}\right)^2.
\]

Fix an energy level \(R\ge1\). In the single-block proof, low energy \(Q_P(a)\le R\) gives a cutoff
\[
B=A X\log X\sqrt R
\]
and, after choosing a regular base vertex \(p_0\), a short list
\[
\mathcal L=\{n\in[-B,B]:n\equiv a_{p_0}\pmod {p_0}\},
\qquad
|\mathcal L|\ll 1+\log X\sqrt R.
\]
Most vertices are covered by labels in \(\mathcal L\):
\[
C_m=\{p\in P:a_p\equiv m\pmod p\},\qquad m\in\mathcal L.
\]

Let
\[
L_X=1+\frac{\log(B+X^2+2)}{\log X}.
\]
A class \(C_m\) is called substantial if
\[
|C_m|\ge C_0L_X
\]
and tiny otherwise.

The dominant case is when some \(m\) has
\[
|C_m|\ge (1-\rho)N
\]
for fixed small \(\rho>0\). Dominant and tiny-exception cases are handled by Irving-good majority correction. The only missing case is:

- no dominant class;
- substantial classes carry a positive proportion of the covered vertices.

---

# 2. Cross-label energy in the missing case

For two different labels \(m\ne m'\) and classes
\[
A=C_m,\qquad B=C_{m'},
\]
write \(H_{pq}^{m,m'}\) for the CRT representative satisfying
\[
H_{pq}^{m,m'}\equiv m\pmod p,\qquad
H_{pq}^{m,m'}\equiv m'\pmod q.
\]
The already-proved divisor-energy lemma gives
\[
\sum_{p\in A,q\in B}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2
\gg
M\min\left(1,\frac{M^2}{X^4L_X^4}\right),
\qquad
M=|A||B|,
\]
provided both classes are substantial.

For a label partition \((C_m)_{m\in\mathcal L}\), define its substantial cross-label energy
\[
S_{\rm sub}(C_\bullet)
=
\sum_{\substack{m\ne m'\\ C_m,C_{m'}\ {\rm substantial}}}
\sum_{p\in C_m,q\in C_{m'}}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2.
\]

---

# 3. Condition SBEE

**Condition SBEE, Single-Block Energy-Entropy condition.**  
For every \(\varepsilon>0\) and every sufficiently small fixed \(\rho>0\), there are constants \(C_0,A,C_\varepsilon\) such that the following holds for every sufficiently large pruned Irving-good block \(P\subset[X,2X]\).

Fix \(R\ge1\), a short label list \(\mathcal L\) arising from the base-list construction above, and a dyadic class-size profile for substantial classes. Consider all residue assignments \(a_P\) satisfying:

1. \(Q_P(a_P)\le R\);
2. at least \((1-o_\rho(1))N\) vertices are covered by labels in \(\mathcal L\);
3. no label is dominant:
   \[
   \max_{m\in\mathcal L}|C_m|<(1-\rho)N;
   \]
4. the union of substantial classes has size at least \(\rho N\);
5. the substantial class sizes lie in the prescribed dyadic profile.

Tiny classes and uncovered vertices are included in this counting problem. They may be encoded separately, but in the non-dominant case they should **not** be assumed to be paid by Irving-good majority correction unless a genuinely near-dominant reference class is present. Thus let \(T_{\rm aux}(a)\) denote whatever additional weighted cross-energy or container cost is assigned to tiny/uncovered data inside the non-dominant counting argument.

Then, for every \(T\ge0\), the number of such assignments with
\[
S_{\rm sub}(C_\bullet)+T_{\rm aux}(a)\le T
\]
is at most
\[
C_\varepsilon
\exp\{\varepsilon(R+T)\}.
\]

Equivalently, after summing over all dyadic profiles, all short lists \(\mathcal L\), and all substantial/tiny decompositions, the total contribution of the non-dominant substantial case to the single-block level set is
\[
\ll_\varepsilon
e^{\varepsilon R}.
\]
This equivalence uses the intended energy accounting
\[
S_{\rm sub}(C_\bullet)+T_{\rm aux}(a)\ll Q_P(a)\le R.
\]

This is the exact missing step. It should be read as a **single-block weighted counting/container statement**, not merely as the pointwise pairwise divisor-energy lower bound. The pairwise lower bound is one input, but the condition also needs to count how many labelled vertex partitions can keep all cross-label weights small.

It says that the cross-label divisor-energy mechanism pays for:

- the choice of substantial labels;
- the choice of substantial vertex classes;
- dyadic class-size bookkeeping;
- the remaining tiny labels and residues, without pretending that a non-dominant largest class is already dense enough for Irving majority correction.

## 3.1 Current refined bottleneck

The working scratch file [[SBEE dyadic proof draft]] and the second Aristotle package now narrow the internal SBEE bottleneck further.

Several finite-combinatorial inputs in the bucket route have been formalized in Lean, outside the main conditional theorem package:

- Fisher counting / marked dual large-sieve:
  $$
  \sum_{p,t}\binom{d_{\mathcal B}(p,t)}2\le \binom{|\mathcal B|}2.
  $$
- Greedy fingerprint exposure: a fingerprint of size $r$ captures at least an $r/|U|$ fraction of incidence mass.
- Generated-core and high-multiplicity container bounds:
  $$
  |\mathcal V_h(\mathcal B)|\,h(h-1)\ll |\mathcal B|^2.
  $$
- Repeated exposure budget:
  $$
  |\mathrm{Idx}|\,m\le |U|M.
  $$
- Common-neighbour mass and rank-one rectangle-defect aliases.

Thus the remaining bottleneck is no longer the first-level finite exposure lemma itself. It is the recursive and arithmetic use of that exposure inside the non-dominant substantial SBEE counting problem.

The arithmetic large-sieve-looking part is reduced to a deterministic marked dual estimate: for a bucket core $\mathcal B$ and incidence threshold $h$, the candidate labelled vertices satisfying

$$
d_{\mathcal B}(p,t)\ge h
$$

lie in a container of size

$$
\ll
\frac{|\mathcal B|N+|\mathcal B|^2}{h^2}.
$$

The current scratch reduction sharpens the remaining subcondition to a fingerprint-iteration entropy check:

$$
\text{FIE}
\Longrightarrow
\text{BCE}
\Longrightarrow
\text{SBEE}.
$$

The present scale check shows that the fingerprint/core-generation entropy is smaller than the bucket-capacity energy by a factor $\ll sL_X(\log X)^4/X$ in the saturated short-list regime, while the complementary large-list regime is already paid by the base-list lower bound on $R$. The remaining FIE issue is the residual-container entropy: after a fingerprint generates a bucket core, one must still show that low-energy choices inside the resulting candidate container are recursively exposed with their reduced ambient universe recorded. A one-parameter peeling tree is not enough, because many terminal leaves would otherwise contribute total entropy of order $W\log(Ns)$.

Thus the current scratch formulation, now isolated in [[Ambient-sensitive FIE proof draft]], uses states $(W,Y)$, where $W$ is residual mass and $Y$ is the current ambient universe size, and the potential

$$
\mathcal P(W,Y)
=
A\frac{W^4}{D^2X^2}
+
B\,W\log\frac{eY}{W},
\qquad D=sL_X.
$$

In the scratch file this is now organized as Proposition FIE with four bookkeeping lemmas: non-saturated deficit, saturated one-step exposure, ambient-sensitive residual descent, and terminal encoding by telescoping ambient entropy. The non-saturated deficit is essentially proved up to dyadic logarithmic constants. The saturated one-step exposure is now supported by the Lean-formalized fingerprint/container infrastructure. The remaining paper proof is the log-corrected ambient-sensitive residual descent:

1. expose a fingerprint;
2. capture a chunk of size
   $$
   \theta W,\qquad \theta\ge(\log X)^{-A};
   $$
3. place that chunk inside a fingerprint-determined container of size
   $$
   Y_1\ll \left(N+\frac{W^2}{D^2}\right)(\log X)^A;
   $$
4. recurse on the captured branch with ambient $Y_1$ and on the complement with ambient $Y$;
5. use the decrease of
   $$
   \mathcal P(W,Y)
   $$
   to pay the parent fingerprint entropy and terminal leaves;
6. prove the global saving form: the cumulative ambient entropy drops reduce the initial crude entropy $N\log s$ to $o(R)$, except in regimes already paid by non-saturated energy or by the base-list lower bound.

The logarithmic loss only changes the large-list split by a fixed power of $\log X$. This ambient-sensitive formulation is the current sharp version of the one remaining internal proof task.

The focused draft further refines this into two nested savings:

1. **First-capture ambient saving**, which removes the main $N\log D$ label-list entropy in the large-list side of the central range.
2. **Polylog-ambient compression**, still to be proved, which must remove the remaining $N\log\log X$ entropy after the ambient has been reduced to $N(\log X)^K$.

The second point has now been sharpened further. The average ambient
multiplicity $Y/N$ is not by itself the effective bucket parameter for a
non-product residual container. Instead, after one generated core
$\mathcal C_0$, the relevant finite statement is the new-bucket capacity bound

$$
\Delta_{\rm new}(A_h(\mathcal C_0);\mathcal C_0)
\le
\frac{|\mathcal C_0|}{h},
$$

where $A_h(\mathcal C_0)$ is the set of vertices incident to at least $h$
buckets of $\mathcal C_0$. If a second saturated core $\mathcal C_1$ persists,
then the residual vertices produce a polylog-dense two-core graph

$$
G_\Gamma(\mathcal C_0,\mathcal C_1)
\subset
\mathcal C_0\times\mathcal C_1.
$$

Thus the current paper-side bottleneck is a **two-core rectangle inverse**:
many low-energy bucket rectangles must either charge the energy ledger or force
rank-one / near-dominant structure. This is smaller and more precise than the
original SBEE statement, but it is still a genuine mathematical step rather
than a purely formal bookkeeping issue.

The inverse statement must remember that the cores are generated by
fingerprints, $\mathcal C_i=N(F_i)$, not arbitrary bucket sets. A vertex captured
inside $A_h(N(F_i))$ is cheap to at least $h$ distinct seed vertices of $F_i$.
Thus the actual arithmetic input is a two-fingerprint common-neighbour inverse;
the two-core rectangle graph is its finite counting shadow.

The focused draft now packages this as a seeded witness-matrix inverse. A
two-sided dependent-random-choice extraction fixes bounded seed tuples
$S_0,S_1$ while preserving a large polylogarithmic common residual
neighbourhood. For every residual vertex $v=(p,t)$ and seed $f=(q,u)$, the
cheap edge has a unique short bucket witness

$$
n_{v,f}=m_t+p\alpha_{v,f}=m_u+q\beta_{v,f},
$$

or

$$
p\alpha_{v,f}-q\beta_{v,f}=p_0(u-t).
$$

The remaining arithmetic lemma is that nonzero mixed defects

$$
n_{v,f}-n_{v,f'}-n_{v',f}+n_{v',f'}
$$

must produce enough energy, unless a large submatrix has zero mixed defect and
hence additive rank one. This is now the sharpest local form of the
polylog-ambient compression problem.

Equivalently, after fixing a reference seed $f_\ast=(q_\ast,u_\ast)$, the row
differences

$$
D_v(f)=n_{v,f}-n_{v,f_\ast}
$$

all share the large prime divisor $p_v$ attached to the residual vertex
$v=(p_v,t_v)$, while also lying in the bounded seed-generated progression

$$
D_v(f)=p_0(u_f-u_\ast)+q_f b_f-q_\ast b_\ast,
\qquad |b_f|,|b_\ast|\ll M_\tau.
$$

Thus the current smallest arithmetic bottleneck is a large-prime gcd bound for
bounded seed progressions, with rank-one / low-entropy structure as the inverse
alternative.

Equivalently, for a fixed seed tuple $S=\{f_\ast,f_1,\ldots,f_k\}$ one must
count affine lattice slices

$$
\Lambda_p(S)=
\left\{
(b_\ast,b_1,\ldots,b_k):
q_i b_i-q_\ast b_\ast+p_0(u_i-u_\ast)\equiv0\pmod p
\right\}.
$$

A determinant-size lattice count gives the right heuristic for these
codimension-$k$ slices. The actual regular side is simpler: the singular
alternative is a short homogeneous kernel

$$
q_i x_i-q_\ast x_\ast\equiv0\pmod p,
$$

which must be shown to have low entropy or to force rank-one / near-dominant
structure.

The regular side is even cleaner: if two points of $\Lambda_p(S)$ lie in the
short box, their difference is such a short homogeneous kernel. Hence, in the
absence of a short kernel, each residual prime $p$ has at most one candidate
witness pattern and therefore no residual polylogarithmic label multiplicity.
The final local lemma is the corresponding seed singularity bound for short
kernel vectors. The number $k$ of non-reference seeds must be chosen large
enough that simultaneous short approximation is sparse, for instance

$$
M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}.
$$

This is why the next DRC step should extract several seed neighbours, not merely
one. In the central case $M_\tau\asymp X^{1/2}$, four non-reference seeds are
enough up to fixed logarithmic slack.

The direct count is as follows. For fixed $p,q_\ast,x_\ast$, each seed prime
$q_i$ satisfying a short homogeneous kernel must lie in one residue class modulo
$p$ for each short $x_i$:

$$
q_i\equiv q_\ast x_\ast x_i^{-1}\pmod p.
$$

Since $q_i\in[X,2X]$ and $p\sim X$, this gives only $O(M_\tau)$ choices for each
seed coordinate. Hence singular seed prime tuples are bounded by

$$
\ll N^2M_\tau^{k+1}(\log X)^{O(1)}
$$

instead of the free count $N^{k+1}$. This is the current candidate proof of the
global sparsity of singular seed tuples, modulo diagonal, zero-star, and
label-bookkeeping exceptions.

The remaining local packaging step is a good-seed selection lemma: either the
fingerprint pool contains a seed tuple outside the sparse singular-tuple
hypergraph, or the pool is concentrated in a low-entropy structured container.

More concretely, for fixed reference seed $q_\ast$ the singular hypergraph is
contained in a union of complete $k$-graphs on reciprocal clusters

$$
\mathcal A(p,q_\ast,x_\ast)
=
\left\{
q\sim X:
q\equiv q_\ast x_\ast x^{-1}\pmod p,\quad |x|\ll M_\tau
\right\},
$$

each of size $\ll M_\tau$. Thus the final packaging problem is a
container/covering statement for these reciprocal clusters: either the seed pool
contains a good tuple, or it is efficiently covered by low-entropy reciprocal
clusters.

The active focused scratch for this final local problem is [[Reciprocal cluster cover proof draft]].
After the latest finite bookkeeping, this local problem is sharpened to a
reciprocal-cluster incidence estimate. Algebraically, a reciprocal cluster is a
large-slope line
$$
z=p\,y+q_\ast x_\ast
$$
meeting the short seed point sets
$$
P_q=\{(y,qx): |x|,|y|\ll M_\tau\}.
$$
Thus the remaining inverse statement is that many such rich lines force many
short factorable collinearity relations, hence a low-entropy rational seed
structure.
Using four total seed primes, this can be sharpened further. If $q_4$ is used
as a base and $a_i=y_i-y_4$, then
$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3),
$$
so
$$
p\equiv -q_4x_4a_i^{-1}\pmod {q_i}.
$$
Thus the final arithmetic endpoint is a CRT product concentration estimate
modulo $Q=q_1q_2q_3$: a short interval in $x_4$ times a reciprocal CRT box in
$(a_1,a_2,a_3)$ should not concentrate inside $[X,2X]\pmod Q$, unless the seed
quadruple is in a low-entropy rational family.
The product-hit statement must be made in its valid quotient form: after
choosing $p,x_4,a_1,a_2,a_3$, the quotients
$$
x_i=\frac{p\,a_i+q_4x_4}{q_i}
$$
must also be nonzero and $\ll M_\tau$. Equivalently, for fixed $p$ the short
variables lie in the homogeneous lattice
$$
q_i x_i-q_4x_4=p\,a_i
\qquad(1\le i\le3).
$$
The remaining estimate is therefore a primitive-ray concentration bound for
these lattices, summed over residual primes $p\sim X$.
One must also keep the reference anchor: the original reciprocal cluster has
intercept $q_\ast x_\ast$, so after using $q_4$ as a base the full normalized
system includes
$$
q_4x_4-q_\ast x_\ast=p\,y_4
$$
in addition to
$$
q_i x_i-q_4x_4=p\,a_i.
$$
The final target is therefore the reference-anchored primitive lattice
concentration theorem, not the unanchored product-hit theorem.

The latest Aristotle package closes the algebraic part of this refinement in
`AnchoredCRTLattice.lean`: the original anchored equations
$$
q_i x_i-q_\ast x_\ast=p\,y_i
\qquad(1\le i\le4)
$$
are equivalent, after using $q_4$ as a base, to the normalized anchored lattice
$$
\begin{cases}
q_i x_i-q_4x_4=p\,a_i,&1\le i\le3,\\
q_4x_4-q_\ast x_\ast=p\,y_4.
\end{cases}
$$
It also proves homogeneous scaling and primitive-ray bookkeeping. Thus the
remaining gap is not an algebraic translation gap. It is the arithmetic
concentration/inverse theorem:
for non-structured $q_\ast,q_1,q_2,q_3,q_4\sim X$ and
$M\le X^{1/2}(\log X)^A$, primitive short rays in the displayed anchored
lattice, summed over $p\sim X$, must be $O((\log X)^C)$, or else the seed primes
must fall into a low-entropy rational structured family that can be charged in
the FIE exception ledger.

This matches the older affine-slice formulation in [[Ambient-sensitive FIE
proof draft]], where regular uniqueness fails only in the presence of a short
homogeneous kernel. It is distinct from the separate [[lattice statement]]
span gadget used in the final Fourier/local-CLT layer.

After `AnchoredSelectionPipeline.lean`, the finite selection part is also no
longer the bottleneck: an anchored codegree estimate feeds into a good tuple,
low-codegree cover, or high-incidence ledger. The extracted arithmetic endpoint
is [[Anchored primitive concentration problem]].

One refinement is important. The cluster codegree counts all scalar multiples
of a primitive anchored ray, because clusters are indexed by $x_\ast$. Thus the
needed theorem is a weighted primitive inverse estimate
$$
\sum_r \frac{M}{H(r)}\ll(\log X)^C
$$
outside structured exceptions, where $H(r)$ is the primitive ray height. Very
small primitive rays must be treated as low-height rational structure, not
silently discarded.

After `AnchoredDeterminantRank.lean`, the fixed-$p$ fibre is algebraically
controlled. Two anchored hits with the same residual prime satisfy
$$
q_i(x_i z_\ast-z_i x_\ast)=p(y_i z_\ast-w_i x_\ast).
$$
Hence either the two short vectors are projectively proportional, or $p$ divides
a nonzero determinant
$$
x_i z_\ast-z_i x_\ast
$$
of size $O(M^2)$. In the strict range $2M^2<p$ this forces projective
proportionality; in the logarithmically enlarged range the determinant quotient
is polylogarithmically small and should enter the structured-exception ledger.

For formal downstream use, this page still treats SBEE as the single named condition. The refined BCE formulation is a sharper route toward proving SBEE, not an additional independent assumption in the main theorem.

---

# 4. Consequence used downstream

Under Condition SBEE, the following single-block compression theorem is available.

**Conditional Single-Block Counting Theorem.**  
For every \(\varepsilon>0\), after Irving-good pruning, every block \(P\subset[X,2X]\) satisfies
\[
\#\{a_P:Q_P(a_P)\le R\}
\ll_\varepsilon
e^{\varepsilon R}
\left(1+\frac{\sqrt R}{\sigma_P}\right)
\]
uniformly for \(R\ge1\).

More precisely, every low-energy assignment can be encoded by:

1. one ordinary label \(m\) with
   \[
   |m|\ll \frac{\sqrt R}{\sigma_P};
   \]
2. an exception set and its residues, whose encoding entropy is paid by internal energy.

The dominant-label case follows from Irving-good majority correction. The non-dominant case in which almost all covered vertices lie in tiny classes forces the short list \(\mathcal L\) to be so large that \(R\) is already large enough to pay the crude entropy. The only nontrivial remaining case is the non-dominant substantial case, exactly Condition SBEE.

---

# 5. What SBEE does not include

SBEE does not hide any of the following:

- Irving's external Kloosterman input;
- the cross-label divisor-energy lemma;
- the lattice-span gadget;
- mass tuning;
- the global Fourier positivity argument;
- the necessity of the squarefree denominator condition.

Those are stated and used separately in [[CP 03 Lemma bank]] and [[CP 01 Conditional theorem]].
