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

The working scratch file [[SBEE dyadic proof draft]] currently narrows the internal SBEE bottleneck further.

The arithmetic large-sieve-looking part is reduced to a deterministic marked dual estimate: for a bucket core $\mathcal B$ and incidence threshold $h$, the candidate labelled vertices satisfying

$$
d_{\mathcal B}(p,t)\ge h
$$

lie in a container of size

$$
\ll
\frac{|\mathcal B|N+|\mathcal B|^2}{h^2}.
$$

Thus the remaining unproved subcondition is the bucket-core exposure/fingerprint step: near-saturated high-collision bucket cores should be generated from low-entropy fingerprints, rather than enumerated as arbitrary subsets of the bucket interval. The current scratch reduction sharpens this once more to a fingerprint-iteration entropy check:

$$
\text{FIE}
\Longrightarrow
\text{BCE}
\Longrightarrow
\text{SBEE}.
$$

The present scale check shows that the fingerprint/core-generation entropy is smaller than the bucket-capacity energy by a factor $\ll sL_X(\log X)^4/X$ in the saturated short-list regime, while the complementary large-list regime is already paid by the base-list lower bound on $R$. The remaining FIE issue is the residual-container entropy: after a fingerprint generates a bucket core, one must still show that low-energy choices inside the resulting $O(N)$-sized candidate container are recursively exposed or else paid by a high-common-neighbour estimate. The current scratch calculation suggests that recursive exposure down to mass

$$
W_\ast=(sL_XX^2\log(Ns))^{1/3}
$$

should pay the residual entropy in the true short-list range, while larger $sL_X$ is already crude-entropy-paid by the base-list lower bound.

In the scratch file this is now organized as Proposition FIE with four finite bookkeeping lemmas: non-saturated deficit, saturated one-step exposure, residual descent, and terminal seed encoding. The saturated exposure and terminal seed parts are essentially in place; the precise non-saturated layer-cake deficit and residual descent statements remain to be written.

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
