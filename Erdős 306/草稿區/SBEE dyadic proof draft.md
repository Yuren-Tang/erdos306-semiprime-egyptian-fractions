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

