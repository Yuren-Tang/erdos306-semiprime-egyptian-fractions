# Lemma bank

Back to [[CP 00 Navigation]]. The only conditional input in this note is [[CP 02 The single remaining condition|SBEE]].

---

# 1. Phase and Fourier notation

Let \(\mathcal P\) be a finite set of primes and
\[
L=\prod_{p\in\mathcal P}p.
\]
For an edge \(e=pq\), write
\[
w_e=\frac{L}{pq}.
\]
A character \(h\bmod L\) is identified with residues
\[
a_p=h\bmod p,\qquad p\in\mathcal P.
\]
For an edge \(pq\), let \(H_{pq}(a)\in(-pq/2,pq/2]\) be the CRT representative
\[
H_{pq}(a)\equiv a_p\pmod p,\qquad
H_{pq}(a)\equiv a_q\pmod q.
\]
Then
\[
\frac{h}{pq}\equiv \frac{H_{pq}(a)}{pq}\pmod1.
\]
For an edge set \(E\), define
\[
Q_E(a)=
\sum_{pq\in E}
\left\|\frac{H_{pq}(a)}{pq}\right\|^2.
\]

If \(\xi_e\) are independent Bernoulli variables with parameters
\[
\theta_e\in[\theta_0,1-\theta_0],
\]
then
\[
\widehat\mu(h)
=
\prod_{e\in E}
\left(1-\theta_e+\theta_e e\!\left(\frac{h}{e}\right)\right).
\]
The elementary inequality
\[
|1-\theta+\theta e(x)|\le \exp(-c_{\theta_0}\|x\|^2)
\]
gives
\[
|\widehat\mu(h)|\le \exp(-c_{\theta_0}Q_E(a)).
\]

---

# 2. Irving-good pruning

**Lemma 2.1, Irving-good pruning.**  
Let \(P\subset[x,2x]\) and \(Q\subset[y,2y]\) be prime blocks in the range covered by Irving's theorem, for instance
\[
y^{2/3+\delta}\le x\le y^{3/2}.
\]
Let \(\mathcal G\) be a bounded-degree family of such block pairs. After deleting \(o(|P_k|)\) primes from each block \(P_k\), the remaining blocks \(P_k^\ast\) satisfy the following.

For every control pair \((P_k^\ast,P_\ell^\ast)\), every \(q\in P_\ell^\ast\), and every \(d\in\mathbb F_q^\times\),
\[
\sum_{p\in P_k^\ast}
\left\|
\frac{d\bar p}{q}
\right\|^2
\ge c|P_k^\ast|.
\]
The symmetric estimate also holds with \(k,\ell\) interchanged. In the internal case \(P_k=P_\ell\), the same estimate holds with \(p\ne q\).

**Proof.**  
Irving's Theorem 1, as present in [[kloost_paper2]], states
\[
\sum_{q\sim Q}\max_{(a,q)=1}|S_q(a;x)|
\ll_\varepsilon
\left(
Q^{5/4}x^{5/8}
+Qx^{9/10}
+Q^{7/6}x^{13/18}
\right)Q^\varepsilon
\]
for \(Q^{2/3}\le x\le Q^{3/2}\). In the compatible range this is \(o(Q|P|)\) after fixing a small saving. Hence all but \(o(|Q|)\) primes \(q\sim Q\) satisfy
\[
\max_{(a,q)=1}
\left|
\sum_{p\in P}e_q(a\bar p)
\right|
\le \delta_0 |P|
\]
with \(\delta_0>0\) fixed sufficiently small.

For such \(q\), fixing \(d\ne0\pmod q\), the same bound holds for all low Fourier modes
\[
\sum_{p\in P}e\!\left(h\frac{d\bar p}{q}\right),
\qquad 1\le h\le H,
\]
because \(hd\not\equiv0\pmod q\) for fixed \(H<q\). A finite Fourier approximation to \(\|t\|^2\), or Erdős-Turán plus \(\int_0^1\|t\|^2dt=1/12\), gives
\[
\sum_{p\in P}
\left\|\frac{d\bar p}{q}\right\|^2
\ge c|P|.
\]
After pruning a bad set for each control pair and taking a union bound over the bounded-degree block graph, each block loses only \(o(|P_k|)\) primes. Removing \(o(|P_k|)\) terms from a good sum preserves a positive proportion of the lower bound. The internal estimate loses at most the term \(p=q\), which is harmless.

---

# 3. Cross-label divisor-energy

**Lemma 3.1, cross-label divisor-energy.**  
Let \(A,B\subset[X,2X]\) be sets of primes. Let \(m\ne m'\) be integers with
\[
|m|,|m'|\le B_0.
\]
For \(p\in A,q\in B\), let \(H_{pq}^{m,m'}\in(-pq/2,pq/2]\) satisfy
\[
H_{pq}^{m,m'}\equiv m\pmod p,\qquad
H_{pq}^{m,m'}\equiv m'\pmod q.
\]
Put
\[
M=|A||B|,
\qquad
L_X=1+\frac{\log(B_0+X^2+2)}{\log X}.
\]
If
\[
\min(|A|,|B|)\ge C L_X,
\]
then
\[
\sum_{p\in A,q\in B}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2
\gg
M\min\left(1,\frac{M^2}{X^4L_X^4}\right).
\]

**Proof.**  
For \(T\le X^2/2\), let
\[
N(T)=\#\{(p,q)\in A\times B:|H_{pq}^{m,m'}|\le T\}.
\]
If \(|H_{pq}^{m,m'}|\le T\), then for some \(|n|\le T\),
\[
p\mid n-m,\qquad q\mid n-m'.
\]
Thus
\[
N(T)\le
\sum_{|n|\le T}\omega_A(n-m)\omega_B(n-m'),
\]
where \(\omega_A(t)=\#\{p\in A:p\mid t\}\). For \(t\ne0\),
\[
\omega_A(t)\le 1+\frac{\log |t|}{\log X}.
\]
Since \(|n-m|,|n-m'|\le B_0+X^2\), all ordinary terms contribute
\[
\ll TL_X^2.
\]
The exceptional terms \(n=m\) and \(n=m'\) contribute at most
\[
|A|\omega_B(m-m')+|B|\omega_A(m-m')\ll (|A|+|B|)L_X.
\]
Hence
\[
N(T)\ll TL_X^2+(|A|+|B|)L_X.
\]
For \(C\) large enough, the second term is \(\le M/10\). Choose
\[
T_\ast=c\min(M/L_X^2,X^2)
\]
with \(c>0\) small. Then \(N(T_\ast)\le M/2\), so at least \(M/2\) pairs satisfy \(|H_{pq}^{m,m'}|>T_\ast\). Since \(pq\asymp X^2\),
\[
\sum_{p,q}
\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2
\gg
\frac{M T_\ast^2}{X^4},
\]
which is the stated bound.

---

# 4. Conditional single-block compression

**Lemma 4.1, conditional single-block counting.**  
Assume [[CP 02 The single remaining condition|SBEE]]. Let \(P\subset[X,2X]\) be an Irving-good block. Then for every \(\varepsilon>0\),
\[
\#\{a_P:Q_P(a_P)\le R\}
\ll_\varepsilon
e^{\varepsilon R}
\left(1+\frac{\sqrt R}{\sigma_P}\right)
\]
uniformly for \(R\ge1\).

Moreover every low-energy assignment can be encoded by one ordinary label
\[
|m|\ll \frac{\sqrt R}{\sigma_P}
\]
and energy-paid exceptions.

**Proof.**  
The base-list construction gives a short label list
\[
|\mathcal L|\ll 1+\log X\sqrt R
\]
covering all but energy-paid vertices. If one label is dominant, Irving-good majority correction charges every nonconforming vertex by \(\gg |P|\), while its choice and residue entropy is \(O(\log X)\). Hence the exception data contributes \(e^{\varepsilon R}\), and the dominant label has
\[
|m|\ll X\log X\sqrt R\asymp \sqrt R/\sigma_P.
\]
If no dominant label exists but tiny classes carry the disturbance, the same majority correction pays for the tiny vertices as exceptions. If substantial non-dominant classes carry positive mass, SBEE gives the required \(e^{\varepsilon R}\) bound after summing all dyadic class profiles. These cases are exhaustive.

---

# 5. Cross-block label mismatch

Let \(P\subset[X,2X]\), \(Q\subset[Y,2Y]\) be an Irving-good control pair. If the two blocks carry ordinary labels \(m\) and \(m'\), define the cross ordinary energy
\[
Q_{P,Q}(m,m')
=
\sum_{p\in P,q\in Q}
\left\|
\frac{H_{pq}^{m,m'}}{pq}
\right\|^2.
\]

**Lemma 5.1.**  
If \(m\ne m'\), then
\[
Q_{P,Q}(m,m')+Q_{P,Q}(m,m)
\gg |P||Q|
\]
up to divisor exceptions in which \(m'-m\) is divisible by primes from \(Q\). Those exceptions are paid by the standard divisor bound
\[
\#\{q\in Q:q\mid (m'-m)\}
\le
1+\frac{\log |m'-m|}{\log Y}.
\]

**Proof.**  
For \(q\nmid(m'-m)\), put \(d=m'-m\ne0\pmod q\). The phase difference between labels \(m\) and \(m'\) along \(p q\) contains
\[
\frac{d\bar p}{q}.
\]
Using
\[
\|x+y\|^2+\|x\|^2\gg \|y\|^2
\]
and Irving-good pruning,
\[
\sum_{p\in P}
\left\|
\frac{H_{pq}^{m,m'}}{pq}
\right\|^2
+
\sum_{p\in P}
\left\|
\frac{H_{pq}^{m,m}}{pq}
\right\|^2
\gg
\sum_{p\in P}
\left\|\frac{d\bar p}{q}\right\|^2
\gg |P|.
\]
Summing over all non-exceptional \(q\in Q\) proves the claim.

---

# 6. Block-label collapse

Let the control block graph be a bounded-degree connected graph \(\mathcal G\), and for simplicity take it to be a path in the final construction. For a block-label configuration \(m_\bullet=(m_k)\), define
\[
\mathcal Q(m_\bullet)
=
\sum_k Q_k^{\rm diag}(m_k)
+
\sum_{(k,\ell)\in\mathcal G}Q_{k\ell}(m_k,m_\ell),
\]
where
\[
Q_k^{\rm diag}(m)=
\sum_{\substack{p<q\\p,q\in P_k}}
\left\|\frac{m}{pq}\right\|^2.
\]

**Lemma 6.1, Peierls collapse.**  
Under SBEE,
\[
\sum_{m_\bullet}e^{-c\mathcal Q(m_\bullet)}
\ll
\sum_m e^{-c'Q_{\rm diag}(m)}.
\]

**Proof.**  
By Lemma 4.1, each block assignment is compressed into an ordinary label plus energy-paid exceptions. Thus, after summing exceptions, it remains to sum block-label configurations with weight \(e^{-c\mathcal Q(m_\bullet)}\).

For every skeleton edge \((k,\ell)\) with \(m_k\ne m_\ell\), Lemma 5.1 gives a boundary penalty
\[
\gg |P_k||P_\ell|
\]
apart from divisor exceptions, which are themselves paid by the same energy accounting. Since
\[
|P_k||P_\ell|\asymp \frac{2^{k+\ell}}{k\ell},
\]
this penalty is exponentially larger than the entropy of choosing labels on any connected droplet, which is controlled by the diagonal Gaussian sums
\[
\sum_m e^{-cQ_k^{\rm diag}(m)}\ll 1/\sigma_k\asymp 2^k k.
\]
For a path skeleton, a nonconstant configuration decomposes into disjoint intervals on which \(m_k\) differs from the exterior label. Each interval has at least one, and usually two, boundary edges. The polymer weight of an interval \(I\) is bounded by
\[
\exp\left(-c\sum_{\partial I}|P_k||P_\ell|\right)
\prod_{j\in I}\left(\sum_m e^{-cQ_j^{\rm diag}(m)}\right).
\]
The boundary exponential dominates the product because the former is \(\exp(-c2^{2j}/j^2)\) at the first boundary scale, while the latter contributes only \(\exp(O(\sum_{j\in I}j))\). Hence the polymer expansion is absolutely summable, uniformly in the number of blocks, and contributes a bounded multiplicative factor. The constant-label sector is exactly
\[
\sum_m e^{-c'\sum_k Q_k^{\rm diag}(m)}
=
\sum_m e^{-c'Q_{\rm diag}(m)}.
\]

---

# 7. Ordinary diagonal counting

**Lemma 7.1.**  
Under SBEE,
\[
\#\{m\bmod L:Q_{\rm diag}(m)\le R\}
\ll_\varepsilon
e^{\varepsilon R}
\left(1+\frac{\sqrt R}{\sigma}\right),
\]
and
\[
\sum_{m\bmod L}e^{-cQ_{\rm diag}(m)}
\ll
\frac1\sigma.
\]
The same estimate with \(o(1/\sigma)\) holds outside \(|m|\le C/\sigma\) after \(C\to\infty\).

**Proof.**  
Apply the conditional single-block theorem to the diagonal residues \(a_p=m\bmod p\) on each block. Low energy gives local representatives \(m_k\) and energy-paid exceptional primes. Lemma 5.1 and Lemma 6.1 collapse the \(m_k\) to a single global ordinary label \(m_0\).

For all non-exceptional primes \(p\), one has
\[
m\equiv m_0\pmod p.
\]
Thus
\[
m\equiv m_0\pmod{\prod_{p\notin T}p},
\]
where \(T\) is the exceptional set. The residue data on \(T\) is paid by Irving-good correction: if \(q\in T\), then \(m-m_0\not\equiv0\pmod q\), and the neighboring conforming primes force cost \(\gg |P|\), exceeding the \(O(\log q)\) residue entropy.

Hence \(m\bmod L\) is encoded by \(m_0\) plus energy-paid exceptions. The ordinary label satisfies
\[
Q_{\rm diag}(m_0)=m_0^2\sigma^2
\le CR,
\]
so there are
\[
\ll 1+\sqrt R/\sigma
\]
choices for \(m_0\). Summing exception data gives the claimed level-set bound. The partition sum follows by dyadic summation in \(R\), choosing \(\varepsilon<c/2\). The tail outside \(|m|\le C/\sigma\) is the usual Gaussian tail.

---

# 8. Global control partition theorem

Let
\[
E_{\rm ctrl}=E_{\rm int}\cup E_{\rm skel}.
\]
Let
\[
\sigma_{\rm ctrl}^2
=
\sum_{e\in E_{\rm ctrl}}\theta_e(1-\theta_e)e^{-2}.
\]

**Proposition 8.1.**  
Under SBEE,
\[
\sum_a e^{-cQ_{\rm ctrl}(a)}
\ll
\frac1{\sigma_{\rm ctrl}},
\]
and, for the main arc
\[
\mathfrak M_C=\{a:a_p\equiv m\pmod p\ {\rm for\ all\ }p,\ |m|\le C/\sigma_{\rm ctrl}\},
\]
one has
\[
\sum_{a\notin\mathfrak M_C}e^{-cQ_{\rm ctrl}(a)}
=o_C(1/\sigma_{\rm ctrl}).
\]

**Proof.**  
Apply Lemma 4.1 block by block, summing internal exceptions into \(e^{\varepsilon Q_{\rm ctrl}}\). The resulting block labels are summed by Lemma 6.1. The surviving ordinary diagonal sum is controlled by Lemma 7.1. Taking \(\varepsilon\) smaller than the Fourier decay constant gives the stated partition bound. The main-arc complement is handled by the tail part of Lemma 7.1.

---

# 9. Edge construction, mass, variance

**Lemma 9.1, edge architecture.**  
For every squarefree \(b\), one can choose finite prime blocks and an edge set
\[
E=E_{\rm int}\cup E_{\rm skel}\cup E_{\rm mass}\cup E_{\rm gad}
\]
with Bernoulli parameters \(\theta_e\in[1/3,2/3]\) such that
\[
\sum_{e\in E}\frac{\theta_e}{e}=\frac1b,
\]
\[
\sigma_E^2\asymp\sigma_{\rm ctrl}^2,
\]
and every prime in \(\mathcal P\) is incident to at least one edge.

**Proof.**  
Choose a large initial scale \(k_0\). Put internal complete graphs on every block \(P_k\) used. Their mass is
\[
\sum_{k\ge k_0}\sum_{p<q\in P_k}\frac1{pq}
\asymp
\sum_{k\ge k_0}\frac1{k^2},
\]
which can be made \(<1/(100b)\). Their variance is dominated by the lowest block:
\[
\sigma_{\rm int}^2\asymp \frac1{2^{2k_0}k_0^2}.
\]
Add a bounded-degree compatible skeleton, for instance a path through the chosen blocks. Its variance is no larger than the same order.

Choose \(K_1\gg k_0\), also large enough that every high edge denominator \(e\) used below satisfies
\[
\frac{1/\sigma_{\rm ctrl}}{e}=o(1).
\]
This is needed only for the uniform main-arc Taylor expansion. High-scale bipartite edges with \(k,\ell\ge K_1\) have total reciprocal mass
\[
\sum_{K_1\le k,\ell\le K}\frac1{k\ell}
\asymp
\left(\log\frac K{K_1}\right)^2,
\]
which tends to infinity with \(K\), while their variance is
\[
\ll 2^{-2K_1}
\sum_{K_1\le k,\ell\le K}\frac1{k\ell}.
\]
Taking \(K_1\) large makes this variance \(o(\sigma_{\rm ctrl}^2)\), and then taking \(K\) large gives enough mass.

Set all mandatory control and gadget edges initially with parameter \(1/2\), making their total expected mass \(M_0<1/(4b)\). Let
\[
\Delta=1/b-M_0>0.
\]
From high-scale mass edges, greedily choose a finite batch \(H\) with reciprocal mass
\[
2\Delta\le W_H=\sum_{e\in H}\frac1e\le 3\Delta,
\]
possible because individual high edges have arbitrarily small mass and the available total mass exceeds \(3\Delta\). Assign all edges in \(H\) the common parameter
\[
\theta_H=\Delta/W_H\in[1/3,1/2].
\]
Then the expected mass is exactly \(1/b\), and all parameters remain in \([1/3,2/3]\).

All primes appearing in mass edges are also placed in internal blocks, so no uncontrolled CRT entropy is introduced. The high-mass variance is \(o(\sigma_{\rm ctrl}^2)\), hence \(\sigma_E\asymp\sigma_{\rm ctrl}\).

---

# 10. Lattice span

**Lemma 10.1.**  
Assume \(b\) is squarefree and
\[
\{r:r\mid b\}\subset\mathcal P,
\qquad
L=\prod_{p\in\mathcal P}p.
\]
If every \(p\in\mathcal P\) is incident to at least one edge \(pq\in E\), then
\[
\gcd\left\{\frac{L}{pq}:pq\in E\right\}=1.
\]

**Proof.**  
Let \(r\in\mathcal P\). Since \(r\) is incident to some edge \(rs\in E\), the weight \(L/(rs)\) is not divisible by \(r\). Hence \(r\) does not divide the gcd of all weights. Every prime divisor of \(L\) lies in \(\mathcal P\), so no prime divides the gcd.

To ensure the hypothesis for primes \(r\mid b\), add gadget edges \(rs_r\), where \(s_r\) is a large prime in a used high block. There are only \(O_b(1)\) such edges, and \(s_r\) can be chosen so large that their mass and variance are negligible and
\[
\frac{1/\sigma_{\rm ctrl}}{rs_r}=o(1).
\]
Their presence removes periodicity obstructions in Fourier inversion without disturbing the main-arc Taylor expansion.
