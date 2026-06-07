# Conditional theorem

Back to [[CP 00 Navigation]].

This note gives the cleaned conditional proof. The only unproved condition is [[CP 02 The single remaining condition|SBEE]]. All other inputs are isolated in [[CP 03 Lemma bank]].

---

# 1. Conditional main theorem

**Theorem, conditional on SBEE.**  
Assume Condition SBEE from [[CP 02 The single remaining condition]]. Let \(b\) be squarefree. For every positive integer \(a\), there exist finitely many distinct squarefree semiprimes
\[
n_i=p_iq_i
\]
such that
\[
\frac ab=\sum_i\frac1{n_i}.
\]

The squarefree hypothesis on \(b\) is necessary: if all \(n_i\) are squarefree, then the least common multiple of the \(n_i\) is squarefree, and therefore the reduced denominator of any finite sum \(\sum_i1/n_i\) is squarefree.

It remains to prove sufficiency.

---

# 2. Reduction to \(1/b\)

It suffices to prove that for every squarefree \(b\) there is a finite set \(S\) of distinct squarefree semiprimes such that
\[
\frac1b=\sum_{n\in S}\frac1n.
\]
Indeed, once this is known, choose \(a\) pairwise disjoint copies of the entire prime construction. The corresponding semiprime sets are disjoint, and summing the \(a\) representations gives
\[
\frac ab=\sum_{j=1}^a\sum_{n\in S_j}\frac1n.
\]

Hence we prove the case \(1/b\).

---

# 3. Edge set and random model

Choose the finite edge set
\[
E=E_{\rm int}\cup E_{\rm skel}\cup E_{\rm mass}\cup E_{\rm gad}
\]
and Bernoulli parameters
\[
\theta_e\in[1/3,2/3]
\]
as in [[CP 03 Lemma bank#9. Edge construction, mass, variance|Lemma 9.1]]. Thus
\[
\sum_{e\in E}\frac{\theta_e}{e}=\frac1b,
\]
and
\[
\sigma_E^2
:=
\sum_{e\in E}\theta_e(1-\theta_e)e^{-2}
\asymp
\sigma_{\rm ctrl}^2.
\]
All primes used by mass edges also lie in internal control blocks. The small primes \(r\mid b\) are included in the total prime set by gadget edges.

Let
\[
\mathcal P
\]
be the full set of primes appearing in the construction, including all \(r\mid b\), and put
\[
L=\prod_{p\in\mathcal P}p.
\]
Since \(b\) is squarefree and \(\{r:r\mid b\}\subset\mathcal P\), we have \(b\mid L\).

Let \(\xi_e\) be independent Bernoulli variables with
\[
\mathbb P(\xi_e=1)=\theta_e.
\]
Define
\[
X=\sum_{e\in E}\frac{\xi_e}{e},
\qquad
Y=LX=\sum_{e\in E}\xi_e\frac Le.
\]
Then
\[
\mathbb E X=\frac1b.
\]
By [[CP 03 Lemma bank#10. Lattice span|Lemma 10.1]],
\[
\gcd\{L/e:e\in E\}=1,
\]
so there is no lattice-period obstruction to the target value \(Y=L/b\).

We will prove
\[
\mathbb P(Y=L/b)>0.
\]
This produces a deterministic subset \(S\subset E\) with
\[
\sum_{e\in S}\frac1e=\frac1b.
\]

---

# 4. Fourier inversion

On \(\mathbb Z/L\mathbb Z\),
\[
\mathbb P(Y=L/b)
=
\frac1L
\sum_{h\bmod L}
\widehat\mu(h)e(-h/b),
\]
where
\[
\widehat\mu(h)
=
\prod_{e\in E}
\left(1-\theta_e+\theta_e e(h/e)\right).
\]

Identify \(h\bmod L\) with residues
\[
a_p=h\bmod p,\qquad p\in\mathcal P.
\]
For \(e=pq\), let \(H_{pq}(a)\) be the symmetric CRT representative. Then
\[
\frac he\equiv \frac{H_{pq}(a)}{pq}\pmod1.
\]
By [[CP 03 Lemma bank#1. Phase and Fourier notation|the standard Bernoulli Fourier bound]],
\[
|\widehat\mu(h)|
\le
\exp(-cQ_E(a)).
\]

---

# 5. Main arc

Let
\[
\mathfrak M_C
=
\{h\bmod L:h\equiv m\pmod p\ {\rm for\ every}\ p\in\mathcal P,\ |m|\le C/\sigma_E\}.
\]
For such \(h\), the character is represented by one ordinary label \(m\), and for every edge \(e=pq\),
\[
\frac he\equiv \frac m{pq}\pmod1.
\]
Since \(|m|/pq\to0\) uniformly along the construction, Taylor expansion gives
\[
\log\widehat\mu(m)
=
2\pi i m\sum_{e\in E}\frac{\theta_e}{e}
-2\pi^2m^2\sum_{e\in E}\theta_e(1-\theta_e)e^{-2}
+o(1)
\]
uniformly for \(|m|\le C/\sigma_E\). The mass tuning gives
\[
\sum_{e\in E}\frac{\theta_e}{e}=\frac1b.
\]
Thus the linear phase is cancelled by \(e(-m/b)\), and
\[
\widehat\mu(m)e(-m/b)
=
\exp(-2\pi^2\sigma_E^2m^2+o(1)).
\]
Therefore
\[
\sum_{h\in\mathfrak M_C}\widehat\mu(h)e(-h/b)
=
(1+o(1))
\sum_{|m|\le C/\sigma_E}
e^{-2\pi^2\sigma_E^2m^2}.
\]
For fixed large \(C\), this is positive and
\[
\asymp \frac1{\sigma_E}.
\]

---

# 6. Minor arc

The full energy dominates the control energy:
\[
Q_E(a)\ge Q_{\rm ctrl}(a).
\]
By [[CP 03 Lemma bank#8. Global control partition theorem|Proposition 8.1]], conditional on SBEE,
\[
\sum_{a\notin\mathfrak M_C}
e^{-cQ_{\rm ctrl}(a)}
=
o_C(1/\sigma_{\rm ctrl}).
\]
Since
\[
\sigma_E\asymp\sigma_{\rm ctrl},
\]
we obtain
\[
\sum_{h\notin\mathfrak M_C}
|\widehat\mu(h)|
\le
\sum_{a\notin\mathfrak M_C}
e^{-cQ_E(a)}
\le
\sum_{a\notin\mathfrak M_C}
e^{-cQ_{\rm ctrl}(a)}
=
o_C(1/\sigma_E).
\]

Thus the minor arc is smaller than the positive main-arc contribution.

---

# 7. Positivity

Combining the main and minor arcs,
\[
\sum_{h\bmod L}\widehat\mu(h)e(-h/b)
=
\sum_{h\in\mathfrak M_C}\widehat\mu(h)e(-h/b)
+
\sum_{h\notin\mathfrak M_C}\widehat\mu(h)e(-h/b)
>0
\]
for the construction parameters sufficiently large and then \(C\) sufficiently large.

Hence
\[
\mathbb P(Y=L/b)
=
\frac1L
\sum_{h\bmod L}\widehat\mu(h)e(-h/b)
>0.
\]
There is therefore a deterministic choice of \(\xi_e\in\{0,1\}\) such that
\[
\sum_{e\in E}\frac{\xi_e}{e}=\frac1b.
\]
Every \(e\in E\) is a product \(pq\) of two distinct primes, so every selected denominator is a squarefree semiprime. The edges are distinct by construction.

This proves the \(1/b\) case, and by Section 2 it proves the theorem for \(a/b\).

---

# 8. Exact conditional status

The proof above depends on SBEE and only on SBEE as an unproved internal input.

The following are not conditions:

- squarefree \(b\): this is part of the theorem and is necessary;
- Irving's theorem: external cited input, isolated in [[CP 03 Lemma bank#2. Irving-good pruning]];
- mass tuning and variance compatibility: construction lemma, [[CP 03 Lemma bank#9. Edge construction, mass, variance]];
- lattice reachability: [[CP 03 Lemma bank#10. Lattice span]];
- cross-label divisor-energy: proved in [[CP 03 Lemma bank#3. Cross-label divisor-energy]].

The remaining work is exactly [[CP 02 The single remaining condition|Condition SBEE]], with the working scratch file [[SBEE dyadic proof draft]].

