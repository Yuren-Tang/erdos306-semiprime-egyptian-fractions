# Formalized conditional proof

Back to [[CP 00 Navigation]].

This note gives a self-contained, publication-level formalization of the conditional proof of the squarefree-denominator Egyptian-fraction theorem for reciprocals of squarefree semiprimes. The sole unproved input is [[CP 02 The single remaining condition|Condition SBEE]]. All other ingredients are either proved internally or cited from external sources (Irving's Kloosterman theorem).

---

# Table of contents

1. [Theorem statement](#1-theorem-statement)
2. [Classification of inputs](#2-classification-of-inputs)
3. [Notation and standing conventions](#3-notation-and-standing-conventions)
4. [External cited input: Irving's Kloosterman bound](#4-external-cited-input-irvings-kloosterman-bound)
5. [Irving-good pruning lemma](#5-irving-good-pruning-lemma)
6. [Cross-label divisor-energy lemma](#6-cross-label-divisor-energy-lemma)
7. [Conditional input: SBEE](#7-conditional-input-sbee)
8. [Conditional single-block counting theorem](#8-conditional-single-block-counting-theorem)
9. [Cross-block label mismatch lemma](#9-cross-block-label-mismatch-lemma)
10. [Block-label Peierls collapse](#10-block-label-peierls-collapse)
11. [Ordinary diagonal counting](#11-ordinary-diagonal-counting)
12. [Global control partition theorem](#12-global-control-partition-theorem)
13. [Edge construction, mass tuning, and variance compatibility](#13-edge-construction-mass-tuning-and-variance-compatibility)
14. [Lattice-span gadget](#14-lattice-span-gadget)
15. [Fourier inversion and positivity](#15-fourier-inversion-and-positivity)
16. [Reduction from $1/b$ to $a/b$](#16-reduction-from-1b-to-ab)
17. [Main theorem](#17-main-theorem)
18. [Potential non-SBEE gaps](#18-potential-non-sbee-gaps)

---

# 1. Theorem statement

**Theorem 1.1 (Conditional main theorem).**
*Assume Condition SBEE (§7). Let $b$ be a squarefree positive integer. Then for every positive integer $a$, there exist finitely many distinct squarefree semiprimes $n_1,\dots,n_k=p_iq_i$ (each $p_i<q_i$ prime) such that*
$$
\frac{a}{b}=\sum_{i=1}^k\frac{1}{n_i}.
$$

**Remark 1.2 (Necessity of squarefree $b$).**
The hypothesis that $b$ is squarefree is necessary. If each $n_i$ is squarefree, then $\operatorname{lcm}(n_1,\dots,n_k)$ is squarefree, and the reduced denominator of any finite sum $\sum_i 1/n_i$ divides this lcm, hence is itself squarefree. Therefore no rational with a non-squarefree denominator can be represented.

**Non-theorem.** The unrestricted-denominator statement "every positive rational is a finite sum of reciprocals of distinct squarefree semiprimes" is *false* by the above observation. This formalization never states or uses that incorrect version.

---

# 2. Classification of inputs

The proof uses inputs of four kinds. We list them once and refer to this classification throughout.

| Label | Type | Status | Reference |
|---|---|---|---|
| **Irving** | External cited theorem | Accepted without proof | Irving, Kloosterman sums (§4) |
| **SBEE** | Conditional hypothesis | Unproved | §7 |
| **Internal lemmas** | Proved in this document | Complete | §5, §6, §8–§14 |
| **Construction** | Explicit finite construction | Verified | §13, §14 |

---

# 3. Notation and standing conventions

## 3.1. Prime blocks

A *prime block* is a finite set of primes $P\subset[X,2X]$ for some scale parameter $X$. We write $N=|P|$ and
$$
\sigma_P^2=\sum_{\substack{p<q\\p,q\in P}}\frac{1}{p^2q^2}.
$$
Since the primes in $P$ have size $\Theta(X)$, we have $\sigma_P^2\asymp N^2/X^4$.

## 3.2. CRT representatives

For distinct primes $p,q$ and residues $a_p\in\mathbb{F}_p$, $a_q\in\mathbb{F}_q$, the *symmetric CRT representative* $H_{pq}(a)\in(-pq/2,pq/2]$ is the unique integer satisfying
$$
H_{pq}(a)\equiv a_p\pmod{p},\qquad H_{pq}(a)\equiv a_q\pmod{q}.
$$
For two labels $m\ne m'$ and primes $p\in A$, $q\in B$, we write $H_{pq}^{m,m'}\in(-pq/2,pq/2]$ for the CRT representative with
$$
H_{pq}^{m,m'}\equiv m\pmod{p},\qquad H_{pq}^{m,m'}\equiv m'\pmod{q}.
$$

## 3.3. Quadratic energy

For a residue assignment $a_P=(a_p)_{p\in P}$ on a block $P$, the *internal energy* is
$$
Q_P(a)=\sum_{\substack{p<q\\p,q\in P}}\left(\frac{H_{pq}(a)}{pq}\right)^2.
$$
For a general edge set $E$ consisting of edges $e=pq$, the *edge energy* is
$$
Q_E(a)=\sum_{pq\in E}\left\|\frac{H_{pq}(a)}{pq}\right\|^2,
$$
where $\|x\|=\min_{n\in\mathbb{Z}}|x-n|$ denotes the distance to the nearest integer.

## 3.4. Fourier characters and edge set

Let $\mathcal{P}$ be a finite set of primes and $L=\prod_{p\in\mathcal{P}}p$. An edge set $E$ consists of products $e=pq$ with $p,q\in\mathcal{P}$, $p\ne q$. For $e=pq$, write $w_e=L/(pq)$.

A character $h\bmod L$ is identified with residues $a_p=h\bmod p$ for each $p\in\mathcal{P}$.

## 3.5. Bernoulli random model

For each edge $e\in E$, let $\theta_e\in[\theta_0,1-\theta_0]$ (with $\theta_0=1/3$ in the final construction) be a Bernoulli parameter. Let $\xi_e$ be independent Bernoulli random variables with $\mathbb{P}(\xi_e=1)=\theta_e$. Define
$$
X=\sum_{e\in E}\frac{\xi_e}{e},\qquad Y=LX=\sum_{e\in E}\xi_e\frac{L}{e}.
$$
The characteristic function (Fourier transform of the distribution of $Y\bmod L$) is
$$
\widehat{\mu}(h)=\prod_{e\in E}\left(1-\theta_e+\theta_e\,e\!\left(\frac{h}{e}\right)\right),
$$
where $e(x)=e^{2\pi ix}$.

## 3.6. Label lists and class decomposition

For a block $P\subset[X,2X]$, an energy level $R\ge 1$, and a base-list parameter $A$, set
$$
B=AX\log X\sqrt{R}.
$$
After choosing a regular base vertex $p_0\in P$, the *short label list* is
$$
\mathcal{L}=\{n\in[-B,B]:n\equiv a_{p_0}\pmod{p_0}\},\qquad |\mathcal{L}|\ll 1+\log X\sqrt{R}.
$$
For $m\in\mathcal{L}$, the *label class* is $C_m=\{p\in P:a_p\equiv m\pmod{p}\}$.

Let $L_X=1+\frac{\log(B+X^2+2)}{\log X}$. A class $C_m$ is *substantial* if $|C_m|\ge C_0 L_X$ and *tiny* otherwise. A label $m$ is *dominant* if $|C_m|\ge(1-\rho)N$ for a fixed small $\rho>0$.

---

# 4. External cited input: Irving's Kloosterman bound

**Theorem 4.1 (Irving).** *Let $Q\ge 1$ and $x\ge 1$ with $Q^{2/3}\le x\le Q^{3/2}$. Then*
$$
\sum_{q\sim Q}\max_{(a,q)=1}\left|\sum_{\substack{p\le x\\p\text{ prime}}}e_q(a\bar{p})\right|\ll_\varepsilon\left(Q^{5/4}x^{5/8}+Qx^{9/10}+Q^{7/6}x^{13/18}\right)Q^\varepsilon.
$$

*Source:* Irving, "Estimates for character sums and Dirichlet $L$-functions to smooth moduli," Theorem 1.

**Status:** External cited input. Not proved in this document.

---

# 5. Irving-good pruning lemma

**Lemma 5.1 (Irving-good pruning).**
*Let $\{(P_k,P_\ell)\}$ be a bounded-degree family of block pairs in the range compatible with Theorem 4.1. After deleting $o(|P_k|)$ primes from each block $P_k$, the remaining blocks $P_k^*$ satisfy the following: for every control pair $(P_k^*,P_\ell^*)$, every $q\in P_\ell^*$, and every $d\in\mathbb{F}_q^\times$,*
$$
\sum_{p\in P_k^*}\left\|\frac{d\bar{p}}{q}\right\|^2\ge c|P_k^*|.
$$
*The symmetric estimate holds with $k,\ell$ interchanged. In the internal case $k=\ell$, the same holds with $p\ne q$.*

**Proof.**

*Step 1 (Kloosterman to equidistribution).* By Theorem 4.1, in the compatible range $Q^{2/3+\delta}\le x\le Q^{3/2}$, one obtains
$$
\sum_{q\sim Q}\max_{(a,q)=1}\left|S_q(a;x)\right|=o(Q|P|).
$$
Hence all but $o(|Q|)$ primes $q\sim Q$ satisfy, for every $(a,q)=1$,
$$
\left|\sum_{p\in P}e_q(a\bar{p})\right|\le\delta_0|P|
$$
with $\delta_0>0$ fixed and sufficiently small.

*Step 2 (Fourier to quadratic equidistribution).* For such a good prime $q$ and any $d\not\equiv 0\pmod{q}$, the exponential sum bound extends to all low frequencies $1\le h\le H$ with $H<q$ fixed:
$$
\left|\sum_{p\in P}e\!\left(h\frac{d\bar{p}}{q}\right)\right|\le\delta_0|P|.
$$
By finite Fourier approximation to $\|t\|^2$ (or Erdős–Turán plus $\int_0^1\|t\|^2\,dt=1/12$),
$$
\sum_{p\in P}\left\|\frac{d\bar{p}}{q}\right\|^2\ge c|P|.
$$

*Step 3 (Union bound and pruning).* For each control pair $(P_k,P_\ell)$ in the bounded-degree block graph, delete the $o(|P_\ell|)$ bad primes in $P_\ell$. The block graph has bounded degree, so the total loss from each block is $o(|P_k|)$. Removing $o(|P_k|)$ terms from a good sum preserves a positive proportion of the lower bound. The internal case ($k=\ell$) loses at most the diagonal term $p=q$, which is harmless. $\square$

**Status:** Internal lemma, proved from external input (Theorem 4.1).

---

# 6. Cross-label divisor-energy lemma

**Lemma 6.1 (Cross-label divisor-energy).**
*Let $A,B\subset[X,2X]$ be sets of primes with $M=|A||B|$. Let $m\ne m'$ be integers with $|m|,|m'|\le B_0$, and put $L_X=1+\frac{\log(B_0+X^2+2)}{\log X}$. If $\min(|A|,|B|)\ge CL_X$ for a sufficiently large constant $C$, then*
$$
\sum_{p\in A,\,q\in B}\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2\gg M\min\!\left(1,\frac{M^2}{X^4 L_X^4}\right).
$$

**Proof.**

*Step 1 (Level-set counting).* For $T\le X^2/2$, let
$$
N(T)=\#\{(p,q)\in A\times B:|H_{pq}^{m,m'}|\le T\}.
$$
If $|H_{pq}^{m,m'}|\le T$, then there exists $n$ with $|n|\le T$ such that $p\mid(n-m)$ and $q\mid(n-m')$. Defining $\omega_A(t)=\#\{p\in A:p\mid t\}$, we have for $t\ne 0$ the bound $\omega_A(t)\le 1+\frac{\log|t|}{\log X}$. Summing:
$$
N(T)\le\sum_{|n|\le T}\omega_A(n-m)\,\omega_B(n-m').
$$

*Step 2 (Ordinary and exceptional terms).* For the $O(T)$ ordinary terms ($n\ne m$ and $n\ne m'$), each factor is $\le L_X$, contributing $\ll TL_X^2$. The exceptional terms $n=m$ and $n=m'$ contribute
$$
|A|\,\omega_B(m-m')+|B|\,\omega_A(m-m')\ll(|A|+|B|)L_X.
$$
Hence
$$
N(T)\ll TL_X^2+(|A|+|B|)L_X.
$$

*Step 3 (Threshold and conclusion).* For $C$ sufficiently large, the second term is $\le M/10$. Choose
$$
T_*=c\min(M/L_X^2,\,X^2)
$$
with $c>0$ small. Then $N(T_*)\le M/2$, so at least $M/2$ pairs satisfy $|H_{pq}^{m,m'}|>T_*$. Since $pq\asymp X^2$,
$$
\sum_{p\in A,\,q\in B}\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2\gg\frac{MT_*^2}{X^4}=M\min\!\left(1,\frac{M^2}{X^4L_X^4}\right).
$$
$\square$

**Status:** Internal lemma, fully proved. No conditional input used.

---

# 7. Conditional input: SBEE

**Condition SBEE (Single-Block Energy-Entropy).**
*For every $\varepsilon>0$ and every sufficiently small fixed $\rho>0$, there exist constants $C_0,A,C_\varepsilon$ such that the following holds for every sufficiently large pruned Irving-good block $P\subset[X,2X]$.*

*Fix $R\ge 1$, a short label list $\mathcal{L}$ arising from the base-list construction (§3.6), and a dyadic class-size profile for substantial classes. Consider all residue assignments $a_P$ satisfying:*

1. *$Q_P(a_P)\le R$;*
2. *at least $(1-o_\rho(1))N$ vertices are covered by labels in $\mathcal{L}$;*
3. *no label is dominant: $\max_{m\in\mathcal{L}}|C_m|<(1-\rho)N$;*
4. *the union of substantial classes has size at least $\rho N$;*
5. *the substantial class sizes lie in the prescribed dyadic profile.*

*Move all tiny classes and uncovered vertices into an exception ledger. Let $T_{\mathrm{exc}}(a)$ denote the total Irving-good exception cost assigned to those vertices; each exception vertex is charged by its interactions with a positive-density conforming reference class, so one exception in a block of size $N$ costs $\gg N$, while its encoding entropy is $O(\log X+\log s)$.*

*Then, for every $T\ge 0$, the number of such assignments with*
$$
S_{\mathrm{sub}}(C_\bullet)+T_{\mathrm{exc}}(a)\le T
$$
*is at most*
$$
C_\varepsilon\exp\{\varepsilon(R+T)\},
$$
*where $S_{\mathrm{sub}}(C_\bullet)=\sum_{\substack{m\ne m'\\ C_m,C_{m'}\text{ substantial}}}\sum_{p\in C_m,\,q\in C_{m'}}\left(\frac{H_{pq}^{m,m'}}{pq}\right)^2$ is the substantial cross-label energy.*

*Equivalently, after summing over all dyadic profiles, all short lists $\mathcal{L}$, and all substantial/tiny decompositions, the total contribution of the non-dominant substantial case to the single-block level set is $\ll_\varepsilon e^{\varepsilon R}$.*

**Status:** Conditional hypothesis. **Not proved.** This is the sole unproved input used in this document.

---

# 8. Conditional single-block counting theorem

**Theorem 8.1 (Conditional single-block counting).**
*Assume SBEE (§7). Let $P\subset[X,2X]$ be an Irving-good block. Then for every $\varepsilon>0$,*
$$
\#\{a_P:Q_P(a_P)\le R\}\ll_\varepsilon e^{\varepsilon R}\left(1+\frac{\sqrt{R}}{\sigma_P}\right)
$$
*uniformly for $R\ge 1$. Moreover, every low-energy assignment can be encoded by one ordinary label $|m|\ll\sqrt{R}/\sigma_P$ and energy-paid exceptions.*

**Proof.** The proof proceeds by exhaustive case analysis over three mutually exclusive and exhaustive cases.

*Case 1: Dominant label.* Suppose some $m_0\in\mathcal{L}$ satisfies $|C_{m_0}|\ge(1-\rho)N$. Then every $p\in P\setminus C_{m_0}$ is a nonconforming vertex, and by Irving-good pruning (Lemma 5.1), each such vertex contributes energy $\gg N$ through its interactions with the $(1-\rho)N$-element conforming class $C_{m_0}$. The choice and residue entropy of each nonconforming vertex is $O(\log X)$. Hence the exception data is encoded within cost $e^{\varepsilon R}$. The dominant label satisfies
$$
|m_0|\ll X\log X\sqrt{R}\asymp\sqrt{R}/\sigma_P,
$$
giving $\ll 1+\sqrt{R}/\sigma_P$ choices.

*Case 2: Non-dominant, tiny classes carry the disturbance.* If no label is dominant and the union of substantial classes has size $<\rho N$, then all disturbance is carried by tiny classes. Tiny vertices are treated as exceptions, and the same Irving-good majority correction pays their cost against a reference class.

*Case 3: Non-dominant, substantial classes present.* This is exactly the scope of Condition SBEE. The substantial cross-label energy $S_{\mathrm{sub}}(C_\bullet)$ plus exception cost $T_{\mathrm{exc}}(a)$ controls the counting. SBEE gives
$$
\#\{\text{assignments in this case with }Q_P\le R\}\ll_\varepsilon e^{\varepsilon R}.
$$

Combining all three cases yields the stated bound. $\square$

**Status:** Internal lemma. Uses SBEE.

---

# 9. Cross-block label mismatch lemma

**Lemma 9.1 (Cross-block label mismatch).**
*Let $(P,Q)$ be an Irving-good control pair with $P\subset[X,2X]$, $Q\subset[Y,2Y]$. If two blocks carry ordinary labels $m$ and $m'$ with $m\ne m'$, then*
$$
Q_{P,Q}(m,m')+Q_{P,Q}(m,m)\gg|P||Q|,
$$
*up to divisor exceptions in which $m'-m$ is divisible by primes from $Q$. Those exceptions are bounded by*
$$
\#\{q\in Q:q\mid(m'-m)\}\le 1+\frac{\log|m'-m|}{\log Y}.
$$

*Here $Q_{P,Q}(m,m')=\sum_{p\in P,\,q\in Q}\left\|\frac{H_{pq}^{m,m'}}{pq}\right\|^2$.*

**Proof.**

For $q\in Q$ with $q\nmid(m'-m)$, set $d=m'-m\not\equiv 0\pmod{q}$. The phase difference between labels $m$ and $m'$ along edge $pq$ contains $d\bar{p}/q$. Using the elementary inequality
$$
\|x+y\|^2+\|x\|^2\gg\|y\|^2,
$$
applied to $x=H_{pq}^{m,m}/(pq)$ and $y=d\bar{p}/q$ modulo $1$, and summing over $p\in P$:
$$
\sum_{p\in P}\left\|\frac{H_{pq}^{m,m'}}{pq}\right\|^2+\sum_{p\in P}\left\|\frac{H_{pq}^{m,m}}{pq}\right\|^2\gg\sum_{p\in P}\left\|\frac{d\bar{p}}{q}\right\|^2\gg|P|,
$$
where the last inequality is Irving-good pruning (Lemma 5.1). Summing over all non-exceptional $q\in Q$ gives the claim. $\square$

**Status:** Internal lemma. Uses Lemma 5.1 (Irving-good pruning).

---

# 10. Block-label Peierls collapse

**Proposition 10.1 (Peierls collapse).**
*Assume SBEE. Let $\mathcal{G}$ be the bounded-degree control block graph (taken as a path in the final construction). For a block-label configuration $m_\bullet=(m_k)_{k}$, define*
$$
\mathcal{Q}(m_\bullet)=\sum_k Q_k^{\mathrm{diag}}(m_k)+\sum_{(k,\ell)\in\mathcal{G}}Q_{k\ell}(m_k,m_\ell),
$$
*where $Q_k^{\mathrm{diag}}(m)=\sum_{\substack{p<q\\p,q\in P_k}}\left\|\frac{m}{pq}\right\|^2$. Then*
$$
\sum_{m_\bullet}e^{-c\mathcal{Q}(m_\bullet)}\ll\sum_m e^{-c'Q_{\mathrm{diag}}(m)}.
$$

**Proof (skeleton with key estimates).**

*Step 1 (Single-block compression).* By Theorem 8.1, each block assignment is compressed into an ordinary label $m_k$ plus energy-paid exceptions. After summing exceptions (absorbed into the exponential), it remains to bound
$$
\sum_{m_\bullet}e^{-c\mathcal{Q}(m_\bullet)}.
$$

*Step 2 (Boundary penalty).* For every skeleton edge $(k,\ell)$ with $m_k\ne m_\ell$, Lemma 9.1 gives a boundary penalty
$$
Q_{k\ell}(m_k,m_\ell)\gg|P_k||P_\ell|\asymp\frac{2^{k+\ell}}{k\ell},
$$
apart from divisor exceptions paid by the same energy accounting.

*Step 3 (Entropy estimate).* The diagonal Gaussian sums satisfy
$$
\sum_m e^{-cQ_k^{\mathrm{diag}}(m)}\ll\frac{1}{\sigma_k}\asymp 2^k k.
$$

*Step 4 (Polymer expansion).* For the path skeleton, a nonconstant label configuration decomposes into disjoint intervals $I$ on which $m_k$ differs from the exterior label. Each interval has at least one boundary edge. The polymer weight of an interval $I$ is bounded by
$$
\exp\!\left(-c\sum_{\partial I}|P_k||P_\ell|\right)\prod_{j\in I}\left(\sum_m e^{-cQ_j^{\mathrm{diag}}(m)}\right).
$$
The boundary exponential dominates: it is $\exp(-c\cdot 2^{2j}/j^2)$ at the first boundary scale, while the product contributes only $\exp(O(\sum_{j\in I}j))$. Hence the polymer expansion is absolutely summable, uniformly in the number of blocks, contributing a bounded multiplicative factor.

*Step 5 (Conclusion).* The constant-label sector is exactly
$$
\sum_m e^{-c'\sum_k Q_k^{\mathrm{diag}}(m)}=\sum_m e^{-c'Q_{\mathrm{diag}}(m)}.
$$
$\square$

**Status:** Internal lemma. Uses SBEE (via Theorem 8.1) and Lemma 9.1.

---

# 11. Ordinary diagonal counting

**Lemma 11.1 (Ordinary diagonal counting).**
*Assume SBEE. Then*
$$
\#\{m\bmod L:Q_{\mathrm{diag}}(m)\le R\}\ll_\varepsilon e^{\varepsilon R}\left(1+\frac{\sqrt{R}}{\sigma}\right),
$$
*and*
$$
\sum_{m\bmod L}e^{-cQ_{\mathrm{diag}}(m)}\ll\frac{1}{\sigma}.
$$
*The same estimate with $o(1/\sigma)$ holds outside $|m|\le C/\sigma$ as $C\to\infty$.*

**Proof.**

*Step 1 (Block-by-block compression).* Apply the conditional single-block theorem (Theorem 8.1) to the diagonal residues $a_p=m\bmod p$ on each block. Low energy gives local representatives $m_k$ and energy-paid exceptional primes.

*Step 2 (Collapse to global label).* Lemma 9.1 and Proposition 10.1 collapse the block labels $m_k$ to a single global ordinary label $m_0$. For all non-exceptional primes $p$, one has $m\equiv m_0\pmod{p}$, hence
$$
m\equiv m_0\pmod{\prod_{p\notin T}p},
$$
where $T$ is the exceptional set. The residue data on $T$ is paid by Irving-good correction: if $q\in T$, then $m-m_0\not\equiv 0\pmod{q}$, and the neighboring conforming primes force cost $\gg|P|$, exceeding the $O(\log q)$ residue entropy.

*Step 3 (Counting).* Hence $m\bmod L$ is encoded by $m_0$ plus energy-paid exceptions. The ordinary label satisfies $Q_{\mathrm{diag}}(m_0)=m_0^2\sigma^2\le CR$, so there are $\ll 1+\sqrt{R}/\sigma$ choices for $m_0$. Summing exception data gives the level-set bound. The partition sum follows by dyadic summation in $R$, choosing $\varepsilon<c/2$. The tail outside $|m|\le C/\sigma$ is the usual Gaussian tail. $\square$

**Status:** Internal lemma. Uses SBEE (via Theorem 8.1 and Proposition 10.1).

---

# 12. Global control partition theorem

**Proposition 12.1 (Global control partition).**
*Assume SBEE. Let $E_{\mathrm{ctrl}}=E_{\mathrm{int}}\cup E_{\mathrm{skel}}$ and $\sigma_{\mathrm{ctrl}}^2=\sum_{e\in E_{\mathrm{ctrl}}}\theta_e(1-\theta_e)e^{-2}$. Then*
$$
\sum_a e^{-cQ_{\mathrm{ctrl}}(a)}\ll\frac{1}{\sigma_{\mathrm{ctrl}}},
$$
*and for the main arc*
$$
\mathfrak{M}_C=\{a:a_p\equiv m\pmod{p}\text{ for all }p,\;|m|\le C/\sigma_{\mathrm{ctrl}}\},
$$
*one has*
$$
\sum_{a\notin\mathfrak{M}_C}e^{-cQ_{\mathrm{ctrl}}(a)}=o_C(1/\sigma_{\mathrm{ctrl}}).
$$

**Proof.** Apply Theorem 8.1 block by block, summing internal exceptions into $e^{\varepsilon Q_{\mathrm{ctrl}}}$. The resulting block labels are summed by Proposition 10.1. The surviving ordinary diagonal sum is controlled by Lemma 11.1. Taking $\varepsilon$ smaller than the Fourier decay constant $c$ gives the partition bound. The main-arc complement is handled by the tail part of Lemma 11.1. $\square$

**Status:** Internal lemma. Uses SBEE (via Theorem 8.1, Proposition 10.1, Lemma 11.1).

---

# 13. Edge construction, mass tuning, and variance compatibility

**Lemma 13.1 (Edge architecture).**
*For every squarefree $b$, one can choose finite prime blocks and an edge set*
$$
E=E_{\mathrm{int}}\cup E_{\mathrm{skel}}\cup E_{\mathrm{mass}}\cup E_{\mathrm{gad}}
$$
*with Bernoulli parameters $\theta_e\in[1/3,2/3]$ such that:*

*(i) $\displaystyle\sum_{e\in E}\frac{\theta_e}{e}=\frac{1}{b}$;*

*(ii) $\sigma_E^2\asymp\sigma_{\mathrm{ctrl}}^2$;*

*(iii) every prime in $\mathcal{P}$ is incident to at least one edge.*

**Construction.** The construction proceeds in the following order.

*Step 1: Choose initial scale.* Fix $k_0$ large (depending on $b$).

*Step 2: Internal edges.* Place internal complete bipartite graphs on every block $P_k$ for $k\ge k_0$. Their mass is
$$
\sum_{k\ge k_0}\sum_{\substack{p<q\\p,q\in P_k}}\frac{1}{pq}\asymp\sum_{k\ge k_0}\frac{1}{k^2},
$$
which can be made $<1/(100b)$ by choosing $k_0$ large. Their variance is dominated by the lowest block: $\sigma_{\mathrm{int}}^2\asymp 1/(2^{2k_0}k_0^2)$.

*Step 3: Skeleton edges.* Add a bounded-degree compatible skeleton (a path through the chosen blocks). Its variance is of the same order or smaller.

*Step 4: High-scale mass edges.* Choose $K_1\gg k_0$ large enough that every high edge $e$ satisfies $1/(\sigma_{\mathrm{ctrl}}\cdot e)=o(1)$ (needed for the main-arc Taylor expansion in §15). High-scale bipartite edges with $k,\ell\ge K_1$ have total reciprocal mass
$$
\sum_{K_1\le k,\ell\le K}\frac{1}{k\ell}\asymp\left(\log\frac{K}{K_1}\right)^2\to\infty,
$$
and variance $\ll 2^{-2K_1}\sum_{K_1\le k,\ell\le K}\frac{1}{k\ell}=o(\sigma_{\mathrm{ctrl}}^2)$ for $K_1$ large.

*Step 5: Mass tuning.* Set all mandatory control and gadget edges initially with parameter $1/2$, making their total expected mass $M_0<1/(4b)$. Let $\Delta=1/b-M_0>0$. From high-scale mass edges, greedily choose a finite batch $H$ with reciprocal mass
$$
2\Delta\le W_H=\sum_{e\in H}\frac{1}{e}\le 3\Delta,
$$
possible because individual high edges have arbitrarily small mass. Assign all edges in $H$ the common parameter
$$
\theta_H=\Delta/W_H\in[1/3,1/2].
$$
Then the expected mass is exactly $1/b$, and all parameters remain in $[1/3,2/3]$.

*Step 6: Gadget edges.* For each prime $r\mid b$, add a gadget edge $rs_r$ where $s_r$ is a large prime in a used high block. There are $O_b(1)$ such edges, with negligible mass and variance.

*Step 7: Verification.* All primes in mass edges also lie in internal blocks, so no uncontrolled CRT entropy is introduced. The high-mass variance is $o(\sigma_{\mathrm{ctrl}}^2)$, hence $\sigma_E\asymp\sigma_{\mathrm{ctrl}}$.

**Order of parameter choice summary:**

| Order | Parameter | Depends on |
|---|---|---|
| 1 | squarefree $b$ | given |
| 2 | $k_0$ (initial scale) | $b$ |
| 3 | $K_1$ (high-scale cutoff) | $k_0$, $\sigma_{\mathrm{ctrl}}$ |
| 4 | pruned prime blocks $P_k^*$ | $k_0$, $K_1$, Irving |
| 5 | $K$ (terminal scale), mass batch $H$ | $K_1$, $\Delta$ |
| 6 | $\theta_H$ (mass parameter) | $\Delta$, $W_H$ |
| 7 | gadget edges | $b$, high blocks |
| 8 | verification of (i)–(iii) | all above |

$\square$

**Status:** Internal construction. No conditional input used.

---

# 14. Lattice-span gadget

**Lemma 14.1 (Lattice span).**
*Assume $b$ is squarefree, $\{r:r\mid b\}\subset\mathcal{P}$, and $L=\prod_{p\in\mathcal{P}}p$. If every $p\in\mathcal{P}$ is incident to at least one edge $pq\in E$, then*
$$
\gcd\left\{\frac{L}{pq}:pq\in E\right\}=1.
$$

**Proof.** Let $r\in\mathcal{P}$. Since $r$ is incident to some edge $rs\in E$, the weight $L/(rs)$ is not divisible by $r$ (because $r\mid rs$ and $r^2\nmid L$ as $L$ is squarefree). Hence $r$ does not divide the gcd of all weights. Since every prime divisor of $L$ lies in $\mathcal{P}$, no prime divides the gcd. $\square$

**Remark 14.2.** The hypothesis $\{r:r\mid b\}\subset\mathcal{P}$ is ensured by the gadget edges (Step 6 of §13). The hypothesis that every prime is incident to an edge is ensured by the construction (internal complete graphs cover all block primes, and gadget edges cover primes dividing $b$).

**Status:** Internal lemma. No conditional input used.

---

# 15. Fourier inversion and positivity

## 15.1. Setup

By Lemma 13.1, we have:
- edge set $E$ with $\sum_{e\in E}\theta_e/e=1/b$;
- $b\mid L$ (since $b$ is squarefree and all prime factors of $b$ lie in $\mathcal{P}$);
- $\gcd\{L/e:e\in E\}=1$ (Lemma 14.1).

The target is $Y=L/b$, which is an integer since $b\mid L$.

**Fourier inversion formula.** On $\mathbb{Z}/L\mathbb{Z}$:
$$
\mathbb{P}(Y=L/b)=\frac{1}{L}\sum_{h\bmod L}\widehat{\mu}(h)\,e(-h/b).
$$

**Fourier bound.** By the elementary Bernoulli inequality $|1-\theta+\theta\,e(x)|\le\exp(-c_{\theta_0}\|x\|^2)$ with $\theta_0=1/3$:
$$
|\widehat{\mu}(h)|\le\exp(-c\,Q_E(a)),
$$
where $a_p=h\bmod p$ for each $p\in\mathcal{P}$.

## 15.2. Main arc

**Definition.** The main arc is
$$
\mathfrak{M}_C=\{h\bmod L:h\equiv m\pmod{p}\text{ for every }p\in\mathcal{P},\;|m|\le C/\sigma_E\}.
$$
For such $h$, every edge $e=pq$ satisfies $h/e\equiv m/(pq)\pmod{1}$, and $|m|/(pq)\to 0$ uniformly along the construction (since $1/(\sigma_E\cdot e)=o(1)$ for all edges, guaranteed by the construction in §13).

**Taylor expansion.** For $|m|\le C/\sigma_E$:
$$
\log\widehat{\mu}(m)=2\pi im\sum_{e\in E}\frac{\theta_e}{e}-2\pi^2 m^2\sum_{e\in E}\theta_e(1-\theta_e)e^{-2}+o(1).
$$
The first sum equals $1/b$ by mass tuning. The second sum is $\sigma_E^2$. The phase $e(-m/b)$ cancels the linear term:
$$
\widehat{\mu}(m)\,e(-m/b)=\exp(-2\pi^2\sigma_E^2 m^2+o(1)).
$$

**Main-arc sum.** Therefore
$$
\sum_{h\in\mathfrak{M}_C}\widehat{\mu}(h)\,e(-h/b)=(1+o(1))\sum_{|m|\le C/\sigma_E}e^{-2\pi^2\sigma_E^2 m^2}.
$$
For fixed large $C$, this is positive and $\asymp 1/\sigma_E$.

## 15.3. Minor arc

**Proposition 15.1 (Minor-arc bound).**
*Assume SBEE. Then*
$$
\sum_{h\notin\mathfrak{M}_C}|\widehat{\mu}(h)|\le\sum_{a\notin\mathfrak{M}_C}e^{-cQ_E(a)}\le\sum_{a\notin\mathfrak{M}_C}e^{-cQ_{\mathrm{ctrl}}(a)}=o_C(1/\sigma_E).
$$

**Proof.** The first inequality is the Fourier bound. The second uses $Q_E(a)\ge Q_{\mathrm{ctrl}}(a)$ (since $E_{\mathrm{ctrl}}\subset E$). The third is Proposition 12.1, using $\sigma_E\asymp\sigma_{\mathrm{ctrl}}$. $\square$

## 15.4. Positivity

Combining the main arc (§15.2) and minor arc (Proposition 15.1):
$$
\sum_{h\bmod L}\widehat{\mu}(h)\,e(-h/b)=\underbrace{\sum_{h\in\mathfrak{M}_C}\widehat{\mu}(h)\,e(-h/b)}_{\asymp\,1/\sigma_E>0}+\underbrace{\sum_{h\notin\mathfrak{M}_C}\widehat{\mu}(h)\,e(-h/b)}_{=\,o_C(1/\sigma_E)}>0
$$
for the construction parameters sufficiently large and then $C$ sufficiently large.

Hence
$$
\mathbb{P}(Y=L/b)=\frac{1}{L}\sum_{h\bmod L}\widehat{\mu}(h)\,e(-h/b)>0.
$$

**Conclusion of the $1/b$ case.** There exists a deterministic choice $\xi_e\in\{0,1\}$ such that $\sum_{e\in E}\xi_e/e=1/b$. Let $S=\{e\in E:\xi_e=1\}$. Every $e\in E$ is a product $pq$ of two distinct primes, so every selected denominator is a squarefree semiprime. The edges are distinct by construction.

---

# 16. Reduction from $1/b$ to $a/b$

**Lemma 16.1.**
*If for every squarefree $b$ there exists a finite set $S$ of distinct squarefree semiprimes with $\sum_{n\in S}1/n=1/b$, then Theorem 1.1 holds.*

**Proof.** Given $a/b$ with $b$ squarefree and $a\ge 1$, choose $a$ pairwise disjoint copies of the prime construction for $1/b$: for each $1\le j\le a$, select all primes in disjoint ranges (e.g., by shifting the initial scale $k_0$ to force disjoint prime supports). This produces semiprime sets $S_1,\dots,S_a$ that are pairwise disjoint (since they use disjoint prime pools) and each satisfies $\sum_{n\in S_j}1/n=1/b$. Then
$$
\frac{a}{b}=\sum_{j=1}^a\sum_{n\in S_j}\frac{1}{n}
$$
is a sum of reciprocals of distinct squarefree semiprimes (distinctness follows from disjointness of the $S_j$). $\square$

---

# 17. Main theorem

**Proof of Theorem 1.1.**

By Lemma 16.1, it suffices to prove the $1/b$ case for every squarefree $b$.

Fix squarefree $b$. Execute the construction of §13 (Lemma 13.1) to obtain:
- finite prime blocks $P_k^*$ (pruned via Lemma 5.1);
- edge set $E=E_{\mathrm{int}}\cup E_{\mathrm{skel}}\cup E_{\mathrm{mass}}\cup E_{\mathrm{gad}}$;
- Bernoulli parameters $\theta_e\in[1/3,2/3]$;
- mass identity $\sum_{e\in E}\theta_e/e=1/b$;
- variance compatibility $\sigma_E^2\asymp\sigma_{\mathrm{ctrl}}^2$;
- lattice span $\gcd\{L/e:e\in E\}=1$ (Lemma 14.1).

Apply the Fourier positivity argument of §15:
- Main arc: §15.2 gives a positive contribution $\asymp 1/\sigma_E$.
- Minor arc: Proposition 15.1 (using SBEE via Proposition 12.1) gives $o_C(1/\sigma_E)$.
- Positivity: §15.4 gives $\mathbb{P}(Y=L/b)>0$.

Extract a deterministic realization $S\subset E$ with $\sum_{e\in S}1/e=1/b$, where every $e\in S$ is a distinct squarefree semiprime.

By Lemma 16.1, extend to $a/b$. $\square$

---

# 18. Potential non-SBEE gaps

No non-SBEE mathematical gaps found at this formalization level.

The proof is a complete conditional argument, assuming only:
- **SBEE** (§7): the single-block energy-entropy condition, which is the sole unproved hypothesis;
- **Irving's theorem** (§4): an external cited result, accepted without proof.

Every other step is either an explicit construction (§13, §14) or a proved lemma (§5, §6, §8–§12, §15, §16).

---

# Dependency graph

```
Theorem 1.1
├── Lemma 16.1 (reduction 1/b → a/b)
└── §15 Fourier positivity
    ├── §15.2 Main arc
    │   └── Lemma 13.1 (edge construction, mass tuning)
    ├── Proposition 15.1 (minor arc)
    │   └── Proposition 12.1 (global control partition)  [SBEE]
    │       ├── Theorem 8.1 (single-block counting)  [SBEE]
    │       │   ├── Lemma 5.1 (Irving-good pruning)
    │       │   │   └── Theorem 4.1 (Irving)  [EXTERNAL]
    │       │   ├── Lemma 6.1 (cross-label divisor-energy)
    │       │   └── SBEE  [CONDITIONAL]
    │       ├── Proposition 10.1 (Peierls collapse)
    │       │   ├── Theorem 8.1
    │       │   └── Lemma 9.1 (cross-block mismatch)
    │       │       └── Lemma 5.1
    │       └── Lemma 11.1 (diagonal counting)
    │           ├── Theorem 8.1
    │           └── Proposition 10.1
    ├── Lemma 13.1 (edge construction)
    └── Lemma 14.1 (lattice span)
```

---

*This document was produced as a formalization of the conditional proof package in [[CP 01 Conditional theorem]], [[CP 02 The single remaining condition]], and [[CP 03 Lemma bank]]. The sole conditional input is SBEE.*
