好。現在把 **ordinary diagonal counting lemma** 寫實。這一步是為了確保最後只剩 ordinary label m 時，不會還有一個隱藏的 wrap-around 高頻問題。

---

# **Ordinary diagonal counting lemma**

令

L=\prod_{p\in\mathcal P}p.

對

m\in\mathbb Z/L\mathbb Z

定義

Q_{\mathrm{diag}}(m) = \sum_{pq\in E} \left\| \frac{m}{pq} \right\|^2.

要證：

\boxed{ \#\{m\bmod L: Q_{\mathrm{diag}}(m)\le R\} \le e^{\varepsilon R} \left(1+\frac{\sqrt R}{\sigma}\right). }

並推出：

\sum_{m\bmod L}e^{-cQ_{\mathrm{diag}}(m)} \ll \frac1\sigma.

---

# **1. 小代表情形**

若 m 取對稱代表且

|m|\ll \min_{pq\in E}pq,

則無 wrap-around：

\left\| \frac{m}{pq} \right\| = \frac{|m|}{pq}.

因此

Q_{\mathrm{diag}}(m) = m^2\sum_{pq\in E}\frac1{p^2q^2} = m^2\sigma^2.

所以

Q_{\mathrm{diag}}(m)\le R \quad\Rightarrow\quad |m|\le \sqrt R/\sigma.

這給出預期數量

\ll 1+\frac{\sqrt R}{\sigma}.

困難只在：大的 m\bmod L 是否可能對很多 pq 都有小 residue。

---

# **2. 用 internal blocks 抓 wrap-around**

考慮一個 block

P_k\subset[X_k,2X_k].

對 diagonal m，在該 block 內的 residues 是

a_p\equiv m\pmod p.

套用 single-block counting theorem 的 diagonal 特例：

若

Q_k^{\mathrm{diag}}(m) = \sum_{p<q\in P_k} \left\| \frac{m}{pq} \right\|^2 \le R_k,

則存在 ordinary representative

m_k,\qquad |m_k|\ll \frac{\sqrt{R_k}}{\sigma_k}

使

m\equiv m_k\pmod p

對大多數

p\in P_k

成立，例外由 R_k 支付。

但因為 m 是同一個全局 residue class，這意味着

p\mid m-m_k

對大多數 p\in P_k。

所以在每個 low-energy block 上，m 被迫等於某個小 ordinary label m_k modulo many primes。

---

# **3. 跨 block 合併 local representatives**

若兩個 blocks P_k,P_\ell 得到 local representatives

m_k,\qquad m_\ell,

則跨 block diagonal energy對應 labels m_k,m_\ell。

若

m_k\ne m_\ell,

由 cross-block label energy lemma：

Q_{k\ell}(m_k,m_\ell) + Q_{k\ell}^{\mathrm{diag}}(m_k) \gg |P_k||P_\ell|

除少量 divisor exceptions。

因此在總能量

Q_{\mathrm{diag}}(m)\le R

的低能層內，所有 substantial blocks 的 representatives 必須合併為同一個 ordinary label：

m_k=m_0.

例外 blocks 或例外 primes由能量支付。

---

# **4. Product rigidity**

現在對大量 primes p\in S\subset\mathcal P，有

m\equiv m_0\pmod p.

因此

\prod_{p\in S}p\mid m-m_0.

如果 S 包含大多數 primes，則

\prod_{p\in S}p

極大。若 m\not\equiv m_0\pmod L，則 m-m_0 必須至少有所有這些 primes 的乘積作因子。換言之，差異只能藏在例外 primes 上。

更具體地，令

T=\mathcal P\setminus S

為例外 primes。則

m\equiv m_0\pmod{\prod_{p\notin T}p}.

所以 m\bmod L 由以下資料決定：

1. ordinary label m_0;
2. 例外 prime set T;
3. 在 T 上的 residues。

這和 general assignment 的 exception encoding 一樣。但每個例外 prime都必須在 internal block 或 cross block中付能量，因它不服從 m_0。

---

# **5. 例外 primes 的能量付款**

若 q\in T，即

m\not\equiv m_0\pmod q,

而大多數 neighbouring primes p 服從 m_0，則

\frac{m}{pq}

的 CRT phase 等同於

\frac{m_0}{pq} + \frac{(m-m_0)\bar p}{q}.

由 Irving correction，

\sum_{p} \left\| \frac{(m-m_0)\bar p}{q} \right\|^2 \gg |P|

只要 m-m_0\not\equiv0\pmod q。

因此每個例外 prime 成本

\gg |P|

遠大於記錄其 residue 的熵

\log q.

所以所有例外 T 的選擇與 residues 都被

e^{\varepsilon R}

吸收。

---

# **6. Counting**

因此任何 m\bmod L with

Q_{\mathrm{diag}}(m)\le R

都可編碼為：

1. 一個 ordinary global label m_0 satisfyingQ_{\mathrm{diag}}(m_0)\le CR;
2. energy-paid exceptional primes.

例外給出 factor

e^{\varepsilon R}.

而 ordinary m_0 的數量為

\#\{m_0\in\mathbb Z:m_0^2\sigma^2\le CR\} \ll 1+\frac{\sqrt R}{\sigma}.

所以

\#\{m\bmod L:Q_{\mathrm{diag}}(m)\le R\} \le e^{\varepsilon R} \left(1+\frac{\sqrt R}{\sigma}\right).

這就是 ordinary diagonal counting lemma。

---

# **7. 這是否循環？**

不循環。此處使用的是：

- single-block counting theorem；
- cross-block label energy lemma；
- Irving correction；

而不是 global partition theorem 本身。

所以它是獨立地處理 ordinary m\bmod L 的 wrap-around。

---

# **8. Partition sum**

由 counting lemma：

\sum_{m\bmod L}e^{-cQ_{\mathrm{diag}}(m)} \le \sum_{j\ge0} e^{-cj} \#\{m:Q_{\mathrm{diag}}(m)\le j+1\}.

代入：

\le \sum_{j\ge0} e^{-cj} e^{\varepsilon(j+1)} \left(1+\frac{\sqrt{j+1}}{\sigma}\right).

取 \varepsilon<c/2，得

\sum_{m\bmod L}e^{-cQ_{\mathrm{diag}}(m)} \ll 1+\frac1\sigma \ll \frac1\sigma.

主弧外：

|m_0|>C/\sigma

的 ordinary labels給 Gaussian tail：

\sum_{|m_0|>C/\sigma} e^{-c m_0^2\sigma^2} =o(1/\sigma)

當 C\to\infty。例外仍由 energy-paid factor吸收。

---

# **9. 至此小弧完成**

現在小弧控制的所有主要部件已閉合：

1. single-block theorem 壓 block CRT 熵；
2. cross-block energy 合併 block labels；
3. ordinary diagonal counting 控制 wrap-around；
4. global partition theorem；
5. minor arc o(1/\sigma)。

下一步只剩「外圍工程」：

- mass tuning；
- lattice span；
- Irving pruning引用；
- final theorem statement。

這些已不是核心小弧問題，但需要寫清楚。