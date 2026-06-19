好。現在處理 **edge-set architecture**，也就是怎樣同時滿足：

\text{mass tuning},\qquad \text{minor arc control},\qquad \text{variance scale compatibility}.

核心要求是：

\boxed{ \sigma_{\mathrm{ctrl}}\asymp \sigma_{\mathrm{total}}. }

否則會出問題：若主弧 Gaussian 方差由大量 uncontrolled mass edges 主導，而小弧 partition theorem 只用 control edges，則小弧 bound 可能只有

O(1/\sigma_{\mathrm{ctrl}})

而主弧是

\asymp 1/\sigma_{\mathrm{total}}.

若

\sigma_{\mathrm{total}}\gg\sigma_{\mathrm{ctrl}},

則

1/\sigma_{\mathrm{ctrl}}\gg1/\sigma_{\mathrm{total}},

小弧可能壓不過主弧。

---

# **1. 邊集合分層**

我們把邊分三類：

E=E_{\mathrm{int}}\cup E_{\mathrm{cross}}\cup E_{\mathrm{gad}}.

其中：

1. **Internal edges**  
    E_{\mathrm{int}}=\bigcup_k\binom{P_k}{2}.  
    用於 single-block compression。
2. **Controlled cross skeleton**  
    E_{\mathrm{skel}}\subset E_{\mathrm{cross}}.  
    用於 block-label merging。這部分需要 Irving-good pruning，最好 bounded degree。
3. **Additional mass edges**  
    E_{\mathrm{mass}}.  
    用於調 expectation。它們可多可少，但不能讓 variance 失控。

令

E_{\mathrm{ctrl}}=E_{\mathrm{int}}\cup E_{\mathrm{skel}}.

小弧用

Q_{\mathrm{ctrl}}.

總 Fourier coefficient 滿足

|\widehat\mu(a)| \le e^{-cQ_{\mathrm{total}}(a)} \le e^{-cQ_{\mathrm{ctrl}}(a)}.

所以 control edges 足以給 upper bound。  
但尺度必須配平：

\sigma_{\mathrm{ctrl}}^2 = \sum_{e\in E_{\mathrm{ctrl}}}\theta_e(1-\theta_e)e^{-2}

應與

\sigma_{\mathrm{total}}^2 = \sum_{e\in E}\theta_e(1-\theta_e)e^{-2}

同階。

---

# **2. Internal variance 的大小**

對 block

P_k\subset[2^k,2^{k+1}],

internal variance contribution：

\sigma_{k,\mathrm{int}}^2 \asymp \sum_{p<q\in P_k}\frac1{p^2q^2}.

因

\sum_{p\in P_k}\frac1{p^2} \asymp \frac{|P_k|}{2^{2k}} \asymp \frac1{2^k k},

所以

\sigma_{k,\mathrm{int}}^2 \asymp \frac1{2^{2k}k^2}.

因此 internal variance 由最低尺度 k_0 主導：

\sigma_{\mathrm{int}}^2 \asymp \frac1{2^{2k_0}k_0^2}.

故

1/\sigma_{\mathrm{int}}\asymp 2^{k_0}k_0.

這正是我們此前的 major arc scale。

---

# **3. Cross mass 與 cross variance**

對兩個 blocks P_k,P_\ell，cross mass：

W_{k\ell} = \sum_{p\in P_k,q\in P_\ell}\frac1{pq} \asymp \frac1{k\ell}.

cross variance：

V_{k\ell} = \sum_{p\in P_k,q\in P_\ell}\frac1{p^2q^2} \asymp \frac1{2^{k+\ell}k\ell}.

因此，高尺度 cross edges 可以提供相當可觀的 mass

\frac1{k\ell}

但 variance

\frac1{2^{k+\ell}k\ell}

非常小。

這是好事：我們可以用較高尺度 edges 調 mass，而不顯著增加 variance。

---

# **4. 設計原則**

選最低控制尺度 k_0。Internal edges at k_0 already give

\sigma_{\mathrm{ctrl}}\asymp 2^{-k_0}/k_0.

接着：

- control skeleton 只在尺度 \ge k_0，其 variance不會超過 internal lowest block同階；
- additional mass edges 選在更高尺度，使其 variance總和

\sigma_{\mathrm{mass}}^2 \le C\sigma_{\mathrm{ctrl}}^2

甚至

o(\sigma_{\mathrm{ctrl}}^2).

同時它們的 mass總和可達到需要的

1/(\theta b).

這可以做到，因為 mass 和 variance 的比例在高尺度非常有利：

\frac{W_{k\ell}}{V_{k\ell}} \asymp 2^{k+\ell}.

高尺度邊幾乎只加 mass，不加 variance。

---

# **5. 如何得到足夠 mass？**

若只取很高尺度，單個 block pair mass約

1/(k\ell).

要得到固定大小如 1/b，可以取很多 block pairs，因

\sum_{k,\ell\le K}\frac1{k\ell}

有 (\log K)^2 型增長。  
但若取太多 pairs，variance是否仍小？

總 variance：

\sum_{k,\ell\le K}\frac1{2^{k+\ell}k\ell}

由最低 k,\ell 主導。若所有 mass edges都取在 k,\ell\ge K_1 很高，則總 variance至多

\ll 2^{-2K_1}

級別，可令其小於 control variance。

而 mass：

\sum_{K_1\le k,\ell\le K}\frac1{k\ell} \asymp \left(\log\frac K{K_1}\right)^2

可通過取 K 巨大達到任意固定值。

所以 mass tuning 與 variance compatibility 可同時滿足。

---

# **6. 但 mass edges 的 primes 是否進入 character space，增加 entropy？**

是的，若加入更多高尺度 primes，它們也進入 \mathcal P，character space變大。  
但如果這些 primes不在 control internal edges中，就會出現無控制的 CRT residues。

因此所有加入的 primes都必須至少有 internal control edges所在 block。  
換言之，若用某些高尺度 blocks做 mass edges，就應把這些 blocks也納入 internal complete graph E_{\mathrm{int}}。

這沒問題；internal edges at high scales貢獻很小 variance與mass，但提供 local compression。

所以 architecture 是：

- 所有使用到的 large prime blocks都配 internal complete graph；
- cross mass edges在這些 blocks之間選取；
- cross skeleton可只連接這些 blocks成 bounded-degree graph以合併 labels。

這樣新增 high blocks 不會引入 uncontrolled entropy。

---

# **7. Control variance 包含所有 internal blocks**

若加入很多高 blocks，internal variance總和：

\sum_{k\ge k_0}\frac1{2^{2k}k^2}

仍由 k_0 主導，收斂。  
所以即使加入極多高 blocks，\sigma_{\mathrm{ctrl}} 不會爆炸。

Control partition theorem也可處理很多 blocks；block-label Peierls在長 chain上仍成立，因 boundary costs增長而shape entropy只是多項/指數小。

---

# **8. Cross skeleton for many blocks**

若使用 blocks

k_0\le k\le K

很多，取 skeleton例如：

k\leftrightarrow k+1

或 4/3-jump plus connectors，只要 compatible and Irving-good。

每個 block degree O(1)。  
Skeleton variance：

\sum_k \frac1{2^{k+k+1}k(k+1)}

也由 k_0 主導，與 internal variance同階或更小。

Boundary cost足以 merge labels.

---

# **9. Final edge-set architecture**

選擇：

1. Blocks P_k for k_0\le k\le K, with k_0 large.
2. Internal complete edges for every P_k.
3. Skeleton cross edges between P_k,P_{k+1} or compatible bounded-degree pairs.
4. Additional mass edges between high blocks K_1\le k,\ell\le K, possibly many pairs, to tune mass.
5. Gadget edges for r\mid b.

Ensure:

\sigma_{\mathrm{total}}^2 \asymp \sigma_{\mathrm{ctrl}}^2 \asymp \frac1{2^{2k_0}k_0^2}.

Mass:

W_{\mathrm{total}} = \sum_{e\in E}\frac1e

can be tuned so

\theta W_{\mathrm{total}}=1/b.

---

# **10. Minor arc with mass edges**

Since all primes in mass edges also have internal control, their residues are compressed.  
Mass edges only add energy, never weaken minor arc.  
Even if mass edge block graph is dense, we do not need Irving pruning for all of them; we can ignore them in control estimate. They increase Q and \sigma_{\mathrm{total}} slightly, but variance controlled.

Thus full proof uses:

Q_{\mathrm{total}}\ge Q_{\mathrm{ctrl}}.

and

\sigma_{\mathrm{total}}\asymp\sigma_{\mathrm{ctrl}}.

Therefore

\sum e^{-cQ_{\mathrm{total}}} \le \sum e^{-cQ_{\mathrm{ctrl}}} \ll 1/\sigma_{\mathrm{ctrl}} \asymp 1/\sigma_{\mathrm{total}}.

This closes the scale compatibility issue.

---

# **11. 下一步**

現在 architecture也閉合了。  
最後可寫 final proof in one piece，帶 squarefree b 假設和上述 edge construction。