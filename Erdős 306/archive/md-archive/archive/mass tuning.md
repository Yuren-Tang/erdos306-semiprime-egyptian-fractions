好。現在處理第一個外圍工程：**mass tuning**，即如何讓隨機和的期望精確等於

\frac1b.

---

# **1. 需要調什麼？**

隨機模型是

X=\sum_{pq\in E}\xi_{pq}\frac1{pq}, \qquad \mathbb P(\xi_{pq}=1)=\theta_{pq}.

我們需要

\mathbb E X = \sum_{pq\in E}\frac{\theta_{pq}}{pq} = \frac1b.

為了 Fourier 主弧乾淨，最好大多數邊有共同參數

\theta_{pq}=\theta

且

\theta\in[c,1-c].

少量 edge 可用來微調。

---

# **2. Internal edges 的 mass**

每個 block P_k\subset[2^k,2^{k+1}] 的 internal mass 是

W_k^{\mathrm{int}} = \sum_{p<q\in P_k}\frac1{pq}.

由

\sum_{p\in P_k}\frac1p \asymp \frac1k

可得

W_k^{\mathrm{int}} \asymp \frac1{k^2}.

所以

\sum_k W_k^{\mathrm{int}} \asymp \sum_k\frac1{k^2}

收斂。

這很重要：internal complete graph 是為 minor arc 控制而加入的，但它不會帶來發散 mass。它只貢獻一個可控的小常數量。

如果擔心 internal mass 太大，可以從很大的 k_0 開始，使

\sum_{k\ge k_0}W_k^{\mathrm{int}} \ll \frac1b.

---

# **3. Cross edges 的 mass**

跨尺度 edges 提供主要 mass。若對每對 compatible blocks P_k,P_\ell 加入完整二部 edges，則 mass 約為

W_{k\ell}^{\mathrm{cross}} = \sum_{p\in P_k,q\in P_\ell}\frac1{pq} \asymp \left(\sum_{p\in P_k}\frac1p\right) \left(\sum_{q\in P_\ell}\frac1q\right) \asymp \frac1{k\ell}.

若允許很多 compatible pairs，則

\sum_{k,\ell}\frac1{k\ell}

可做出需要的大小，甚至有 logarithmic divergence。  
因此 cross edges 負責把總 mass 調到約 1/b。

---

# **4. 具體調節策略**

選一個很大的起點 k_0，再選終點 K，令

E_{\mathrm{base}} = E_{\mathrm{int}}\cup E_{\mathrm{cross}}(k_0\le k,\ell\le K).

其總 mass

W(K)=\sum_{pq\in E_{\mathrm{base}}}\frac1{pq}

隨 K 增長而緩慢增加。

取 K 使

W(K)

略大於

\frac1{\theta b}

其中 \theta\in(0,1) 固定，例如 \theta=1/2。

若不能精確等於，就用最後一小批 edge 作微調：

- 可刪去部分 cross edges；
- 或令少量 \theta_{pq} 不等於共同 \theta；
- 或用一個 thinning parameter 在某一個 block-pair 上連續調節。

因為單個 edge mass

1/(pq)

可以取得極小，所以誤差可調到比 lattice spacing還細。

---

# **5. Edge-dependent probabilities 不會破壞 Fourier 分析**

若少量或一批 edges 用參數

\theta_{pq}\in[c,1-c]

而不是共同 \theta，則 Fourier bound仍成立：

|1-\theta_{pq}+\theta_{pq}e(x)| \le \exp(-c\|x\|^2)

其中 c 只依賴於

\min(\theta_{pq},1-\theta_{pq})

的下界。

主弧方差變成

\sigma^2 = \sum_{pq} \theta_{pq}(1-\theta_{pq})\frac1{p^2q^2}.

只要所有 \theta_{pq} bounded away from 0,1，Gaussian 主弧完全一樣。

所以 mass tuning 不會破壞小弧估計。

---

# **6. 若需要非常精確的期望**

Fourier positivity要求目標點靠近均值在 lattice 上精確對齊。最乾淨做法是讓

\mathbb E Y=L/b

其中

Y=LX.

若 \theta_{pq} 允許實數，精確調期望很容易。  
但最後我們要的是 existence of deterministic subset；Bernoulli probabilities 不必是 rational，因為只要

\mathbb P(Y=L/b)>0

即可。機率模型只是證明存在，不要求每個 \theta_{pq} 有算術意義。

所以可用連續參數 \theta_{pq} 精確調整期望。

---

# **7. 需要避免** \theta **太接近 0 或 1**

如果為了微調使用某些 edge 的 \theta_{pq} 很小，該 edge 對 Fourier damping 幾乎無用。這問題不大，只要主體 edges 保持 \theta\in[c,1-c]。  
但為簡潔，可採用兩層策略：

1. 大部分 edges 取固定 \theta=1/2，使 mass 接近 1/b 但略小；
2. 添加一個調節 block-pair，其 total mass 足夠覆蓋剩餘差額，並對其中所有 edges 使用共同參數 \theta'\in[c,1-c]。

因為 block-pair mass可選得與差額同量級，\theta' 不必極端。

---

# **8. Internal edges 對期望的處理**

Internal edges 是 minor arc 控制必需的。它們也進入隨機和，因此也貢獻期望。  
若不想它們干擾，可從非常高的 scales 開始，使 internal total mass很小；或者把它們計入總 mass，一起調節 \theta。

它們的存在不要求最終 subset 必須使用 internal edges；Bernoulli 模型會隨機選或不選。最後得到的 subset 自然可能包含 internal semiprimes，這完全合法。

---

# **9. 結論**

Mass tuning 沒有核心障礙：

\boxed{ \text{Internal edges 提供小而可控的固定 mass；cross edges 提供可調 mass；edge probabilities 可連續微調。} }

下一個外圍工程是 **lattice span / congruence obstruction**：確保目標點

L/b

真的在隨機和可達的格點 coset 裏，而不是被 gcd obstruction 排除。