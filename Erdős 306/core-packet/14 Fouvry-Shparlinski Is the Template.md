# Fouvry–Shparlinski Is the Template

Back to [[00 README]]. Prerequisites: [[11 Irving Toolbox and the Finish Roadmap]],
[[13 The Averaged Framing Is Essential]].

The paper Irving cites as `foushpar` — É. Fouvry & I. E. Shparlinski, *"On a
ternary quadratic form over primes"*, Acta Arith. 150(3) (2011), 285–314 — is now
in the repo (`archive/FS_ternary_quadratic_form_over_primes_ActaArith2011.pdf`,
CC-BY). It studies **exactly** the form $A(X,Y,Z)=XY+XZ+YZ$ over primes, and its
machinery is precisely our remaining toolkit. This is a major de-risking: the
core analytic gap is no longer "invent a theorem" but "adapt FS's published
Theorem 1.2 and its proof."

## 1. The structural match

FS study the multiset $\mathcal A_3(x)=(p_1p_2+p_1p_3+p_2p_3)_{p_i\sim x}$ and
prove (their **Theorem 1.2**) an asymptotic for
$\#\{(p_1,p_2,p_3): A(p_1,p_2,p_3)\equiv0\pmod q\}$, with explicit main term
$\prod_{p\mid q}(1-\tfrac1{(p-1)^2})\tilde\pi(x)^3/q$, **uniformly for
$1\le q\le x^{17/16-\epsilon}$** (improved to $x^{14/13}$ in their Thm 1.5).

Our anchored split-star (after eliminating $p$, [[08 Anchor Energy and the Joint Obstruction]] §3)
is the relation $q_iU_i+q_0V_i-q_4W_i=0$ — a ternary form of exactly the
$XY+XZ+YZ$ type, but in the *dual* organization: FS have three prime variables
and one modulus $q$; we have one prime $p$ and several seed moduli $q_i$ with
short box weights. The **exponential-sum inputs are identical** in both
organizations (reciprocal sums over primes + bilinear Kloosterman fractions +
Cayley's congruence), so FS's toolkit transfers.

## 2. The toolkit (now in hand, CC-BY, in repo)

* **Lemma 2.1** (short Kloosterman–Ramanujan sum): the completion bound; our
  [[12 M_B Computation and the Bilinear Necessity]] completion step is exactly
  this.
* **Cayley's congruence (2.2):** $\overline{n_1}+\overline{n_2}\equiv\overline{n_3}+\overline{n_4}\pmod q$,
  with $J_K(q)=\#\{$solutions, $n_i\le K\}$. This is the **same** object as our
  Lemma C difference relations ([[09 Cluster Concentration and the Structured Family]]).
  * **Lemma 2.2 (individual):** $J_K(q)\ll(K^{7/2}q^{-1/2}+K^2)q^\epsilon$.
  * **Lemma 2.3 (averaged, via Heath-Brown on Cayley's cubic surface):**
    $\sum_{q\sim Q}J_K(q)\ll(K^2Q+K^4)K^\epsilon$ — **the averaging that supplies
    the extra saving** missing from the individual bound.
* **Double sums $\mathfrak S=\sum_{\ell\sim L}|\sum_{m\sim M}\beta_m e(a\overline{\ell m}/q)|$:**
  Lemma 2.4; **Cor 2.5** (individual, three ranges); **Cor 2.6** (averaged over
  $q$); Lemma 2.7 ($\mathfrak S\ll\|\beta\|_\infty q^\epsilon(LM^{1/2}+q^{1/4}L^{1/2}M)$).
* **Theorem 3.1 (the central sum, composite modulus):**
  $$
  S_q(a;x)=\sum_{x<p\le2x}e\!\Big(\tfrac{a\overline p}{q}\Big)\ll(x^{15/16}+q^{1/4}x^{2/3})q^\epsilon,\quad (a,q)=1,\ x^{3/4}\le q\le x^{4/3}.
  $$
  Our $q\asymp X\asymp x$ is central in this range, and composite $q$ (we need
  $q_iq_4$) is allowed. This is the individual input.

## 3. How the averaging closes the deficit of note 13

[[13 The Averaged Framing Is Essential]] showed the individual saving
($\lesssim X^{1/10}$) is far short of the required $\sim X^{1/2}$, so the per-tuple
bound is false. FS resolve the identical gap: their **individual** inputs (Thm
3.1, Cor 2.5) are also too weak, but **averaging over $q$ via Lemma 2.3 + Cor
2.6** upgrades them to Theorem 1.2 — the asymptotic valid up to $q\le x^{17/16}$,
where the averaged error genuinely beats the main term. The arithmetic factor
$\Xi(q,L)$ that "can be very large for special $q$" (FS (1.4)) is precisely our
structured family: large for rare $q$, but $\sum_{q\sim Q}\Xi(q,L)\ll
L^{-1/2}Q(\log)^{\sqrt2-1}$, hence average-negligible. **FS (1.4)–(1.5) is the
literature form of [[09 Cluster Concentration and the Structured Family]] +
[[13 The Averaged Framing Is Essential]].**

So the mechanism that closes our deficit is already published: average the Cayley
congruence over the seed modulus (Lemma 2.3), feed Cor 2.6, recover the asymptotic.

## 4. Re-scoped remaining work

The gap is now **adaptation, not invention**:

1. Map our anchored split-star count $N_H'$ onto FS's framework: identify the
   seed modulus we average over (one $q_i$, with the others + $q_4$ as the
   bilinear coefficient data and AP weights), and the box variables $x_0,x_4,a_i$
   as the smooth weights $\beta$.
2. Run FS's Theorem 1.2 proof (their §3–§4) with these weights: Vaughan →
   $\mathfrak S$ double sums → Cor 2.6 (averaged) + Lemma 2.7, with Cayley moment
   via Lemma 2.3.
3. Track the box widths $H$ and the anchor modulus $q_4$ (FS have no anchor; this
   is the one genuinely new ingredient — a fourth modulus carrying a *linear*,
   not reciprocal, phase, which should only help).
4. Conclude the averaged $N_H'$ bound; feed to SBEE.

## 5. Status

* **The entire remaining analytic content is covered by FS's toolkit** (Lemmas
  2.1–2.7, Thm 3.1), all freely available and now in the repo.
* **FS's Theorem 1.2 is a direct template** for the averaged $N_H'$ bound.
* The genuinely new piece is the **anchor modulus $q_4$** (linear phase), which
  should be benign.
* This converts the bottleneck from open analysis to a scoped adaptation of a
  published proof — the most tractable the project has ever been.

## Next action

Begin the adaptation at step 1–2 for the cluster-only piece (no anchor): show the
averaged-over-$q_1$ version of $M_B$ matches FS's Theorem 1.2 specialization,
using their §3 proof with our box weights. Then add the anchor modulus (step 3).
