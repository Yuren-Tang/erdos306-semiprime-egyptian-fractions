# Theorem C Decomposition: Phase Identity and Cold Rigidity

Back to [[00 README]]. After V2 the **deterministic dispersion engine is fully
machine-verified** (`lemmaD`, `card_prime_factors_dyadic_le_two`,
`phase_dvd_witness`, `dispersion_residue_count`, `dispersion_energy_bound`,
`phase_sub_le` — all sorry-free, standard axioms). Only `fingerprint_count`
(Theorem C) and the forcing/assembly layer remain. Aristotle could not formalize
Theorem C monolithically. This note **decomposes it into four sub-lemmas and
proves the two new/crucial ones in full** (phase identity; cold rigidity), so the
formalization proceeds in reachable steps.

Notation as in [[30 Theorem C - The Window Counted, SBEE Assembled]]: block $P$,
fingerprint $F\subset P$, for $q\in P\setminus F$ and residue $w$ (centered integer
rep $\tilde w\in(-q/2,q/2]$): $t^{(p)}_q(w):=(H_{pq}(a_p,w)/pq)^2$ where
$H_{pq}=\mathrm{crtRepr}\ p\ q\ a_p\ w$, and $t_q(w):=\sum_{p\in F}t^{(p)}_q(w)$.

## Sub-lemma 1 — Phase identity (the bridge crtRepr ↔ phase). **PROVED below.**

> **Lemma P1.** For primes $p,q$, $a_p\in\mathbb F_p$ (lift $\tilde a_p$), residue
> $w$ (centered $\tilde w$, $|\tilde w|\le q/2$):
> $$\mathrm{phase}(\tilde a_p-\tilde w,\ q,\ p)\ \le\ \frac{|H_{pq}(a_p,w)|}{pq}+\frac1X\ =\ \sqrt{t^{(p)}_q(w)}+\frac1X\qquad(p\ge X).$$

*Proof.* $H:=H_{pq}(a_p,w)$ satisfies $H\equiv\tilde w\ (\mathrm{mod}\ q)$, so
$H=\tilde w+vq$ for an integer $v$; and $H\equiv\tilde a_p\ (\mathrm{mod}\ p)$, so
$\tilde w+vq\equiv\tilde a_p\ (p)$, i.e. $v\equiv(\tilde a_p-\tilde w)\bar q\
(\mathrm{mod}\ p)$ where $\bar q=(q\bmod p)^{-1}$. Hence
$\mathrm{phase}(\tilde a_p-\tilde w,q,p)=\|(\tilde a_p-\tilde w)\bar q/p\|=\|v/p\|$.
Now $H/(pq)=\tilde w/(pq)+v/p$, so
$$\|v/p\|=\Big\|\frac{H}{pq}-\frac{\tilde w}{pq}\Big\|\le\Big|\frac{H}{pq}\Big|+\frac{|\tilde w|}{pq}\le\frac{|H|}{pq}+\frac{q/2}{pq}=\frac{|H|}{pq}+\frac1{2p}\le\frac{|H|}{pq}+\frac1X.$$
(First inequality: $\|x-y\|\le\|x\|+\|y\|\le|x|+|y|$ — fine, $\|x\|\le|x|$.)
Finally $|H|/pq=\sqrt{(H/pq)^2}=\sqrt{t^{(p)}_q(w)}$. $\square$

The only Lean ingredient beyond arithmetic is the decomposition $H=\tilde w+vq$
with $v\equiv(\tilde a_p-\tilde w)\bar q\ (p)$ from `crtRepr`'s congruences (already
available: `crtRepr_congr_left/right` in `BlockCRTEnergy.lean`), plus
`Int.fract`/`round` manipulation for $\|\cdot\|$.

## Sub-lemma 2 — Cold rigidity. **PROVED below** (given P1 + the verified engine).

> **Lemma P2.** Set $T:=G_F/7$ with $G_F=|F|^3/(2^{11}X^2)$, $|F|\ge8$. For
> $q\in P\setminus F$, at most one residue $w\in\mathbb F_q$ has $t_q(w)<T$.

*Proof.* Suppose $w\ne w'$ both satisfy it. Let $E:=\tilde w'-\tilde w$: integer,
$0<|E|<q$ (both reps in $(-q/2,q/2]$), and $q\nmid E$ (since $w\ne w'$ mod $q$).
For each $p\in F$, by `phase_sub_le` and Lemma P1 (applied to $w$ and to $w'$):
$$\mathrm{phase}(E,q,p)=\mathrm{phase}((\tilde a_p-\tilde w)-(\tilde a_p-\tilde w'),q,p)\le\mathrm{phase}(\tilde a_p-\tilde w,q,p)+\mathrm{phase}(\tilde a_p-\tilde w',q,p)\le\sqrt{t^{(p)}_q(w)}+\sqrt{t^{(p)}_q(w')}+\frac2X.$$
Squaring and using $(\alpha+\beta+\gamma)^2\le3(\alpha^2+\beta^2+\gamma^2)$, then
summing over $p\in F$:
$$\sum_{p\in F}\mathrm{phase}(E,q,p)^2\le3\,t_q(w)+3\,t_q(w')+\frac{12|F|}{X^2}<6T+1=\tfrac67G_F+1\le G_F$$
for $X\ge X_0$ (the $+1$ absorbs $12|F|/X^2\le1$ since $|F|\le N\ll X$, and
$\tfrac67G_F+1\le G_F\Leftrightarrow G_F\ge7$, true for $|F|\ge2^{11/3}X^{2/3}$ i.e.
in the window). But `dispersion_energy_bound` gives
$\sum_{p\in F}\mathrm{phase}(E,q,p)^2\ge G_F$ (its hypotheses $q\nmid E$, $0<|E|<q$
hold). Contradiction. $\square$

This uses **only** the already-verified `dispersion_energy_bound`, `phase_sub_le`,
and Lemma P1. It is the heart of Theorem C and is now fully reachable.

## Sub-lemma 3 — The decoding injection (counting).

> **Lemma P3.** Let $\mathrm{Hot}(a):=\{q\in P\setminus F: t_q(a_q)\ge T\}$. The map
> $$a\ \longmapsto\ \big(a|_F,\ \mathrm{Hot}(a),\ (a_q)_{q\in\mathrm{Hot}(a)}\big)$$
> is injective on $\{a:Q_P(a)\le R\}$.

*Proof.* From $a|_F$ and the hot data, recover each $a_q$: if $q\in F$ or
$q\in\mathrm{Hot}(a)$, it is given; if $q\in P\setminus(F\cup\mathrm{Hot}(a))$ (cold),
then $t_q(a_q)<T$, and by Lemma P2 $a_q$ is **the unique** residue with
$t_q(\cdot)<T$ — and $t_q(\cdot)$ is a function of $a|_F$ alone. So $a$ is
determined. $\square$

> **Lemma P3'.** $|\mathrm{Hot}(a)|\le R/T=7R/G_F$, since
> $\sum_{q\notin F}t_q(a_q)\le Q_P(a)\le R$ (disjoint pair sets) and each hot $q$
> has $t_q\ge T$.

## Sub-lemma 4 — Entropy inequality (real-analysis bookkeeping).

> **Lemma P4.** With $|F|=\lceil\varepsilon R/(2\log2X)\rceil$ and $h\le7R/G_F$: for
> $R\ge R_C:=C_\varepsilon X^{2/3}\log^{4/3}X$,
> $$\underbrace{(2X)^{|F|}}_{a|_F}\cdot\underbrace{\binom{|P|}{h}(2X)^{h}}_{\text{hot set+residues}}\ \le\ |P|\,e^{\varepsilon R}.$$

*Proof sketch (to formalize).* $\log\big[(2X)^{|F|}\big]=|F|\log2X\le\varepsilon
R/2+\log2X$. $\log\big[\binom{|P|}h(2X)^h\big]\le h(\log|P|+\log2X)\le 3h\log X\le
21R\log X/G_F$. Now $G_F=|F|^3/2^{11}X^2\ge(\varepsilon R/2\log2X)^3/2^{11}X^2$, so
$21R\log X/G_F\le C'X^2\log^4X/(\varepsilon^3R^2)\le\varepsilon R/2$ exactly when
$R^3\ge C''\varepsilon^{-4}X^2\log^4X$, i.e. $R\ge R_C$. Sum:
$\le\log|P|+\varepsilon R$. $\square$

## Assembly of Theorem C

$\mathcal N(R)=\#\{a:Q_P\le R\}\le\#\{\text{images}\}\le$ (Lemma P3 injection) $\le$
the product of Lemma P4 $\le|P|e^{\varepsilon R}$. $\blacksquare$

## Status and next (V3)

* **Now reachable & should be formalized next (heart):** Lemma P1 (phase identity)
  then Lemma P2 (cold rigidity) — both proved above, using only verified pieces.
  Getting P2 machine-checked confirms the **novel core** of the SBEE argument.
* **Then:** Lemma P3/P3' (injection + hot bound — finite combinatorics) and Lemma
  P4 (real-analysis inequality), assembling into `fingerprint_count`.
* Independently, the forcing layer A/E/B (`SBEEForcing.lean`) — Theorems A, B use
  the same Lemma D dispersion and are elementary (notes 29 §3,§6); they can be
  formalized in parallel.

The decomposition turns the "monolithic, failed" Theorem C into five reachable
Lean lemmas, two of which (the genuinely new ones) are proved here in full.
