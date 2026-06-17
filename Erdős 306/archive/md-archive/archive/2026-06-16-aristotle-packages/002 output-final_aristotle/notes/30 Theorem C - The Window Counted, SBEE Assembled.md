# Theorem C: The Window Counted, SBEE Assembled

Back to [[00 README]]. Continuation of [[29 SBEE Master - Dominant Case Proved, Window Isolated]]
(setup and Theorems A, B are there). This note records the outcome of attacking
the window by the three announced routes: the multi-class energy route (i) and the
FIE-style entropy route (iii) **merged** into a single fingerprint argument that
counts the window — and in fact counts **everything** above $R\gtrsim X^{2/3+o(1)}$,
with no covering, no labels, and no Kloosterman input.

> ⚠️ **Status: claimed proof.** Every step is elementary and I have adversarially
> re-checked it (the checklist is §5), including numerical verification of the
> bookkeeping. But this session has already produced two over-confident claims,
> so this stands as *claimed pending independent verification* — it is now the
> ideal Lean target. If it survives, **the single-block counting condition (SBEE)
> is proved**.

## 1. Theorem C (fingerprint count)

> **Theorem C.** For every $\varepsilon\in(0,1)$ there are $C_\varepsilon,X_0$
> such that for $X\ge X_0$, any prime block $P\subset[X,2X]$, and any
> $$R\ \ge\ R_C:=C_\varepsilon\,X^{2/3}\log^{4/3}X\qquad(C_\varepsilon\asymp\varepsilon^{-4/3}),$$
> the **full** level set satisfies
> $$\mathcal N(R)=\#\{a:\ Q_P(a)\le R\}\ \le\ N\,e^{\varepsilon R}.$$

No dominance hypothesis; this counts all assignments.

*Proof.*

**Setup.** May assume $R\le R_{\rm triv}=\varepsilon^{-1}N\log2X$ (else trivial).
Fix once and for all (no entropy) the **fingerprint** $F\subset P$: the
$\lceil\varepsilon R/(2\log2X)\rceil$ smallest elements of $P$; note
$|F|\le N$ in this range, and $|F|\ge8$ for $X\ge X_0$.

For $q\in P\setminus F$ and a *candidate residue* $w\in\mathbb F_q$ define the
**vertex–fingerprint energy**
$$t_q(w):=\sum_{p\in F}\Big(\frac{H_{pq}(a_p,w)}{pq}\Big)^2,$$
where $H_{pq}(a_p,w)$ is the centered CRT representative of $(a_p\bmod p,\ w\bmod q)$.
For the actual assignment, $t_q:=t_q(a_q)$; the pair sets $\{(p,q):p\in F\}$ are
disjoint over distinct $q$, so
$$\sum_{q\notin F}t_q\ \le\ Q_P(a)\ \le\ R.$$

**Phase identity.** Writing $H=w+vq$ with $v\equiv(a_p-w)\bar q\pmod p$:
$|H|\ge q|v|-|w|\ge pq\,\big\|(a_p-w)\bar q/p\big\|-q$, hence
$$\Big\|\frac{(a_p-w)\bar q}{p}\Big\|\ \le\ \sqrt{t^{(p)}_q(w)}+\frac1X
\qquad\big(t^{(p)}_q(w):=\text{the }p\text{-term of }t_q(w)\big).$$

**Dispersion (Lemma D form).** For $q\notin F$ and any integer $E$ with
$E\not\equiv0\pmod q$, $|E|\le q/2$, and any $\delta\in(0,\tfrac14]$:
$\|E\bar q/p\|\le\delta$ forces $p\mid E-uq$ for some $|u|\le\delta p\le2\delta X$,
and $E-uq\ne0$ (since $|E|<q\le|uq|$ for $u\ne0$, and $u=0$ gives $E=0$);
$|E-uq|\le X+4\delta X^2<X^3$ has at most $2$ prime factors in $[X,2X]$. Hence
$$\#\{p\in F:\ \|E\bar q/p\|\le\delta\}\ \le\ 2(4\delta X+1).$$
With $\delta:=|F|/(32X)$ (note $\delta\le\tfrac14$): the right side is
$\le|F|/4+2\le|F|/2$, so
$$\sum_{p\in F}\big\|E\bar q/p\big\|^2\ \ge\ \delta^2\,\frac{|F|}2\ =\ \frac{|F|^3}{2^{11}X^2}\ =:\ G_F .$$

**Cold rigidity.** Call $q$ **cold** if $t_q<T:=G_F/7$, else **hot**. Claim: at
most one $w\in\mathbb F_q$ has $t_q(w)<T$.

*Representative discipline (re-verified — a real subtlety).* Use **centered
integer representatives** $\tilde w\in(-q/2,q/2]$ for residues mod $q$. The phase
identity then reads, with $H=\tilde w+vq$ and $v\equiv(a_p-\tilde w)\bar q\ (p)$,
$\|v/p\|\le\sqrt{t^{(p)}_q(w)}+\tfrac1{2p}$, i.e. it controls
$\|(a_p-\tilde w)\bar q/p\|$ with the **fixed integer** $\tilde w$. (Crucially one
must NOT re-center the difference mod $q$ afterwards: for $E=E^*+kq$ one has
$\|E\bar q/p\|\ne\|E^*\bar q/p\|$ in general, since $\bar q\cdot kq\equiv k\ (p)$
adds $k/p$. So we keep the *un-recentered* integer difference.)

Suppose $w\ne w'$ both cold; set $E:=\tilde w'-\tilde w$, an integer with
$0<|E|<q$ and $E\not\equiv0\ (q)$. By the triangle inequality, for each $p\in F$,
$$\|E\bar q/p\|=\|(\tilde w'-\tilde w)\bar q/p\|\le\|(a_p-\tilde w)\bar q/p\|+\|(a_p-\tilde w')\bar q/p\|\le\sqrt{t^{(p)}_q(w)}+\sqrt{t^{(p)}_q(w')}+\tfrac1X,$$
so $\sum_{p\in F}\|E\bar q/p\|^2\le 3t_q(w)+3t_q(w')+\tfrac{3|F|}{X^2}<6T+1\le G_F$
for $X\ge X_0$ — contradicting the dispersion bound (which holds for any integer
$E\not\equiv0\ (q)$ with $|E|<q$; the proof there needs only $E-uq\not\equiv0\ (q)$
and $|E-uq|<X^3$, both fine for $|E|<q$, $|u|\le2\delta X$). $\square$

> **Verification note.** Re-deriving this adversarially fixed the
> representative/recentering point (note 30 originally said "$|E|\le q/2$" and
> "centered rep of $w-w'$" loosely); the corrected version above uses fixed
> centered integer reps and $|E|<q$, and the dispersion lemma's range is relaxed
> to $|E|<q$ accordingly. The argument survives. This is the kind of soft spot the
> Lean check must police.

**Encoding.** An assignment $a$ in the level set is determined by:
1. $a|_F$ — at most $(2X)^{|F|}$ choices; entropy $\le|F|\log2X\le\varepsilon R/2$;
2. the hot set and its residues — $h:=\#\text{hot}\le R/T=7R/G_F$, entropy
   $\le h(\log N+\log2X)\le 3h\log X$;
3. nothing else: every cold $q$ is recovered as *the unique $w$ with $t_q(w)<T$*
   (computable from $a|_F$; the true residue qualifies and is unique).

**Bookkeeping.** $G_F=|F|^3/2^{11}X^2\ge\varepsilon^3R^3/(2^{14}X^2\log^32X)$, so
$3h\log X\le 21\cdot2^{14}X^2\log^4 2X/(\varepsilon^3R^2)\le\varepsilon R/2$
exactly when $R^3\ge C\varepsilon^{-4}X^2\log^4X$, i.e. $R\ge R_C$. Total count
$\le N\cdot e^{\varepsilon R/2+\varepsilon R/2}$. $\blacksquare$

**Numerical check (done).** The ratios (fingerprint entropy)$/\varepsilon R$ and
(hot entropy)$/\varepsilon R$ behave as claimed across the window; the mesh
$R_C<R_w$ ($R_w$ from Theorem B) holds asymptotically, with crossover at
$X\approx10^{35}$ under the crude constants above (improvable; the statement is
asymptotic in $X$, which is the regime of the construction).

## 2. The assembled single-block counting theorem (= SBEE)

> **Theorem (single-block counting; claimed).** For every $\varepsilon>0$,
> $\rho\in(0,\tfrac14]$ there are $C_{\varepsilon,\rho},X_0$ with: for $X\ge X_0$
> and any prime block $P\subset[X,2X]$ with $N=|P|\ge X/(2\log X)$, and all
> $R\ge1$:
> $$\mathcal N(R)\ \le\ C_{\varepsilon,\rho}\,e^{\varepsilon R}\Big(1+\frac{\sqrt R}{\sigma_P}\Big).$$

*Proof.* Trichotomy on $R$ and dominance:
* $R<R_w$ ($R_w\asymp_\rho X/\log^3X$ from Theorem B): every level-set assignment
  is dominant (Theorem B), and the dominant count is
  $\le e^{\varepsilon R}(1+C_\rho\sqrt R/\sigma_P)$ (Theorem A).
* $R_w\le R\le R_{\rm triv}$: Theorem C applies (mesh: $R_C\ll R_w$
  asymptotically), giving $\le Ne^{\varepsilon R}\le e^{2\varepsilon R}$ for
  $X\ge X_0$; rescale $\varepsilon$.
* $R>R_{\rm triv}$: trivial.  $\blacksquare$

**Partition-function form** (what the circle method consumes): integrating the
level-set bound against $ce^{-cR}$ with $\varepsilon<c/2$ gives
$\sum_a e^{-cQ_P(a)}\le C/\sigma_P$ — the uniform single-block saving, i.e.
exactly the faithful `SBEEPartitionBound` designed in
[[28 Faithful SBEE Statement - Design (4th iteration)]].

## 3. Why this dissolves the FIE difficulty

The drafts fought the **label entropy at all $R$ simultaneously** — at small $R$
no fingerprint is affordable ($|F|\log X\le\varepsilon R$ fails), whence buckets,
ambient compression, polylog chases. The resolution is the **$R$-dichotomy**:

* below the window ($R<R_w$): no counting at all — *rigidity* (Theorems A+B): the
  level set is exactly the near-diagonal;
* in/above the window ($R\ge R_w\gg R_C$): the fingerprint is affordable
  ($|F|=\varepsilon R/2\log2X$), and cold vertices have **zero** entropy by
  reciprocal dispersion.

And the dispersion input everywhere is the **deterministic** Lemma D (an interval
of length $\le$ modulus meets a residue class in $\le2$ points + "an integer
$<X^3$ has $\le2$ prime factors $\ge X$") — **no Irving, no Kloosterman, no
polymer expansion, at the block level.**

## 4. Consequences for the project

If §1–§2 survive verification:
* **CP 02's "single remaining condition" (SBEE) is proved** — the named open gap
  of the conditional proof.
* Remaining for a full Erdős 306 proof: (a) the block-to-global chain
  (CP 03 §§5–8: cross-block mismatch, Peierls collapse, global partition —
  markdown, partially audited; note: the cross-block dispersion may *also* be
  deterministic by dispersing on the larger-modulus side — to check); (b) the
  circle-method layer (CP 01, audited standard); (c) formalization of all of it.
* The Lean path: formalize Lemma D, Theorems A, B, C against the faithful
  encoding of [[28 Faithful SBEE Statement - Design (4th iteration)]] — all four
  are elementary, finite, and now have explicit paper proofs to follow. This is
  the right next Aristotle task, and it now *verifies* rather than explores.

## 5. Adversarial checklist (what I verified before claiming)

1. Toy falsification: with a fake zero energy the proof must fail — it does (cold
   rigidity uses the *true* CRT pair energies via the phase identity).
2. Diagonals: max-label diagonal configs are cold throughout the window and are
   recovered from $a|_F$; their multiplicity is inside $(2X)^{|F|}$. Consistent.
3. Disjointness of pair sets in $\sum_q t_q\le R$; $F$ fixed in advance (no
   entropy); decoder computability of $t_q(w)$ from $a|_F$; existence+uniqueness
   for cold decoding.
4. Lemma D application legality: $E\not\equiv0\ (q)$; $|u|\le2\delta X<X$;
   $E-uq\ne0$; $\le2$ primes of $[X,2X]$ divide a nonzero integer $<X^3$.
5. All range conditions: $|F|\le N$ ⟺ $R\le2R_{\rm triv}$; $\delta\le1/4$;
   $|F|\ge8$; slack terms $12|F|/X^2\le1$.
6. Numerical bookkeeping across the window and the asymptotic mesh $R_C\ll R_w$
   (crossover $X\sim10^{35}$ with crude constants — large but explicit; the
   statement is asymptotic, matching the construction's regime).
7. Theorems A and B re-audited under the final parameter choices (constant $A$;
   $R_w\asymp X/\log^3X$; tiny-mass and $K$-conditions all hold in range).

Known soft spots for the verifier to scrutinize: the phase identity's slack
($|H|\ge pq\|\cdot\|-q$) at both ends of the window; the hot-set double counting
($t_q$ vs pairs inside $F$ — excluded by $q\notin F$); the exact constant chase in
$G_F$ and $T$; and Theorem B's covering bookkeeping (note 29 §6).
