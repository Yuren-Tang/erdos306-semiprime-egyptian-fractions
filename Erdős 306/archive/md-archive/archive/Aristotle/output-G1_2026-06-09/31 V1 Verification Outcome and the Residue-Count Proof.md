# V1 Verification Outcome and the Residue-Count Proof

Back to [[00 README]]. Records the outcome of the first verification pass (V1) of
the SBEE proof (notes [[29 SBEE Master - Dominant Case Proved, Window Isolated]] /
[[30 Theorem C - The Window Counted, SBEE Assembled]]) and proves, in full, the
most foundational remaining `sorry`.

## 1. Faithfulness review — PASSED (bodies checked this time)

After two earlier faithfulness misses, I checked the **definition bodies** of
every load-bearing object Aristotle produced (`SBEEDispersion.lean`,
`SBEEAssembly.lean`):

* `phase E q p = |E·(q^{-1} mod p).val/p − round(·)|` — the genuine reciprocal
  fractional norm $\|E\bar q/p\|$. **Faithful** (not stubbed).
* `lemmaD` / `lemmaD_fiber` — **faithful and fully PROVED** (no sorry): the
  deterministic dispersion engine. Machine-verified, standard axioms only.
  Aristotle's finding: the hypothesis $U<X$ is unnecessary (invertibility of $u$
  follows from $q\nmid w$). True and slightly more general.
* `fingerprint_count` (Theorem C) — **faithful**: uniform $C_\varepsilon,X_0$;
  bound $\#\{a:Q_P(a)\le R\}\le|P|\,e^{\varepsilon R}$; threshold
  $R\ge C_\varepsilon X^{2/3}\log^{4/3}X$.
* `SBEEPartitionBound` — **faithful, exactly note 28's design**: uniform $C$
  outside $\forall P$, an `IrvingGood` hypothesis, $2\le|P|$, no free labeling.

## 2. The pruning worry (note 28) is RESOLVED — no Irving pruning needed

Aristotle defined `IrvingGood P := ∃X>0, (P ⊆ primes∩[X,2X]) ∧ |P| ≥ X/(2\log X)`
— a **dyadic-window + density** predicate, *not* Irving's phase-dispersion
pruning. This is correct **because the notes 29/30 proof uses the deterministic
Lemma D, which holds for all prime blocks** — it needs no probabilistic dispersion
hypothesis. So:

> My note-28 fear that "structured blocks violate the bound, so pruning is needed"
> was an artifact of the old (probabilistic-Irving) route. The deterministic
> dispersion forbids any block — structured or not — from having too many
> low-energy assignments. The only block hypothesis the new proof needs is
> window + density (for the $\sigma_P\asymp N/X^2$, $N\asymp X/\log X$ relations).

`IrvingGood` is therefore faithful and non-vacuous; it is merely **misnamed**
(should be `DyadicPrimeBlock`). This is a genuine simplification: **the block
layer of SBEE needs no Irving/Kloosterman input at all.**

## 3. Status map

* **Machine-verified:** `lemmaD`, `lemmaD_fiber` (the dispersion engine).
* **Faithful, `sorry`:** `dispersion_residue_count`, `dispersion_energy_bound`
  (the bridge phase→Lemma D), `fingerprint_count` (Thm C), `theorem_A_dominant_count`,
  `lemma_E_cross_label_energy`, `theorem_B_nondominant_forcing`,
  `single_block_counting` (assembly).

So the statements are faithfully pinned and the foundation is verified; the
substantive counting is not yet machine-checked. **SBEE is not yet verified** — we
have the foundation + a faithful, honest map of the remaining work.

## 4. Full proof of `dispersion_residue_count` (the foundational bridge)

> **Claim.** $F$ a set of primes in $[X,2X]$, $|F|\ge8$; $q$ prime, $q\notin F$,
> $E\in\mathbb Z$, $q\nmid E$, $0<|E|<q$. With $\delta:=|F|/(32X)\le\tfrac14$,
> $$\#\{p\in F:\ \mathrm{phase}(E,q,p)\le\delta\}\ \le\ \tfrac{|F|}2.$$

*Proof.* Fix $p\in F$ with $\mathrm{phase}(E,q,p)\le\delta$. Let
$\bar q:=(q\bmod p)^{-1}\in\{0,\dots,p-1\}$. By definition there is an integer $r$
with $|E\bar q/p - r|\le\delta$, i.e. $|E\bar q - rp|\le\delta p$. Set
$s:=E\bar q-rp\in\mathbb Z$, $|s|\le\delta p\le\delta\cdot2X=|F|/16\le 2\delta X$.
Then $E\bar q\equiv s\ (\mathrm{mod}\ p)$, so multiplying by $q$ and using
$q\bar q\equiv1\ (p)$: $E\equiv sq\ (\mathrm{mod}\ p)$, i.e.
$$p\ \mid\ E-sq,\qquad |s|\le 2\delta X.$$
Now $E-sq\ne0$: if $E-sq=0$ then $q\mid E$, contradicting $q\nmid E$. And
$|E-sq|\le|E|+|s|q\le q+2\delta X\cdot 2X\le 2X+4\delta X^2\le 2X+X^2<X^3$
(using $\delta\le\tfrac14$, $X\ge2$). An integer $n$ with $0<|n|<X^3$ has at most
$2$ prime factors in $[X,2X]$ (three would give a product $\ge X^3>|n|$). Hence,
for each fixed $s$, at most $2$ primes $p\in F$ satisfy $p\mid E-sq$. Summing over
the $\le 4\delta X+1$ integers $s$ with $|s|\le2\delta X$:
$$\#\{p\in F:\ \mathrm{phase}\le\delta\}\ \le\ 2(4\delta X+1)\ =\ \tfrac{|F|}{4}+2\ \le\ \tfrac{|F|}2.\qquad\square$$

This needs only: the modular-inverse identity $q\bar q\equiv1\ (p)$; the
"$\le2$ prime factors in $[X,2X]$ of a nonzero integer $<X^3$" lemma (already
inside `lemmaD_fiber`'s proof — factor it out as `card_prime_factors_dyadic_le_two`);
and `Finset.card_le` over the $s$-fibres. It is elementary and deterministic.
`dispersion_energy_bound` then follows by the constant chase
$\delta^2\cdot|F|/2=|F|^3/(2^{11}X^2)$ (Aristotle reports its body already reduces
to this residue count).

## 5. Next

1. **Close `dispersion_residue_count`** (proof above) and hence
   `dispersion_energy_bound` — completing the **dispersion engine** in Lean
   (foundational, elementary). Factor `card_prime_factors_dyadic_le_two` out of
   `lemmaD_fiber`.
2. **Then `fingerprint_count` (Theorem C)** — cold rigidity (representative
   discipline of note 30 §1) + entropy bookkeeping; the crux.
3. Then A / E / B / assembly.

The faithfulness discipline (design the statement fully in [[28 Faithful SBEE Statement - Design (4th iteration)]];
check bodies) worked this round: no vacuity, no over-strength, and the pruning
question resolved in the simplifying direction. The remaining work is honest
formalization of elementary-to-moderate proofs we now have on paper.
