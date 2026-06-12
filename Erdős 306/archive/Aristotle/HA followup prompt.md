# Follow-up Prompt for Aristotle

Please continue from the previous Lean 4 formalization of the conditional proof for Erdős Problem 306.

The previous run compiled but left two `sorry`s:

1. `reduction_to_unit_numerator`;
2. `fourier_positivity`.

The first `sorry` is caused by an interface problem, not by a mathematical gap. The current hypothesis

```lean
∀ (b : ℕ), 0 < b → Squarefree b → HasEgyptianSemiprimeRepr ((1 : ℚ) / b)
```

is too weak to prove the reduction from $1/b$ to $a/b$, because it only gives one representation of $1/b$ and does not let us choose $a$ pairwise disjoint copies. The mathematical proof uses the fact that the whole prime construction can be started above an arbitrary finite scale, so it can avoid any finite set of previously used denominators/prime factors.

Please revise the Lean interface as follows.

## 1. Add an avoiding version of the representation predicate

Add a denominator-avoidance predicate, which is enough for the reduction:

```lean
def HasEgyptianSemiprimeReprAvoiding (T : Finset ℕ) (r : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, IsSemiprime n) ∧
    Disjoint S T ∧
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = r
```

Optionally also add the stronger prime-support avoidance version:

```lean
def UsesOnlyPrimesOutside (S F : Finset ℕ) : Prop :=
  ∀ n ∈ S, ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∉ F

def HasEgyptianSemiprimeReprAvoidingPrimes (F : Finset ℕ) (r : ℚ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, IsSemiprime n) ∧
    UsesOnlyPrimesOutside S F ∧
    (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = r
```

But the denominator-avoidance version is sufficient and should be easier for Lean.

## 2. Replace `fourier_positivity` by an avoiding version

The Fourier/probabilistic construction in `CP 01 Conditional theorem.md`, Sections 3--7, and `CP 03 Lemma bank.md`, Lemmas 9--10, has a free initial-scale parameter $k_0$. Therefore it can be run after excluding any finite set of old denominators. The high-scale mass edges, gadget edges, and control blocks are all chosen beyond that finite obstruction.

Please formulate the SBEE-derived unit case as:

```lean
lemma fourier_positivity_avoiding
    (hSBEE : ConditionSBEE)
    (T : Finset ℕ)
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b)
```

At the current abstraction level of the Lean project, do not try to formalize all analytic Fourier estimates down to epsilon details. Instead, make this the abstract interface for the document-level proof:

- It is proved mathematically by the edge construction, lattice-span gadget, Fourier inversion, main-arc Taylor expansion, and minor-arc bound from the global control partition under SBEE.
- It is not an additional mathematical condition beyond SBEE.
- If the Lean skeleton cannot derive it from the current `ConditionSBEE : Prop` definition, replace `ConditionSBEE` by a small structure/interface that includes this SBEE-derived avoiding unit theorem as the downstream consequence used by the main theorem, and document that this field represents CP 01 §§3--7 conditional on SBEE.

The goal is to avoid an unexplained `sorry`: either prove this from the chosen abstraction layer, or expose it as the single named SBEE-derived analytic interface. Do not leave it as an anonymous `sorry`.

## 3. Prove the reduction from the avoiding version

Then prove the reduction by induction on `a`.

Suggested statement:

```lean
lemma reduction_to_unit_numerator_avoiding
    (h : ∀ (T : Finset ℕ) (b : ℕ),
      0 < b → Squarefree b →
      HasEgyptianSemiprimeReprAvoiding T ((1 : ℚ) / b))
    (b : ℕ) (hb : 0 < b) (hbsf : Squarefree b) :
    ∀ a : ℕ, HasEgyptianSemiprimeRepr ((a : ℚ) / b)
```

Proof idea:

- Base case `a = 0`: use the empty finset.
- Inductive step: suppose `S` represents `a/b`.
- Apply `h S b hb hbsf` to get a new representation `U` of `1/b` with `Disjoint U S`.
- Use `S ∪ U`.
- `Finset.sum_union` and disjointness give the sum:
  $$
  \sum_{n\in S\cup U}\frac1n
  =
  \frac ab+\frac1b
  =
  \frac{a+1}{b}.
  $$
- Semiprime-ness on the union follows from semiprime-ness on each piece.

Then the theorem for positive `a` follows immediately from this all-`a` statement.

## 4. Main theorem should use the avoiding unit theorem

The final theorem should become:

```lean
theorem erdos_306_conditional (hSBEE : ConditionSBEE)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hbsf : Squarefree b) :
    HasEgyptianSemiprimeRepr ((a : ℚ) / b) :=
  reduction_to_unit_numerator_avoiding
    (fun T b hb hbsf => fourier_positivity_avoiding hSBEE T b hb hbsf)
    b hb hbsf a
```

or the analogous version if `ConditionSBEE` is changed into a structure/interface.

## 5. Expected result

After this change:

- `reduction_to_unit_numerator` should no longer need `sorry`;
- the disjoint-prime-pool issue is represented by the avoiding theorem, matching the written proof;
- the remaining analytic content should be a single named SBEE-derived interface, not an anonymous `sorry`;
- the summary should say clearly that the Lean file is an abstract dependency formalization, while the mathematical proof of `fourier_positivity_avoiding` is the document-level Fourier argument from CP 01 and CP 03, conditional on SBEE.

Do not work on SBEE/FIE in this follow-up. SBEE remains the unique mathematical condition. The current task is only to repair the Lean abstraction boundary around the two `sorry`s.
