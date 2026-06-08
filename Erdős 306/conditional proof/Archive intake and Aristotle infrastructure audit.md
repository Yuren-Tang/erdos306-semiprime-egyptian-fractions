# Archive intake and Aristotle infrastructure audit

Back to [[CP 00 Navigation]].

This note records what the newly imported archive and the second Aristotle package contribute to the conditional proof project. It is an intake note, not a replacement for [[CP 02 The single remaining condition]].

---

# 1. Snapshot

The raw imported materials are now stored under:

- `Erdős 306/archive/`
- `Erdős 306/Aristotle/output-final_aristotle_2/`
- `Erdős 306/kloost_paper2.tex`

The `.webarchive` file `AI對Lean 4支持分析.webarchive` was decoded enough to inspect the visible ChatGPT share text. Its useful content is a route-history record: it contains earlier discussions of SBEE, bucket exposure, Aristotle prompts, and warnings about several older high-frequency routes.

The raw `.webarchive` is the archival source. The large decoded HTML helpers are generated scratch artifacts and are ignored by git.

---

# 2. What Actually Helps

The second Aristotle package is genuinely useful because it formalizes the finite-combinatorial spine used by the current FIE/BCE route.

The useful formal components are:

- `FisherCounting.lean`: abstracts the marked dual large-sieve into the pair-disjoint Fisher inequality
  $$
  \sum_i\binom{|S_i|}2\le \binom{|U|}2.
  $$
- `BucketFingerprint.lean`: proves the greedy fingerprint lemma, giving a fingerprint of size $r$ that captures at least an $r/|U|$ fraction of incidence mass.
- `BucketContainer.lean` and `BucketExposure.lean`: assemble generated bucket cores and high-multiplicity containers, including
  $$
  |\mathcal V_h|\,h(h-1)\ll (rM)^2.
  $$
- `BucketBudget.lean`: proves the repeated-exposure budget
  $$
  |\mathrm{Idx}|\,m\le |U|M.
  $$
- `BipartiteCycles.lean`: supplies the ordered double-counting/common-neighbour mass bridge.
- `RankOneRigidity.lean` and `GeneralizedRankOne.lean`: formalize the rectangle-defect implication
  $$
  \Delta_{xy}a=0
  \Longleftrightarrow
  a(x,y)=\alpha(x)+\beta(y),
  $$
  in the generalized file over any additive abelian group.
- `InfrastructureAudit.lean`: verifies that these pieces import together and restates them with paper-aligned names.
- `PotentialTree.lean`, from the later Aristotle run, formalizes the finite
  binary-tree telescoping step: a local inequality
  $$
  C(v)+P(v_1)+P(v_2)\le P(v)
  $$
  implies the corresponding global bound for total internal cost plus leaf
  potential, with an optional weighted-saving version.

This supports the current scratch sections around marked dual counting, fingerprint exposure, first-level containers, repeated exposure budget, common-neighbour mass, and low-mode rank-one rigidity.

---

# 3. What It Does Not Close

The imported material does not prove SBEE. It also does not prove the reduced-ambient inverse theorem, shifted Irving-good charging, or any Fourier analytic estimate.

The remaining mathematical condition is now best stated as the log-corrected, ambient-sensitive recursive FIE descent plus its return to the SBEE ledger:

Given a non-dominant substantial labelled residual of mass $W$, short-list scale $s$, and
$$
D=sL_X,
$$
one must show that saturated exposure steps decrease a two-parameter potential. A one-parameter mass recursion is not enough, because terminal leaves in a binary peeling tree would have total entropy of order $W\log(Ns)$.

The current state is a pair $(W,Y)$, where $Y$ is the available ambient universe. Use the potential

$$
\mathcal P(W,Y)
=
A\frac{W^4}{D^2X^2}
+
B\,W\log\frac{eY}{W}.
$$

Each saturated exposure step should produce a fingerprint with entropy small enough to be paid by the potential drop. The captured branch must live in a fingerprint-determined container of size

$$
Y_1\ll
\left(N+\frac{W^2}{D^2}\right)(\log X)^A,
$$
while the complement branch remains in ambient $Y$.

Concretely, after exposing a chunk of size
$$
\theta W,\qquad \theta\ge(\log X)^{-A},
$$
the split
$$
W_1=\lfloor \theta W/2\rfloor,\qquad W_2=W-W_1
$$
must satisfy a recursion whose total fingerprint entropy is dominated by
$$
\mathcal P(W,Y)-\mathcal P(W_1,Y_1)-\mathcal P(W_2,Y).
$$

Terminal leaves are then paid by telescoping decrease of the entropy term $W\log(eY/W)$, while the complementary large-list range is paid by the base-list lower bound on $R$. The final form must be a genuine saving statement: the cumulative ambient entropy drops must reduce the initial crude entropy $N\log s$ to $o(R)$, except in regimes already paid by forced energy.

The newest refinement separates this into a first-capture saving and a residual polylog-ambient compression problem. First capture removes the main $N\log D$ entropy. The remaining local task is to remove the $N\log\log X$ entropy left when the ambient has size $N(\log X)^K$.

The sharpest current form is more specific than average ambient multiplicity.
For a generated bucket core $\mathcal C$, the captured container
$A_h(\mathcal C)$ satisfies the new-bucket capacity bound

$$
\#\{v\in A_h(\mathcal C):n\in\mathcal B_\tau(v)\}\cdot h
\le
|\mathcal C|,
\qquad n\notin\mathcal C.
$$

If a second saturated generated core persists, the residual vertices determine
a polylog-dense two-core graph between the two bucket cores. The remaining
paper-side step is therefore a seed-generated two-core inverse: bucket
rectangles must either be energy-paid or force rank-one / near-dominant
structure, and the proof must remember that the cores have the form
$\mathcal C_i=N(F_i)$ for fingerprints $F_i$.

Equivalently, persistent saturation gives many residual vertices that are
cheap to many seed vertices in two fingerprints. The two-core rectangle graph is
the finite counting shadow of this two-fingerprint common-neighbour structure,
not the whole inverse problem by itself.

This is the current precise subcondition behind the route
$$
\mathrm{FIE}\Longrightarrow \mathrm{BCE}\Longrightarrow \mathrm{SBEE}.
$$

---

# 4. Archive Triage

The newly imported Markdown archive contains useful history, but most of it is not a new proof ingredient. The important distinctions are:

- `178.md` records an earlier multi-label entropy lemma. It is an ancestor of SBEE, but still too coarse because it says "cross energy pays entropy" without the recursive container ledger.
- `092.md` records mass tuning, integerization, and lattice-span setup. This agrees with the existing CP 03 edge/lattice material and is useful as a sanity check.
- `089.md`, `055.md`, and `129.md` record older high-diagonal, inverse-entropy, and modular-phase routes. They are useful cautions, but not the current FIE proof route.
- `316.md` is valuable as a handoff warning: it marks older single-block CRT Poincare / pair-kernel / pi-adic routes as context-heavy and easy to confuse with the current route.

No imported archive file appears to contain a completed proof of the log-corrected ambient-sensitive recursive FIE descent. The archive mainly confirms that the project should stay focused on that one condition rather than reopen earlier high-frequency side routes.

---

# 5. Current Working Directive

For the main conditional proof package, keep the single named assumption as [[CP 02 The single remaining condition|SBEE]].

For the proof attempt, work on the sharper internal target:

$$
\boxed{
\text{two-fingerprint common-neighbour inverse inside ambient-sensitive FIE}
}
$$

The Lean/Aristotle infrastructure can support the finite pieces, especially the
new-bucket capacity, seed-neighbour, and two-core density bookkeeping. The
remaining step is still a paper-side mathematical proof tying the generated
bucket-rectangle inverse to the SBEE counting ledger.
