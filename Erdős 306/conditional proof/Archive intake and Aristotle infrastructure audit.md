# Archive intake and Aristotle infrastructure audit

Back to [[CP 00 Navigation]].

This note records what the newly imported archive and the second Aristotle package contribute to the conditional proof project. It is an intake note, not a replacement for [[CP 02 The single remaining condition]].

---

# 1. Snapshot

The raw imported materials are now stored under:

- `Erdős 306/archive/`
- `Erdős 306/Aristotle/output-final_aristotle_2/`
- `Erdős 306/Aristotle/output-final_aristotle_3/`
- `Erdős 306/Aristotle/output-final_aristotle_4/`
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
- `TwoCoreBookkeeping.lean`, from the next Aristotle run, proves the three
  finite implications needed after persistent second saturation: new-bucket
  capacity for one generated core, the two-core edge lower bound, and the fact
  that high degree into a generated core gives many seed neighbours.
- `SeededWitnessMatrix.lean`, from the later Aristotle run, proves the
  two-sided dependent-random-choice averaging lemma, packages witness matrices
  and zero mixed defect as additive rank one, and formalizes row differences and
  the common-divisor predicate used in the seed singularity reduction.
- `ClusterCoverBookkeeping.lean`, from the latest Aristotle run, proves the
  finite cluster-cover lemma: if every one-point extension of $T$ is contained
  in some cluster, then the seed pool lies in $T$ plus the union of clusters
  containing $T$, with the cardinal consequence $|F|\le |T|+RL$ when at most
  $R$ clusters contain $T$ and every cluster has size at most $L$.
- `AdaptiveClusterSelection.lean`, from the subsequent Aristotle run, proves
  the finite trichotomy around reciprocal clusters: either there is a good
  $k$-subset, or all $k$-subsets are covered and a low-codegree $(k-1)$-set
  gives the cluster-cover bound, or high codegree gives a large cluster-subset
  incidence ledger. It also proves the cardinal upper bound for this incidence
  in terms of cluster intersections.
- `ClusterLineIncidence.lean`, from the subsequent Aristotle run, proves the
  algebraic bridge from reciprocal-cluster congruences to integer line
  incidence, including the three-point determinant identity and the three- and
  four-point factorable relations.
- `ReciprocalCRTProduct.lean`, from the subsequent Aristotle run, proves the
  four-seed CRT product interface: base-difference equations, divisibility and
  modular residue forms, inverse witnesses, three local CRT congruences, and
  the paper-facing `CRTProductHit` bridge.
- `ValidCRTLattice.lean`, from the subsequent Aristotle run, upgrades bare CRT
  hits to valid quotient hits, proves the bridge with four-seed line witnesses,
  formalizes the homogeneous lattice and scaling/ray properties, and defines
  primitive CRT rays with basic scaling obstruction lemmas.
- `AnchoredCRTLattice.lean`, from the latest Aristotle run, restores the
  reference seed in the reciprocal-cluster equations, proves the bridge between
  anchored cluster witnesses and the normalized anchored lattice in both
  directions, proves anchored hits imply the unanchored valid hits, and
  formalizes the fourth local residue, homogeneous scaling, primitive
  anchored rays, and basic projection/divisibility diagnostics.
- `AnchoredSelectionPipeline.lean`, from the subsequent Aristotle run, connects
  the anchored cluster definition to the generic adaptive cluster-selection
  machinery: anchored witness membership, anchored bad-tuple coverage, the good
  tuple / all-covered dichotomy, the low-codegree cover bound, the
  high-incidence ledger, and a three-way endpoint pipeline.
- `AnchoredDeterminantRank.lean`, from the subsequent Aristotle run, proves the
  fixed-$p$ determinant obstruction for two anchored hits, the small-determinant
  projective-proportionality theorem, and the full six-relation anchored
  factorable shell.
- `LatticeSpan.lean`, `SemiprimeInfinity.lean`, and `BernoulliFourier.lean`,
  from the broad overview Aristotle run, formalize useful peripheral
  infrastructure: the lattice-span gcd lemma, existence of fresh semiprimes,
  and elementary Bernoulli characteristic-function estimates.

This supports the current scratch sections around marked dual counting, fingerprint exposure, first-level containers, repeated exposure budget, common-neighbour mass, and low-mode rank-one rigidity.

---

# 3. What It Does Not Close

The imported material does not prove SBEE. It also does not prove the reduced-ambient inverse theorem, shifted Irving-good charging, or any Fourier analytic estimate.

The broad overview Aristotle run is useful but must be interpreted carefully.
It removes syntactic `sorry` and `True := trivial` from its Lean package by
making several analytic steps tautological restatements of hypotheses and by
leaving the final avoiding theorem as a field of `ConditionSBEE`:

$$
\texttt{fourier\_positivity\_avoiding}.
$$

Thus it improves the formal interface, and its `LatticeSpan`,
`SemiprimeInfinity`, and elementary `BernoulliFourier` files can be mined for
supporting lemmas, but it does not prove the Fourier positivity argument or the
SBEE route. In particular:

- its `edge_construction` proves only existence of a fresh semiprime, not the
  full mass-tuned edge architecture;
- its `main_arc_positive` is a positive finite Gaussian sum, not the full
  main-arc Taylor expansion plus error control;
- its intermediate Peierls/global-partition lemmas assume the desired bounds as
  hypotheses and return them.

This is acceptable as scaffold, not as closure of the main mathematical gap.

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

The active draft now phrases the missing framework as a seeded witness-matrix
inverse. After fixing bounded seed tuples by a two-sided dependent-random-choice
extraction, each residual--seed cheap edge has a unique short witness

$$
n_{v,f}=m_t+p\alpha_{v,f}=m_u+q\beta_{v,f}.
$$

The matrix $(n_{v,f})$ has mixed defects

$$
\Delta(v,v';f,f')
=
n_{v,f}-n_{v,f'}-n_{v',f}+n_{v',f'}.
$$

Zero mixed defect gives additive rank one by the Lean-formalized rigidity
lemma. The remaining arithmetic task is to show that nonzero mixed defects are
energy-paid in the SBEE ledger, using the short bilinear equation

$$
p\alpha-q\beta=p_0(u-t).
$$

After choosing a reference seed $f_\ast=(q_\ast,u_\ast)$, this becomes a
large-prime gcd problem for the row-difference vectors

$$
D_v(f)=n_{v,f}-n_{v,f_\ast}
=p_0(u_f-u_\ast)+q_f b_f-q_\ast b_\ast.
$$

All coordinates of this vector are divisible by the same residual prime
$p_v\sim X$. The smallest current arithmetic bottleneck is to bound how often a
bounded seed-generated progression can contain vectors with such a common large
prime divisor, unless the seed data are rank-one / low-entropy structured.

The newest lattice-sieve formulation says: for fixed seeds, count the affine
codimension-$k$ slices

$$
q_i b_i-q_\ast b_\ast+p_0(u_i-u_\ast)\equiv0\pmod p.
$$

The regular case should be paid by the determinant-size lattice count. The
singular case is the existence of a short homogeneous kernel

$$
q_i x_i-q_\ast x_\ast\equiv0\pmod p,
$$

which must be counted as a low-entropy structured seed family.

The regular case has a particularly simple form: two short-box points in the
same affine slice differ by a short homogeneous kernel. Thus if no such kernel
exists, each residual prime contributes at most one witness pattern. The final
local bottleneck is therefore the seed singularity lemma: short homogeneous
kernels must occur only in a low-entropy seed family, or force the rank-one /
near-dominant structural exit. One non-reference seed is not enough, because
ordinary Dirichlet approximation can create short kernels around
$M_\tau\asymp X^{1/2}$. The DRC extraction must keep enough seeds so that

$$
M_\tau^{k+1}\ll X^{k-1}(\log X)^{-C}
$$

for the number $k$ of non-reference seeds used in the simultaneous kernel
condition. In the central case this means $k>3$, so four non-reference seeds are
enough up to logarithmic slack. The direct seed-singularity count is

$$
\#\{\text{singular seed prime tuples}\}
\ll
N^2M_\tau^{k+1}(\log X)^{O(1)},
$$

because after fixing $p,q_\ast,x_\ast$, each seed prime $q_i$ lies in one residue
class modulo $p$ for each short $x_i$. This is small compared with the free
count $N^{k+1}$ under the displayed condition. This proves global sparsity of
singular seed tuples, not yet the full fixed-configuration statement.

The remaining packaging step is a good-seed selection lemma: either the
fingerprint pool contains a seed tuple outside the sparse singular-tuple
hypergraph, or the pool is itself trapped in a low-entropy structured container.

The singular hypergraph has extra arithmetic structure: for fixed reference
seed $q_\ast$, residual prime $p$, and short coefficient $x_\ast$, bad seed
primes lie in a reciprocal cluster

$$
\mathcal A(p,q_\ast,x_\ast)
=
\{q\sim X:q\equiv q_\ast x_\ast x^{-1}\pmod p,\ |x|\ll M_\tau\},
$$

with $|\mathcal A|\ll M_\tau$. The selection problem is therefore a
container/covering statement for these reciprocal clusters, not an arbitrary
sparse hypergraph problem.

The active focused scratch for this last local issue is [[Reciprocal cluster cover proof draft]].

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

There is one important terminological trap. The word "lattice" appears in two
different roles:

- [[lattice statement]] and the old lattice-span gadget are final
  Fourier/local-CLT tools. They ensure
  $$
  \gcd_{pq\in E}\frac{L}{pq}=1
  $$
  after integerization, so the target has no global periodicity obstruction.
- Sections 20--21 of [[Ambient-sensitive FIE proof draft]] are the same local
  mechanism as the current reciprocal-cluster endpoint. They introduce affine
  slices
  $$
  q_i b_i-q_\ast b_\ast+A_i\equiv0\pmod p
  $$
  and identify the obstruction to regular uniqueness as a short homogeneous
  kernel
  $$
  q_i x_i-q_\ast x_\ast\equiv0\pmod p.
  $$

The latest `AnchoredCRTLattice.lean` formalizes the four-seed,
reference-preserving version of this second lattice. It should not be merged
conceptually with the global span gadget, though both are ultimately
periodicity obstructions in different layers of the proof.

No imported archive file appears to contain a completed proof of the log-corrected ambient-sensitive recursive FIE descent. The archive mainly confirms that the project should stay focused on that one condition rather than reopen earlier high-frequency side routes.

---

# 5. Current Working Directive

For the main conditional proof package, keep the single named assumption as [[CP 02 The single remaining condition|SBEE]].

For the proof attempt, work on the sharper internal target:

$$
\boxed{
\text{reciprocal-cluster covering for singular seeds}
}
$$

The Lean/Aristotle infrastructure can support the finite and algebraic pieces,
especially the new-bucket capacity, seed-neighbour, two-core density
bookkeeping, seeded witness matrices, cluster covers, line incidence, valid CRT
hits, the anchored CRT lattice, the anchored selection pipeline, and the
fixed-$p$ determinant rank theorem. The remaining step is still a paper-side
mathematical proof tying the generated bucket-rectangle / witness-defect inverse
to the SBEE counting ledger. In its current sharpest form, it is the weighted
reference-anchored primitive lattice inverse theorem:

$$
\begin{cases}
q_i x_i-q_4x_4=p\,a_i,&1\le i\le3,\\
q_4x_4-q_\ast x_\ast=p\,y_4,
\end{cases}
\qquad
p\sim X,
$$

with all short variables bounded by $M\le X^{1/2}(\log X)^A$. The desired
statement is that primitive short rays, weighted by their available scalar
multiplicity $M/H(r)$, are polylogarithmically sparse after summing over $p$,
unless the seed primes lie in a low-entropy rational structured family
acceptable to the FIE exception ledger. The regular affine-slice side has
reduced to uniqueness per residual prime; the singular anchored short-kernel
family is the part that still needs proof. The extracted focused note is
[[Anchored primitive concentration problem]].

After `AnchoredDeterminantRank.lean`, the fixed-$p$ fibre is controlled by a
projective-proportionality / small-determinant-quotient dichotomy. The next
exact algebraic step is primitive projective normalization: one projective class
should give only a sign pair after imposing primitivity. The remaining
paper-side arithmetic is then the distribution across different $p$ and the
entropy of the small-determinant / factorable-relation exceptions.
