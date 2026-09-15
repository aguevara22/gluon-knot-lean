# Continue from checkpoint091

The goal remains the corner state sum wall laws and soft theorem in TARGETS.md.
Checkpoint091 assembles all four printed clauses of lem:soft-generic as the
kernel-checked candidate SM.soft_family_generic_source. The complete source
and definitions still require stronger fidelity review and controlled canonical
integration. The accepted source map and327 canonical modules remain frozen.

Implement thm:A-soft next, then thm:C-soft and the remaining wall-law route.
A-soft is commissioned by the full cusp/comparison/anchor chain; it is not a
substitute for the final C theorem. Read reference/SM/sm-2-amplitude.tex1152–1467.
The DAG row has no explicit references, but the proof has substantial semantic
dependencies. Do not use its historical reviewed tag as a Lean certificate.

## Reuse existing proof machinery

Canonical NearFarTriangular.lean and TriangularPolynomial.lean provide the
inverse/uniqueness statements. NearFarFactorization.lean proves the complete
factorization. FarOnlyOutput.lean gives complete_output_near_independent,
reversedFar_output_of_solution, treeCoefficient_farOnly and the one-leaf cases.
GeometricNearFar.lean identifies the actual geometric open and root sums.
CompositionCutSet.lean, InteriorCutSet.lean and ConsecutiveCuts.lean supply
cut-set/composition and consecutive-part equivalences. Frozen external
FormalNearFarRecursion.body.lean and NearFarRingMaps.body.lean provide the
formal-recursion and coefficient-ring bridges. Use these bodies with their
existing receipts; do not reprove or silently integrate them.

## Next executable mathematical work

1. Define an ordered occurrence duplication model with arbitrary core size
   M+1, M>=2, and arbitrary distinguished position0<=s<=M. Insert B just after
   A=z_s. Prove the collapse map and all five source interval cases, including
   the singleton[A,B]; every other collapsed interval has distinct endpoints.
2. Construct actual cut-set/composition fibers and their inverses: a bijection
   outside the duplicate; two presentations for intervals starting at A; two
   for intervals ending at B; one for a spanning core composition avoiding A;
   three for a spanning core composition cutting at A. Include the unary term.
   Prove neighboring near-gate transport and all child-product identities.
3. Define the exact source auxiliary near arrays and ordinary-array table.
   Reindex the finite sums using those fibers. Verify all ordinary coordinates
   equal E before using nearFar_solution_unique. Verify root multipliers too.
   The spanning residual uses a*a=h*h=1, with a,h genuine signs. Unrestricted
   far scalars do not justify it. No division by a child/exterior factor is
   allowed, and auxiliary binary open sums must not be assumed zero.
4. Handle one-leaf core boundary intervals explicitly: their ordinary
   multipliers vanish by the cyclic neighbor identities. For s=0 the last
   endpoint contributes eta_minus; for s=M the first contributes eta_plus.
   Both full-root outputs give(eta_minus+eta_plus)/2. Restore geometric near
   arrays via the proved independence theorem.
5. Build one common positive radius for all far-array sign pullbacks using
   soft_new_nonattachment_chi_persists, chi_softInsertion_old,
   chi_softInsertion_new_attachment and softInsertion_attachment_signs.
   Prove the actual boundary-word collapse for every nonsoft physical root,
   including cyclic wrap. Incoming root is soft-first(s=0), return root is
   soft-last(s=M) and maps to parent edge E_j; other roots are internal.
   soft_parent_edges_exhaust, softParentEdge_injective and softParentEdge_next
   give edge correspondence but do not alone prove the root-cut word identity.
6. Intersect with the source epsilon0 and evaluate all three sign sectors.
   Preserve n>=3 and every nonsoft root; do not invoke a two-gon amplitude,
   root independence or wall laws to prove this theorem.

A read-only independent inventory by /root/review_relgp_full confirmed that
steps1–5 are not supplied by the existing contraction helpers. This is an
implementation inventory, not stronger fidelity approval or accepted proof.

## Direct C soft route still required

Read reference/SM/sm-4-knotlaws.tex984 onward. The assembled soft geometry is
available, but carrier correspondence, named-record/coefficient transport,
sector-specific uniformity and rotation arguments and support summation must
still be proved. Retain mixed-sector zero and loop omitted/newborn-selected
support cases. Prove the actual C identity; an abstract lawful quantity is
insufficient. The final R/full-cusp obligations also remain.

## Execution discipline

Keep all passing files/source/map/canonical modules frozen. Start a new frozen
baseline from checkpoint091 evidence/reviews before further implementation.
Use separate candidate bodies/prototypes and ledger, exact standard-only axiom
traces, and independent nonauthor technical review with contributions disclosed.
Preserve every failed body/prototype/log before proof-only repair. Root owns
one kernel/build/audit at a time; agents do not run kernels. Keep the hourly
app automation and one ten-minute watcher, relay its reports and stop its exact
handle on exit. Accepted source progress remains19/132; checklist39/192;
final targets0/8. No author question or source-map acceptance change is needed.
