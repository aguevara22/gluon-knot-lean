# Execution checkpoint — 2026-09-10

Accepted original source proofs: 10/132 (7.58%).
Accepted original checklist: 23/191 (12.04%): ten proofs and thirteen definitions.
One additional supporting source lemma, lem:weak-open, is independently accepted.
Expanded tracked checklist: 24/192 (12.50%; standard reporter reports 12.5%).
The original baseline and all eight main targets are unchanged. Main targets: 0/8.

Original accepted proofs: lem:chi-basic, lem:g1, lem:crossing-test,
lem:wall-segment-stability, prop:chambers, lem:rot, lem:uniformrot, lem:fibres,
lem:triple-sides, lem:flat-sides.
Accepted definitions: def:polygon, def:chirotope, def:generic, def:crossings,
def:chamber, def:weak, def:shift, def:gauss, def:interlace, def:visible, def:regular,
def:admissible, def:germ.
The main wall laws, soft theorem and unconditional R discharge remain pending.

## Latest work and evidence

All 162 SM modules compile on the exact pinned toolchain and are imported through
Supplemental.lean. Latest development audit: checks/checkpoint-038-output.json,
1632 local declarations, 24 mapped claims, only propext, Classical.choice and
Quot.sound. No literature axiom was used. Original session80844 is terminal
with exit0. Receipt SHA256:
23d75299bbcf8305e314e141e45f43f6f1bade0cf4365f5be74fbe31e30941ef.
The exact168-file project inventory and all project/frozen hashes match;
all24 accepted reviews and every supporting-file hash are current. The separate
shift counterexample/log/scope-review/repair bindings are unchanged; its repair
index now points to receipt038. Full-stage acceptance remains false.

Twenty new modules implement the E/C silent-wall geometry and partial V geometry.
SilentSides proves actual central and nearby crossing/visit records, every-edge
parameter comparisons, crossing-point distinctness, exclusion of all vertices,
regularity and noncritical chirotopes on one common radius. ContactCrossingSides
proves the exact two-pair symmetric difference and bigon/sliding alternatives
for independently chosen parameters on the two full connected Generic sides.
The finite-segment tests prove both required endpoint sign conditions. Other
supports persist, and ContactOrder proves all persistent parameter comparisons.
ContactVertices excludes all vertices from persistent central crossings;
ContactApproach proves both changing pairs' actual parameter limits.

At a V centre, raw IsCrossing includes the two endpoint-contact pairs. Only
explicitly unaffected pairs are certified transverse interior crossings there;
no global central CrossingGeometry or Generic word is asserted. Simultaneous
contact-neighbourhood separation, actual visit localization and the T/full
assembly are still unproved. Both lem:wall-sides and def:walls remain pending
and unmapped; these helpers add no original acceptance. The actual partial
type/definition/axiom trace passed (session89174, exit0), SHA256
bb59fbf90f7167a0b3663efb82f6ecb5b835f9da4029af39284f493102fdced6.
Trace: checks/named-wall-partial-types.log. Current inventory/review verification:
checks/checkpoint-038-verification.json. Independent partial review completed:
reviews/lem-wall-sides-partial-checkpoint038.md, SHA256
f175fedb57264f59d7c4212f8d7c62a588634aaa8923bdaa02ddf725e71085b6.
All 78 supporting-file hashes and its exact import closure match the receipt.
This partial review does not accept either full original claim.

Full original lem:flat-sides is independently accepted as SM.flat_sides.
Review: reviews/lem-flat-sides.json, SHA256
ed07a0b556323b4409efe25852fb981c5ad58e8167622bd2290d3bf45c643e7a.
It binds all91 supporting files and the110-entry semantic dependency hash
390e52915488af936ec194118130b4e6e0e9123922c47211147040be011980f2.
Candidate036 and final accepted-metadata037 passed. Actual type/definition/axiom
trace checks/flat-sides-types.log passed (session14374, exit0), SHA256
a41453ec0030a7e7740965ea1fd6e7e2334b523ad36aceacfe2264a24b5a4be4.
No build or audit command is running. The earlier033/034/035 partial reviews are
historical; they did not themselves accept the original row.

- Full weak openness is accepted as SM.weak_open. WeakGeometry proves the weak
  adjacent-interior and remote-closed-triple geometry. WeakTopology preserves
  every weak condition without G1, including disjoint parallel/collinear remote
  pairs. PolygonalConnected uses actual finite straight-segment chains.
  EuclideanTuple proves a homeomorphism to the genuine 2n-dimensional Euclidean
  coordinate space and positive-radius ball containment. WeakOpen assembles all
  source clauses for actual labelled visible components.
  Review: reviews/lem-weak-open.json. This source lemma was absent from the
  frozen focused DAG, so it is additional support, not another original proof.
- Full reversal definition is accepted as SM.reversal_definition. Reversal is
  exactly i -> P(2-i), fixes vertex 1, conjugates shifts to opposite shifts,
  and descends by the actual quotient map to polygons. Edge and turn reversal
  formulas verify the change of orientation. Review: reviews/def-shift.json.
- Full Gauss definition is accepted as SM.gauss_definition. Traversal and
  GaussVisits build the actual half-open traversal set, geometric evaluation,
  actual visits, finiteness, exactly two visits per crossing and distinct visit
  positions. GaussWord constructs the sorted list and the genuine rotation
  quotient, preserving repeated crossing labels and the empty word.
  TraversalRelabel proves order preservation on every traversal point;
  VisitRelabel gives the actual visit bijection. SortedCut and GaussRelabel
  compare independently constructed sorted words after cyclic relabelling.
  GaussDefinition includes strict sorting, exact length and two occurrences of
  each crossing. Review: reviews/def-gauss.json, with 16 supporting file hashes.
  This is a DEFINE row, not another original PROVE row. It does not establish
  interlacement, visible-signature constancy, record-polynomial invariance or
  topological link equivalence.
- Previously accepted chamber results retain their reviews. They use genuine
  connected components and quotient topology, including cyclic preimage
  decomposition into at most n labelled components and invariance of chirotope,
  actual crossing set and all crossing-parameter comparisons along paths.
- Full interlacement definition is accepted as SM.interlacement_definition.
  TraversalArcs proves complementary open arcs and four-point cyclic rotation.
  CrossingPair proves that any distinct pair exhausts the actual two-visit
  fibre. Interlacement and InterlaceCount prove symmetry and equivalence with
  exactly one y visit on the chosen x arc, for every choice of first x visit.
  InterlaceRelabel transports the actual fibres and order. InterlaceSupports
  builds the actual SimpleGraph, its complete powerset filter of independent
  supports (including empty), N(S) for arbitrary S, and U(S) as the exact
  complement of S union N(S). N(S) may meet S when S is not independent.
  The actual graph isomorphism, independent-support transport and exact N/U
  image equalities are proved. Review: reviews/def-interlace.json, 19 supporting
  file hashes. This is a DEFINE row; helper lemmas do not add original proofs.
- Full visible signature is accepted as SM.visible_signature_definition.
  CrossingTransport preserves actual crossing supports and visited edges.
  GaussFamilyOrder proves all visit-order comparisons constant in continuous
  preconnected generic families, using the accepted actual parameter-order
  theorem on a common edge. GaussFamily compares independently sorted complete
  lists and derives word equality under the canonical crossing equivalence.
  CycleMaps proves that injective letter maps preserve entire rotation classes.
  VisibleSignature builds the actual turn/crossing-set/Gauss-word triple using
  the faithful common alphabet of unordered edge supports, with exact letter
  inventory and length. VisibleRelabel proves the actual cyclic action on all
  three projections, including identity and composition. VisibleChambers proves
  exact equality on actual labelled connected components and equality up to an
  actual cyclic shift for arbitrary representatives over quotient chambers.
  This is the explicitly permitted source labelled/equivariant reading; no
  separate data quotient or unproved path-lifting assertion is used.
  Review: reviews/def-visible.json, 32 supporting file hashes. The source row
  is DEFINE despite including constancy proofs. Weak-visible-chamber constancy
  and the corner state sum's wall/soft laws remain separate pending obligations.
- Full regular-locus definition is accepted as SM.regular_definition.
  EuclideanPlane proves the genuine Euclidean norm and oriented rotor identities.
  RegularPairs/PrincipalAngles prove the exact strict-interval cosine/sign
  specification, existence and uniqueness. The domain excludes only zero edges
  and antiparallel consecutive edges, preserving positive collinearity and zero
  turns. Existence implies this domain without including it in the specification.
  RegularLocus proves all source edge/existence equivalences, Generic inclusion,
  and cyclic equivariance. Review: reviews/def-regular.json, ten supporting files,
  semantic hash 8a62d85fc1d8b3723b863093d7c2b1a555fc3064cd36980a36668c701bc9cfc2.
  This is one original DEFINE row, separate from the original PROVE count.
- Full lem:rot is independently accepted as SM.rotation_number.
  RotationNumber proves the actual real sum divided by 2*pi is an integer by
  telescoping genuine edge-argument classes. RotationContinuity proves equality
  at every pair of parameters of genuine continuous regular paths.
  RotationReversal uses the actual i -> 2-i map. RegularTriangle derives the
  nonzero common determinant from regular closing edges; RotationTriangle then
  proves signed unit rotation equal to every turn for the same triangle P.
  RotationBounds proves the strict bound by summing actual principal-angle bounds.
- The insertion clause is now complete. AngleScaling proves actual angle and
  regular-pair invariance under positive independent scalings. InsertionIndices
  retains old natural labels injectively, adds exactly index n, and proves all
  wraparound predecessor/successor identities. InsertedTuple constructs the
  actual edge-interior vertex and proves the split vectors are t and 1-t times
  the old edge. InsertionSum proves the entire finite index partition;
  AppendRotation proves every old angle unchanged and the new angle zero.
  VertexInsertion handles every original edge through its actual cyclic cut,
  proves the inserted point is on that original edge, preserves regularity,
  and gives equality of the actual rotation sums. No Generic, global vertex
  injectivity, noncrossing or supplied turn-inventory premise is introduced.
- RotationTheorem assembles all five source clauses, exact normalization and
  cyclic invariance. Independent full review: reviews/lem-rot.json, 24 local
  supporting files, semantic hash
  847dc8b72fa93fe2f7edc30e0d550f96ab2bfa0b2eb96bf047c15fc8d6b4c889.
  Candidate checkpoint 021 and final checkpoint 022 passed. The earlier partial
  checkpoint 020 review is historical; its missing insertion clause is now
  closed. This accepts one original PROVE row. Helpers add no original counts.
- Original sources, blueprint, provenance, templates and delivered ZIPs were
  not changed. python3 verify_bundle.py passed after the new implementation:
  25 source-context files, 59 bridge quotations, 172 source/clause rows and
  19 R/bridge/final obligations. This is source integrity, not a proof receipt.

- Full lem:uniformrot is independently accepted as SM.uniform_rotation.
  DirectionProjection constructs an actual Euclidean dot product and proves its
  finite additivity. CumulativeTurns proves the full actual turn-sum split,
  positive prefix bounds, and telescoping of genuine edge-direction classes in
  Real.Angle. NarrowSector constructs the middle direction of the actual short
  angle interval and proves every actual edge has strictly positive projection;
  this contradicts the actual zero edge sum. UniformRotation uses integrality,
  cyclic transport of the exceptional index and actual reversal to prove all
  four source cases on Regular with all turns nonzero. No Generic or supplied
  sector/functional premise is introduced. Review: reviews/lem-uniformrot.json,
  17 supporting files, semantic hash
  7ea25a7517b8ea35522431f42857e13a299aaae1e663beb9a2fda7db86ea4fc1.
  Candidate checkpoint 023 and accepted-metadata checkpoint 024 both passed.
  This adds one original proof; helpers do not change the baseline.

- Full def:admissible is independently accepted as SM.admissible_definition.
  Admissible and MinimalAdmissible retain the exact integer domain, strict
  inequality and excluded/special pairs. GenericPolygonRotation is the genuine
  quotient lift of the actual normalized turn sum, proved well-defined by
  cyclic invariance. GenericFibre is its actual level set, with exact quotient,
  representative and cyclic-shift membership equivalences. No existence or
  density is assumed. Review: reviews/def-admissible.json, 21 supporting files,
  semantic hash f573f5525867696d3d0398761286535bb1fc806a4fb4b9534ab106599c759cba.
  It adds one original DEFINE row and no original PROVE row.
- The literal original lem:shift(iii) is independently disproved on its printed
  domain. There is no standing Generic/nonzero-turn premise in its surrounding
  source. The regular four-tuple ((0,0),(1,0),(2,0),(0,1)) has left count 3 and
  reversed left count 0, whereas 4-3=1. repairs/ShiftZeroTurn.lean proves actual
  regularity, exact turn inventory, both counts and the contradiction, with
  only standard axioms. It is separately compiled outside the theorem library
  and independently reproduced. Earlier failed logs were superseded by the
  successful final check; reviews/lem-shift-scope.md binds the current file and
  successful log. Original lem:shift remains pending and unmapped.
- SM.shift_reversal_corrected is a separately reviewed repair, not an accepted
  original row. GenericReversal proves exact reversed affine points t->1-t,
  closed/interior segments and full G1/G2 preservation. ReversalCrossings proves
  the actual unordered crossing-support bijection i->1-i and exact set image.
  ReversalChambers constructs actual generic and quotient homeomorphisms and
  proves their full connected-component images. TurnCountReversal gives the
  unconditional original-right-turn count, then the n-left formula with the
  explicit nonzero-turn premise, plus a proved Generic corollary. ShiftReversal
  assembles these with the existing cyclic and regular rotation laws, retaining
  each other clause's full domain. Review: reviews/lem-shift-repair.md, 43 local
  supporting files. Both direct consumers have Generic domains. The original
  source omission is recorded as a local obstruction in TASKS.json and in
  repairs/index.json; independent main-target work remains available.

## Latest accepted claim and next executable work

Full lem:fibres is independently accepted as SM.nonempty_fibres.
Review: reviews/lem-fibres.json, 46 supporting files, semantic dependency hash
48ab82a43285f5174e250cd1cdf8e35fe936821eae3762c4624a54137ad1833b.
Candidate checkpoint027 and final accepted-metadata checkpoint028 both passed. PolynomialAvoidance,
AreaDensity, LineConcurrence, ConcurrenceDensity and GenericDensity prove full
G1/G2 density from actual affine-line polynomials and explicit nonzero witnesses.
RegularPerturbation proves actual regular openness, rotation local constancy
and generic perturbation with the same rotation. FibreReduction iterates actual
subdivision and derives necessary admissibility from the actual rotation bounds.
ZeroRotationSeed gives the actual bowtie by principal-angle cancellation.
CyclicComplexSeed computes all actual cyclic edges, including closure, and their
principal turns. PositiveRotationSeed uses exp(i*2*pi*k/(2*k+1)) with the proved
strict angle bounds to construct a regular seed of rotation k for every k>0.
FibreExistence handles every positive, zero and negative integer rotation;
negative seeds use actual reversal before generic perturbation. Fibres proves
actual quotient-fibre nonemptiness and the full existence iff on ALL integer n,r.
Its integer-domain existence explicitly requires a natural vertex count m>=3
with m=n and an actual GenericPolygon fibre. Raw tuples at n<3 are not source
polygons. Both full existence and density are in the mapped aggregate.

Full def:germ is independently accepted as SM.wall_germ_definition.
Review: reviews/def-germ.json, 22 supporting files, semantic dependency hash
955b5ddf1638ba17aef798e9545375ede704c0a24972b8556c529542c6d95e09.
WallGerm retains the actual open interval subtype, Continuous curve, all
punctured Generic values and nongeneric centre. GermSides proves connected
actual side images, their genuine labelled/quotient chambers, uniqueness,
basepoint independence, projection and chamber-constant values. GermSignChange
uses exactly the opposite-sign product on both actual sides; it proves the
radius-bound/local-witness equivalence, real-parameter formulation and shrinking.
ZeroTriples defines actual unordered 3-element supports, proves chi-zero order
independence, and uses actual pairwise-remote common interior points for
concurrence. GermRelabel and ZeroTripleRelabel prove full fixed cyclic transport
of the curve, chambers, centre, zero sets and real observables. No global
extension, differentiability, Regular, named-wall or derivative transversality
premise is introduced. Candidate029 and final accepted-metadata checkpoint030
both passed. This adds one original DEFINE row and no original PROVE row.

Full lem:triple-sides is independently accepted as SM.triple_sides.
Review: reviews/lem-triple-sides.json, 33 supporting files, semantic dependency
hash 411fa8796f549d890ea8784b9f5e8c748db1cacdb3288f6fc20ace8fa7ebe4ec.
G1CrossingStability proves complete crossing-support constancy from G1 alone;
TripleCenter derives the common selected parameter and excludes every outside
crossing at that parameter. TripleParameters uses finite strict comparisons and
actual Cramer continuity to keep every other crossing outside both selected
parameters. PairVisits exhausts all actual visits on a selected edge and proves
that traversal-key betweenness forces that same edge. SortedAdjacency proves
consecutive actual finite-sort indices; TripleAdjacency applies it to the full
independently constructed gaussList. TripleSides assembles all three persistent
crossings, all pairwise inequalities between actual points, and adjacency on
all three selected edges. GermNeighborhood gives one genuine positive radius
covering both punctured sides of the original interval. No sign-change,
derivative, transversal-parameter or central Generic premise was added.
Candidate031 and final032 passed. This accepts one original PROVE row; the
seven supporting modules do not add counts.

Checkpoint033 proves partial flat geometry and local records in SM.FlatLocal.
Twenty new modules establish distinct central vertices, nonzero edges, Regular,
the unique zero turn, positive affine fusion, exclusion of nonincident vertices,
adjacent-interior separation and transverse remote crossings without G1 at the
flat centre. CrossingGeometry is derived from these source hypotheses, not
assumed as an extra premise. Actual geometric visits, sorted lists, cyclic words,
interlacement graphs and directed crossing signs agree exactly with the accepted
Generic constructions. Complete crossing support and actual parameter order
persist on one neighbourhood, including the centre. The raw-curve bridge derives
its required nongeneric centre from the singleton point-zero set.

Checkpoint034 adds14 modules for actual deletion and fusion. DeletionIndices
and DeletedTuple prove the retained cyclic index set, closing edge, continuity
and reconstruction of the actual shifted parent by appendVertex. DeletionG1
uses the retained triples' exclusion of the deleted label. AffineSubdivision,
DeletionInteriors and DeletionGeneric explicitly exclude the middle vertex
from unchanged child edges, lift each remaining interior to a parent interior,
prove distinct child labels have disjoint sets of parent lifts, and contradict
actual parent G2. The child, including a triangle, is therefore Generic.
GenericCurveChamber and DeletionChamber prove actual nearby Generic deletions
lie in the central labelled and quotient chambers on one full smaller interval.

FusionIndices defines the exact total parent-to-child edge map and proves
remote parent pairs cannot collapse. FusionGeometry proves positive edge
factors, exact point/parameter formulas and parent-interior containment.
FusionCrossings proves the actual crossing bijection, its exact support image
and preservation of its actual geometric point; surjectivity explicitly lifts
child crossings, while injectivity uses parent G2 and unique points.
FusionVisits proves the actual two-visit fibre equivalence, complete visit
bijection, pairing and exact actual parameter formula. FusionSigns proves all
directed determinant signs and positive over/under data preserved.
FusionParameterOrder proves order within every original edge and that every
first-piece visit precedes every second-piece visit on the fused edge.

Checkpoint035 adds FusionKey: a strictly increasing piecewise affine real map
compresses the final two parent-edge traversal intervals into the child's fused
edge interval. The exact actual-key formula handles the deleted label, its
predecessor and all other retained labels, using actual natural representatives
and explicit casts. Strict monotonicity transfers every key comparison, and
the proved traversalBetween_shift removes the actual cut. Thus GLOBAL cyclic
visit order is now proved without assuming Generic at the flat centre.

Checkpoint036/037 completes full flat-side geometry in seven new modules.
SortedCompressedCut compares independently sorted complete visit universes under
an actual cut followed by a strictly increasing compression, including empty
lists. FusionGaussWord derives rotation of the actual full lists and equality of
the genuine Cycle words. FusionInterlacement transports both actual two-visit
fibres and both alternating arc conditions. CrossingVertexExclusion handles
incident endpoints by actual parameter injectivity and every nonincident vertex
by the proved closed-segment exclusion. FlatSpatial covers zero and the entire
punctured Generic germ domain.

FlatFusionData packages the actual child Generic proof, constructed crossing
and visit bijections, exact edge-label image and crossing-point equality, the
actual affine parameter formula, global cyclic order, pairing, independently
formed Gauss word, interlacement and all directed determinant/over-under signs.
FlatSides assembles every source clause on ONE positive radius: noncritical
chirotope signs, actual crossing geometry and distinct points, exclusion of all
vertices, explicit every-edge parameter comparisons, complete records, and
actual Generic deletions in their central labelled and quotient chambers.
The source's actual turn SignChanges is retained and used on that same radius.
flat_sides_curve covers every raw continuous source curve, deriving central
nongenericity from the actual singleton zero set. The n+1/child-size presentation
covers every parent N>=4 by flat_parent_size. Independent full source/type/body
review accepts this one original PROVE row; helpers do not add original counts.

The next full source result remains lem:wall-sides. The remaining UNPROVED work
is in decisions/named-wall-localization-next.md. Reuse the twenty audited
modules: do not repeat the E/C proof or V crossing classification. Next establish
one finite contact neighbourhood for all persistent and changing V visits, then
the exact T visit swaps and full F/V/T/E/C assembly. Full def:walls remains
pending until all cusp/side conventions, cyclic transport and mutual exclusivity
are proved as well; do not count partial predicates.

## Resumption and progress

Run python3 work/claim_progress.py for the evidence-backed ORIGINAL proof and
checklist counts. python3 tools/progress.py --once reports the EXPANDED checklist,
including the extra weak-openness row. These denominators intentionally differ;
never present expanded checklist percentage as percentage of original proofs.
Latest reports: progress/claims-latest.json and progress/latest.json. Both progress
reporters ran after checkpoint038 (20:51:12 UTC). All accepted source/review
dependencies and separate scope/repair review hashes are current; no accepted-row
evidence issue is reported. Helpers do not inflate the original count.

Use python3 tools/check_lean.py work/lean after changes. Full-stage acceptance
requires every retained obligation and independent source/type review; successful
builds and status percentages do not replace that requirement. The goal remains
active. The original shift row has a verified local source obstruction;
independent work toward the main targets can continue.

Hourly automation: hourly-lean-formalization-progress (ACTIVE). The user requested
hourly reports, overriding the handoff ten-minute default. File reporter session
42482 was confirmed live during this checkpoint; its last hourly relay was
20:00:09 UTC (relayed with original proof/checklist counts). The next hourly report is due at 21:00 UTC. Keep one watcher; check its handle before starting another.
Continue periodic reporting throughout active execution.

No pending development copy remains for the completed flat proof. The earlier
flat-cyclic-next.md plan is fully implemented and its status is updated. Start
the remaining source work from decisions/named-wall-localization-next.md without redoing
any completed flat scalar, index, deletion, cyclic, word or spatial calculation.

## Environment

Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0.
Use /Users/aguevaragonzalez/.elan/bin/lake from work/lean.
work/lean/.lake/packages links to the exact cache at
/tmp/lean-handoff-mathlib-smoke/lean/.lake/packages. If it disappears, remove only
the broken symlink and restore the same pinned dependencies/cache. The eventual
delivery must not depend on that temporary cache path.

## Source interpretation and literature

lem:g1(iv) uses “two adjacent edges” as distinct edges, as its printed proof
requires. The index relation includes self-adjacency; a literal self-pair singleton
intersection assertion would be false. This interpretation is explicitly recorded
in AUTHOR_NOTES.md and the independent review, not silently added.

The supplied sibling LEAN_HANDOFF_20260909_SOURCES_ADDENDUM contains literature
and historical audits. Its verifier passed (8 checks, 11 PDF hashes, 103 manifest
entries). See reports/sources-addendum-review.md. The full Lickorish–Millett 1987,
Lickorish 1997 and Geiges 2008 originals would help later figure/page verification;
extracts are already supplied. Reidemeister proof-depth review remains open, with
Queffelec 2024 already included as a candidate. No source request blocks current
geometry. The addendum cannot authorize a new axiom or weaken geometric scope.
