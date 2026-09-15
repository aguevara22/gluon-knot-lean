# Nonblocking decisions

- The current user requests initial formalization of the focused handoff and hourly claim percentages. Continue autonomously; retain the 132 proof / 191 checklist baseline denominators. Count only full, checked and independently reviewed source claims as accepted.
- Use ZMod n indices, real coordinate pairs, SignType for the exact {-1,0,1} sign values, and the actual cyclic-orbit quotient. Supporting tuple definitions are allowed at smaller sizes; source results specialize to n >= 3. No genericity or nonzero-edge restriction is silently added.
- Reuse the existing exact pinned dependency cache; implementation and restart metadata are in work/. The final package must not rely on the temporary symlink.
- Literature acquisition remains incomplete, but the initial coordinate/finite-combinatorial proofs require none of the five literature axioms. They are not introduced speculatively.

- Source interpretation for lem:g1(iv): def:polygon marks an edge adjacent to itself, but the phrase “two adjacent edges” and its printed proof refer to two distinct incident edges. SM.g1 quantifies distinct i,j and covers both orientations explicitly. A literal self-pair statement would be false (an edge intersects itself in the full segment). Independent reviewer agrees that distinctness is contextual disambiguation; this is documented, not silently added. Likewise “flat/kink” concerns consecutive edge vectors, as the source determinant argument shows.

## Sources addendum received — 2026-09-10

Verified the supplied sibling SOURCES_ADDENDUM (8 checks, no failures). See
reports/sources-addendum-review.md for local copies, remaining original-page
needs, and source-priority corrections to two index suggestions. Continue
without asking the author: no new axiom or weakened geometric scope is permitted.
The current geometry proofs do not depend on the missing publisher PDFs.

## Chamber formalization — 2026-09-10

Completed the full chamber proposition and definition. G2 openness is proved
through actual remote closed triples and compact projection; the cyclic quotient
uses its genuine quotient topology. Chamber preimages are unions of at most n
actual labelled components, permuted by sigma. Path invariance covers every
time, including endpoints, and both orientations of parameter comparison.
Independent reviews: def-chamber.json and prop-chambers.json. No new axioms.

The weakly generic predicates now use nonincident closed-segment exclusion and
conditional transversality at actual remote intersections. Disjoint parallel or
collinear remote segments remain allowed. Its openness proof must not assume G1
or replace polygonal connectedness by ordinary path connectedness.

## Weak openness and progress accounting — 2026-09-10

SM.weak_open now proves weak-locus openness, open polygonally connected labelled
components and the positive-radius Euclidean-ball clause. Its independent
review is reviews/lem-weak-open.json. The proof preserves disjoint parallel and
collinear remote pairs and uses no G1 assumption. Euclidean balls use the actual
2n-coordinate L2 space, with a proved coordinate homeomorphism.

The frozen focused DAG did not select lem:weak-open. Track it as an additional
supporting source row rather than incrementing the original 132-proof or
191-checklist baseline. tools/progress.py includes added rows in its expanded
denominator; work/claim_progress.py keeps the original baseline and lists extra
IDs separately. This difference is deliberate and must be explained in reports.

## Full Gauss definition — 2026-09-10

The actual traversal set is ZMod n times the half-open real interval [0,1),
with plane evaluation by the original affine edge map. Sorting uses i.val+t
after a cut at label zero; the circular order and genuine rotation quotient
remove that cut. Actual visits are the dependent sum over actual crossings of
their two incident edges. Finiteness, exact two-visit counts, distinct positions,
strict sorted enumeration, word length and two occurrences of each crossing
are all proved, including the empty word. No arbitrary word is an input.

Relabelling has actual traversal, crossing and visit bijections. The traversal
cyclic-order proof covers all half-open edge points. The Gauss word at a shifted
tuple is independently constructed; SortedCut proves equality in the rotation
quotient by moving the portion before the new cut to the end. Reversal is not
identified with a rotation. Full independent review: reviews/def-gauss.json.

This constructs the source data; it does not prove arbitrary link equivalence,
the named-record polynomial theorem or CV ax:gausscode. Those obligations and
the main corner wall laws/soft theorem remain pending. Next implement actual
interlacement and visible-signature constancy, with their source equivalences.

## Full interlacement definition — 2026-09-10

SM.interlacement_definition is independently reviewed in def-interlace.json.
The four visits are the actual two-edge crossing fibres at their proved
geometric traversal positions. Complementarity of the two open arcs uses
generic injectivity and excludes the endpoints explicitly. The exactly-one
count is equivalent for every ordering of x's two visits; symmetry follows by
rotating the four actual positions. No arbitrary graph or adjacency input is used.

The finite graph has the actual crossing type as its vertices. Ind is the
complete powerset filter by independence, including empty. N(S) is defined on
every subset and may intersect S for non-independent S; U(S) is exactly the
complement of S union N(S). Cyclic relabelling transports the actual visit
fibres, graph, independent supports and N/U through proved bijections.

This accepts one original DEFINE row, leaving the original proof count at
5/132. The visible signature and its chamber-constancy assertion remain pending;
see decisions/visible-signature-next.md. No literature axiom has been introduced.

## Full visible signature and source quotient convention — 2026-09-10

SM.visible_signature_definition is independently accepted in def-visible.json.
The stored triple is the actual turn tuple, actual crossing set and actual
Gauss word with its letters embedded by the injective support map. CycleMaps
proves injectivity on whole cyclic words, so this removes only dependent proof
data and preserves crossing identities, repeated letters and rotation classes.
The exact word inventory and length are also proved, including the empty case.

Constancy compares independently sorted geometric words using canonical
crossing/visit transport. Different-edge order uses unchanged edge labels;
same-edge order uses the proved geometric parameter theorem, including equal
partners. The full signature is exactly constant on genuine labelled connected
components. Its shift action reads turns at i+a and moves crossing indices by
-a. For every two representatives over a quotient chamber, the signatures agree
by an actual cyclic shift, using the proved component-preimage decomposition.

The source def:polygon and its formalization remark explicitly permit labelled
constructions with shift-equivariance. Independent review confirms that this
full reading needs no separate quotient of signature data. This does not say
that signatures classify chambers and does not prove the weak-locus extension
in lem:silentlocus. Retain that separate dependency for the silent-wall chain.

Next implement regular principal turns and all clauses of the rotation lemma.
Use the actual Euclidean length (for example through the complex coordinate
norm); the default norm on Plane=R×R is not the source Euclidean norm. Positive
collinear consecutive edges must remain in the regular domain. See the explicit
unproved plan in decisions/regular-rotation-next.md. The main wall/soft targets
and unconditional R discharge remain pending; no literature axiom has been used.

## Full regular definition and partial rotation lemma — 2026-09-10

SM.regular_definition is independently accepted in reviews/def-regular.json.
EuclideanPlane proves the genuine Euclidean length formula and the actual
oriented rotor identities. RegularPairs and PrincipalAngles prove the exact
strict-interval cosine/sign characterization, uniqueness and existence on
precisely the nonzero/non-antiparallel domain. Positive collinear edges remain
allowed and give zero turns. Existence itself implies the domain: regularity
is not built into PrincipalAngleSpec as a premise. RegularLocus proves the
source edge-predicate equivalence, generic inclusion and cyclic equivariance.

The rotation number is the actual real sum of principal turns divided by
2*pi. Its integrality follows by telescoping actual edge-argument classes in
Real.Angle and applying that quotient's proved integer-period characterization.
The real finite sum is explicitly typed before coercion, avoiding the distinct
expression that would instead sum already-coerced terms. No integer winding
number or exponential-product identity is provided as an input.

RotationContinuity proves actual angle continuity on regular families and
constancy through the discrete range of the real integer embedding. It includes
genuine continuous Path endpoints. RotationReversal uses the actual source
i -> 2-i reversal and proves regularity plus negation of every principal turn
and the sum. RotationBounds sums the strict principal-angle bounds.

RegularTriangle derives nonzero common determinant from regular closing edges,
without strengthening the domain to Generic. RotationTriangle combines the
common sign, integer rotation and strict bound to prove equality to every turn
sign, signed unit rotation and nonzero rotation.

These are partial clauses of the single original lem:rot. Actual vertex
insertion and the complete source aggregate remain outstanding, so no original
proof row is accepted for these helpers. See decisions/rotation-insertion-next.md.
The main wall/soft targets and unconditional R discharge remain pending.

Independent partial review in reviews/lem-rot-partial-checkpoint020.md found
no fidelity defect in the implemented rotation clauses. It explicitly leaves
insertion and the full source aggregate missing. Its file and receipt hashes
were verified; it accepts no original proof row and changes no denominator.

## Full rotation lemma and actual vertex insertion — 2026-09-10

SM.rotation_number is independently accepted in reviews/lem-rot.json, closing
all five clauses of the original lem:rot. This supersedes the missing-insertion
status recorded at checkpoint 020; the historical partial review remains a
record of that earlier state. The full review binds all 24 local supporting
files and semantic hash 847dc8b72fa93fe2f7edc30e0d550f96ab2bfa0b2eb96bf047c15fc8d6b4c889.

The actual n+1 tuple retains each old natural index and adds one new index n.
InsertionIndices proves the old index map injective, disjoint from the new
index, and exhaustive together with it. Its successor/predecessor identities
handle both cut ends. InsertedTuple keeps every old coordinate and places the
new vertex at the actual edgePoint on the old wrap edge. The split edge vectors
are t and 1-t times the old edge; every other edge is unchanged.

AngleScaling proves principal angles and RegularPair preserved under positive
independent scaling of incoming and outgoing vectors. AppendRotation derives
all old principal turns unchanged and the new turn zero from actual new edges.
InsertionSum derives the complete finite-sum identity from the proved index
partition. VertexInsertion shifts an arbitrary chosen edge i to the cut by
i+1, retaining all old vertices in cyclic order and inserting the actual strict
interior point on that original edge. The previously proved cyclic invariance
returns equality of rotation with the original tuple. No Generic, global
vertex-injectivity, noncrossing or supplied angle-inventory premise is used.

The complete source aggregate includes constancy at every pair of parameters
of genuine continuous regular paths, actual insertion at every edge and every
strict interior parameter, actual reversal, the n=3 conditional for the same
polygon P, the strict bound and cyclic invariance. Only this full original
lemma increases the proof count. The next original row is lem:uniformrot; see
decisions/uniform-rotation-next.md. All main wall/soft targets and unconditional
R discharge remain pending. No literature axiom has been used.


## Full uniform-turn rotation and next source omission — 2026-09-10

Full lem:uniformrot is accepted as SM.uniform_rotation after independent review
of all four implications and all 17 supporting files. Its actual short-sector
proof uses cumulative principal-turn sums, equality of direction classes modulo
2*pi, the explicit unit vector at the sector midpoint, positive Euclidean edge
lengths and actual edge closure. It does not assume a sector, a positive linear
functional or an unwrapped real argument. Source Regular and all-turns-nonzero
premises are retained. Actual cyclic and reversal index maps handle arbitrary
exceptional turns and both negative clauses. Candidate023 and final024 audit
791 declarations with only standard axioms; no literature input is used.

Independent reviewer review_chirotope-independent-20260910 also confirmed a
literal omitted premise in the next source lem:shift(iii). Its printed formula
leftTurns(reverse P)=n-leftTurns P is false if zero turns are allowed, and the
surrounding scope does allow them. Generic intended scope is plausible but is
not supplied by the printed environment. The candidate regular four-tuple
((0,0),(1,0),(2,0),(0,1)) has three left turns and one zero; reversal has zero
left turns. A separate exact Lean check is being completed under work/repairs/.
The source row remains unaccepted. Prove the corrected count under explicit
nonzero turns, separately record the repair and use it only after proving the
consumer hypotheses. Both direct observed consumers have Generic domains.
No frozen file is edited, no source claim is silently replaced and no author
answer is required. See decisions/shift-scope.md for the next concrete work.


## Admissible fibres and explicit reviewed shift repair — 2026-09-10

SM.admissible_definition has passed independent full review in
reviews/def-admissible.json. Integer Admissible/MinimalAdmissible predicates
retain all source parameter cases, while the fibre is the actual rotation
level set on GenericPolygon, with a proved quotient lift and representative
membership equivalence. It asserts neither nonemptiness nor density.

The exact regular counterexample to the unrestricted original lem:shift(iii)
now compiles and was independently reproduced. reviews/lem-shift-scope.md
binds the actual tuple, definitions, successful log and frozen scope/consumer
files. Only standard axioms occur. The source original remains unmapped and
unaccepted; repairs/index.json makes the separation explicit.

SM.shift_reversal_corrected also has an independent repair review,
reviews/lem-shift-repair.md, over 43 actual supporting files. It retains
unrestricted chirotope, affine edge and individual-turn identities, actual
full Generic/crossing preservation, genuine labelled/quotient homeomorphisms
and connected-component image equalities, and actual regular rotation laws.
The correct unconditional count equals original rightTurns. Only the n-left
conclusion has the explicit minimal all-turns-nonzero condition. Its Generic
corollary proves that condition from actual G1. Both observed consumers already
have Generic domains. This repairs their dependency without assuming the false
unrestricted conclusion or counting the repair as the original source row.
No frozen source, DAG baseline or acceptance checker is changed.

The next full row is lem:fibres, including both existence and full Generic
density. See decisions/fibres-next.md. The all-triple determinant and remote
line-concurrence constraints must be handled at their full source scope; a
weaker CV genericity or an isolated regular seed would be incomplete.


## Fibre-existence construction completed; candidate checkpoint027

Full source lem:fibres now compiles as SM.nonempty_fibres. The construction
proves both exact existence for all integer parameter pairs and full G1/G2
density on the actual tuple space. It awaits independent final acceptance;
intermediate density, perturbation and seed results do not add original counts.

Implementation decisions: use ordinary one-variable polynomials along actual
affine tuple lines, finite root avoidance and finite intersections of open dense
sets. This replaces the printed multivariable product proof by a proved route
to the same full Generic density. Explicit area witnesses and six-index remote
edge witnesses prove nonvanishing; actual line coefficients and their genuine
3x3 determinant exclude finite triple interior meetings. G1 excludes adjacent
interior meetings. Determinant nonconcurrence is only a sufficient intermediate
condition, never a replacement definition of Generic or of actual concurrence.

The actual regular locus is open including positive-collinear zero turns.
Continuity of the genuine normalized turn sum plus the proved integer-rotation
theorem gives a neighbourhood with constant rotation, replacing the printed
small-ball path argument by a proved stronger local-constancy result. Actual
subdivision is repeated and preserves all old angles plus inserted zero angles.
The bowtie's actual principal angles cancel in pairs; exact arctangent values
are unnecessary for its zero-rotation conclusion. Positive seeds use the
printed complex exponential, compute every cyclic edge including closure,
and prove every turn equals the strict angle 2*pi*k/(2*k+1). Negative rotations
use actual regular reversal. No seed's Generic property is assumed: full
Generic tuples are produced only by the proved density/perturbation theorem.

The all-integer existence predicate uses an actual quotient GenericPolygon
fibre and an explicit natural vertex-count witness m>=3 with m=n. This retains
the source polygon domain even though helper tuple/Generic types exist for
small n. Exact necessity and sufficiency, negative n, zero rotation, and the
excluded pair (3,0) are all handled. Candidate audit027 passed with 996 local
declarations, 21 mapped claims and only standard axioms; source bundle integrity
also passed. No literature interface is used or added. No source file changed.


## Full lem:fibres independently accepted

Review reviews/lem-fibres.json certifies both original clauses, with all 46
supporting Lean files and semantic dependency hash
48ab82a43285f5174e250cd1cdf8e35fe936821eae3762c4624a54137ad1833b.
Reviewer identity: review_chirotope-independent-20260910; implementation author:
root-implementation-20260910. Review file SHA256:
01a5033e9dba533e96b790d6556ab5abcc9f6c9e0f824f0e6c493fed83dee20f.
All supporting/source bindings were independently checked and rechecked locally.
This accepts one original PROVE row: 8/132 (6.06%), with 20/191 original
checklist rows (10.47%) and 21/192 expanded rows (10.94%). All eight main targets
remain pending. No helper or repaired original shift statement adds a count.
Final metadata audit028 runs after acceptance; then continue with full def:germ.

Final accepted-metadata checkpoint028 passed (996 declarations, 21 mapped claims); the complete project inventory and all project/frozen-bundle hashes and independent-review bindings were verified. Original session90909 terminated with exit 0. No proof/build job remains running. Full-stage acceptance remains false as expected; receipt.current is a full-stage predicate, not an incremental audit predicate. Next: full def:germ.


## Full wall-germ definition candidate — checkpoint029

The previous goal turn made verified progress: full lem:fibres was accepted.
The next source unit, def:germ, is now fully implemented in seven new modules.
The curve is defined on its genuine open interval subtype, with no silently
required global extension. Both sides use actual positive-distance parameters
with reflection for the negative side, and cover the full half intervals.
Their actual connected images determine unique connected-component chambers;
any chamber-constant function has the same side value at every side point.
The quotient projection is the previously proved actual cyclic orbit map.

Point-zero triples are genuine finite unordered three-element index supports.
The universal chi-zero condition is proved equivalent to chi=0 for every
ordered representative using alternation and repeated-index identities.
Concurrence triples require pairwise remote edges and an actual common point
of all relative interiors; no homogeneous-line determinant substitutes for
that geometric definition. All constructions apply at nongeneric centres.
Sign change is exactly the opposite-sign product on P(t),P(-t). A bounded
positive witness radius is proved equivalent to the local condition by
shrinking, with an explicit real-parameter formulation. Fixed cyclic shifts
transport the curve, preserve its actual quotient chambers, and relabel all
central supports by -a; observables pull back by the actual tuple shift.
No Regular, named-wall, derivative or transversality premise was added.

Candidate029 passed: 1105 audited declarations, 22 mapped claims, standard
axioms only. Source and project hashes match. Full def:germ review is pending;
this is a DEFINE row and will not increment the original PROVE denominator.
Next full proof is lem:triple-sides, retaining the source's absence of a
sign-change hypothesis. Its precise unproved plan is saved in
 decisions/triple-sides-next.md. The 18:00:09 UTC hourly report was relayed;
reporter42482 remains live and next hourly report is due at 19:00 UTC.


## Full def:germ independently accepted

Review reviews/def-germ.json, by review_chirotope-independent-20260910,
certifies every original definition clause and the labelled/cyclic equivalence.
Author: root-implementation-20260910. The review binds 22 supporting files and
semantic dependency hash
955b5ddf1638ba17aef798e9545375ede704c0a24972b8556c529542c6d95e09.
Review SHA256:
24eea4d4ec45c870beb5dc545fc05c9c1650ca67bc53bf7cea8823346bd82df0.
Identity/source/semantic/supporting-file hashes were verified before recording
acceptance. This is one original DEFINE row: original proofs stay 8/132
(6.06%); original checklist is 21/191 (10.99%); expanded checklist is 22/192
(11.46%, reported 11.5%). No helper counts were added. Candidate029 passed;
final metadata audit030 is running. All eight main targets remain pending.

Final accepted-metadata checkpoint030 passed (1105 declarations, 22 mapped claims). All project/frozen-bundle hashes, complete local project inventory and independent-review bindings match. Original session29922 is terminal with exit 0; no proof/build job remains running. Full-stage acceptance is still false. Next execute the saved full lem:triple-sides proof plan.


## Full lem:triple-sides independently accepted — checkpoint032

The complete source lemma is SM.triple_sides. Its hypotheses are exactly n>=3,
an actual continuous wall germ, empty central point-zero set and singleton
central concurrence set. No sign-change or central Generic premise was added.
The finite strict-neighbourhood argument replaces the printed subsequence
argument: G1 gives all crossing-support stability, every other crossing stays
strictly outside both selected parameters, and actual finite sorting converts
no intervening visit to consecutive indices in the full gaussList. The three
geometric points are pairwise distinct on punctured Generic values. A genuine
interval-subtype neighbourhood gives one common positive radius on both sides.

Author: root-implementation-20260910. Independent reviewer:
review_chirotope-independent-20260910. Review reviews/lem-triple-sides.json binds
33 supporting files and semantic hash
411fa8796f549d890ea8784b9f5e8c748db1cacdb3288f6fc20ace8fa7ebe4ec.
Review SHA256 fddcc7bed9c84a4c40c80f1b1991dc03d836282b7f0db97e91409b3b7154aa8e.
Candidate031 and accepted-metadata032 passed: 100 SM modules, 1156 audited local
declarations, 23 mapped claims, standard axioms only. Original session21020 is
terminal with exit 0. Complete inventory, every current project/frozen hash,
all 23 accepted review bindings and separate shift scope/repair evidence were
verified. No proof/build/audit job remains running. Full-stage acceptance is
false; all eight main targets remain pending.

Original proofs: 9/132 (6.82%). Original checklist: 22/191 (11.52%). Expanded
checklist: 23/192 (11.98%, reported 12.0%). Only one original proof is added;
helpers do not change the baseline. The original unrestricted shift statement
remains unaccepted. Next execute decisions/flat-sides-next.md: the flat centre
has a zero turn, so neither G1 nor WeakGeneric may be assumed there. Preserve
actual central records, fusion/deletion bijections and chamber conclusions.
No author answer is needed. Frozen references, blueprints and ZIPs are unchanged.

## Partial flat geometry and records — checkpoint033

SM.flat_germ_local_data proves central vertex injectivity, nonzero edges,
Regular, the unique zero turn, positive affine fusion, and one neighbourhood
with all noncritical chirotope signs and complete geometric records constant.
These records use actual crossings, visit parameters, a full sorted visit list,
the actual cyclic word and alternating-visit interlacement graph. Their Generic
specializations equal the previously accepted definitions. CrossingGeometry is
proved from the central source assumptions and punctured Generic values; it is
not an extra hypothesis inserted into the source theorem. pointZeroCurveGerm
derives the nongeneric centre of every raw source curve from its singleton
point-zero support. Local geometry does not need sign change; full source
assembly must retain the printed scope.

Actual deletion/fusion correspondence, Generic of deletion, cyclic visit
transport to deletion and the nearby deletion chamber remain UNPROVED.
The full lem:flat-sides row stays pending with blank module/declaration.
No original claim was added: proofs 9/132 (6.82%), original checklist 22/191
(11.52%), expanded checklist 23/192 (11.98%). All eight main targets pending.
The next executable unproved strategy is decisions/flat-deletion-next.md.

Audit033 completed with exit 0: 120 SM modules, 1302 audited local declarations,
23 mapped claims, standard Lean axioms only, no literature interfaces used.
Receipt SHA256 e63c292ddc011cbab3f6863976ea0a002d213211bd4ac1f07cf5bf0ca69a265b.
Exact project inventory, all project/frozen hashes, all 23 accepted semantic
review bindings and the separate shift counterexample/repair bindings match.
The unmapped partial root type and axiom trace also completed with exit 0 at
checks/flat-local-types.log. Independent partial review is being finalized;
it cannot accept the full original lemma. No Lean/map changes followed audit033.

At 19:09 UTC both progress reporters ran; watcher42482 was confirmed live.
The 19:00:09 UTC hourly report was relayed; the next hourly report is due at
20:00 UTC. The addendum ZIP was reread directly: all 103 manifest hashes match,
and 11 source PDFs are present. The source availability conclusions in
reports/sources-addendum-review.md still apply. No author answer is needed.

Independent partial review completed by review_chirotope-independent-20260910:
reviews/lem-flat-sides-partial-checkpoint033.md, SHA256
03ad30f1ec92df75921b7c7a2d81e281f8bbba0a1841486551c5ba9472fbc3f8.
It binds the64-file supporting closure, audit033 and completed actual type trace.
The full flat source row remains pending/unmapped; counts are unchanged.


## Actual deletion and fusion — checkpoint034

Fourteen new modules prove actual deletion with its induced cyclic cut and
closing edge; reconstruct the shifted parent by appendVertex; prove the child
Generic on the full source size domain (including four-to-three deletion); and
prove every nearby deletion on one smaller full interval lies in the actual
central labelled/quotient chamber. The G2 proof excludes the deleted middle
vertex using an unchanged child edge, lifts other interior points and distinct
child edge labels to parent interiors, and contradicts proved parent G2.

The actual fusionIndex identifies precisely the two incident edges with the
child closing edge. Remote parent pairs cannot collapse. The crossing map is
its exact support image; child G1 proves image remoteness from actual common
interiors. Surjectivity lifts each actual child crossing, excluding the middle
vertex. Injectivity uses preservation of the actual unique crossing point and
parent G2. Thus no bijection or subdivision exclusivity is assumed. The actual
sigma visit equivalence preserves the two-visit pairing and exact affine
parameters. Positive edge scales give determinant-sign and positive over/under
preservation. Within-piece order and every first-piece-before-second-piece
comparison are proved from the strict actual crossing-parameter bounds.

GLOBAL cyclic order and independent Gauss-word transport across the changed
cut, plus the full original source aggregate, remain unproved. The original
lem:flat-sides row remains pending/unmapped; no original counts changed.
Next executable unproved strategy: decisions/flat-cyclic-next.md. A scalar
compression and actual-key lemma are being developed separately in
work/development/FusionKey.lean; this file is NOT part of audit034 or its review.

Audit034 completed with exit0 (session34975):134 SM modules,1396 local
declarations,23 mapped claims. Receipt SHA256:
9b157769fd4d892423f8b1df881bf376149fd6011a8f3ed2df818baaa1c1ca36.
All140 project hashes, all38 frozen hashes, complete project inventory,
all23 accepted source/review bindings, the033 partial64-file closure and
separate shift counterexample/repair bindings were verified current.
The actual deletion/fusion type and axiom trace completed with exit0
(session9247), SHA256 c6e3870976dfd24b98584748d2628613957ccbf9646a1e25dd1b7d391313e8e5.
Only propext, Classical.choice and Quot.sound occur; no literature interfaces.

Independent reviewer review_chirotope-independent-20260910 completed
reviews/lem-flat-sides-partial-checkpoint034.md; SHA256
1088eca7bf7e750e39796459bb8a8e11ac15c53481dfb999d857ea9e46103282.
Its cumulative82-file closure (14 new,68 unchanged) and report hash were
independently rechecked. This is explicitly PARTIAL, not acceptance of the
original flat lemma. Author identity remains root-implementation-20260910.

Original proof progress9/132 (6.82%); original checklist22/191 (11.52%);
expanded checklist23/192 (11.98%, reporter12.0%); all8 main targets pending.
Both reporters ran at19:34 UTC; watcher42482 was confirmed live. The19:00:09
hourly report was already relayed; next hourly report due20:00 UTC.
Frozen sources, blueprints, templates and deliverable ZIPs remain unchanged.


## Global cyclic visit order — checkpoint035

SM.FusionKey is now in the audited project. Its piecewise affine scalar map is
strictly increasing for0<r<1. The actual child visit key equals this map applied
to the actual parent traversal key after shifting the cut to j+1. The proof
handles the old j edge with representative n, the old j-1 edge with representative
n-1, and all other retained edges with smaller representatives. Every cast and
strict parameter bound is explicit. Three-comparison cyclic order transfers
through strict monotonicity, and traversalBetween_shift restores the original
cut. No Generic function is evaluated at the flat centre. The actual crossing
and visit bijections remain those independently proved in checkpoint034.

The complete development file compiled (session53699,exit0), then was moved
from development/FusionKey.lean into lean/SM/FusionKey.lean. Audit035 passed
(session17888,exit0):135 SM modules,1413 local declarations,23 mapped claims;
only standard Lean axioms. Receipt SHA256:
ed048830165e507b03775c619c6352763929fdf3f44b67e5981891ee1ea71eea.
Exact141-file inventory, every project/frozen hash, all23 accepted reviews,
all82 cumulative034 partial-review hashes and separate shift evidence match.
Cyclic root type/axiom trace passed (session67283,exit0), SHA256:
5f731895dc365eca109e8d135ac8a2b8d5baf543b43741043dc86c31759298b6.
The035 independent partial review is being finalized. No Lean/map changes
followed audit035. No build/proof command is running.

Full original lem:flat-sides remains pending/unmapped. Independently formed
Gauss-word transport, required derived fusion interlacement and full source
assembly/review remain. The next plan preserves all explicit spatial clauses,
including no crossing equal to any vertex, and the actual source sign-change
predicate; these must not be hidden behind word equality. Original proofs9/132
(6.82%), original checklist22/191(11.52%), expanded23/192(11.98%), targets0/8.
No new original acceptance and no changed frozen sources.

Independent partial035 review completed by review_chirotope-independent-20260910;
SHA2568792bd089e3e50ed3b857ed37927a413c1d8147f4660dcb79f634c68ac6f415e.
All83 cumulative supporting-file hashes verified. Full flat row still pending.

## Full flat-side source assembly — 2026-09-10

Original locator: reference/SM/sm-1-polygons.tex:751–893, lem:flat-sides and
flatpr:fusion. The actual geometric theorem is now SM.flat_sides, with a raw
continuous-curve bridge SM.flat_sides_curve. Parent size is n+1 with n>=3;
flat_parent_size proves this covers every original N>=4. The source's actual
turn-sign change is retained and used. One minimum radius simultaneously
controls all noncritical chirotopes, actual spatial/vertex properties, every
edge's actual parameter comparisons, independently formed records, and the
actual deletions' labelled/quotient connected components. At the central
nongeneric polygon the records use derived CrossingGeometry and are proved
to agree with Generic records whenever the tuple is Generic.

Fusion uses the actual deleted vertex and induced cyclic order. The full
crossing/visit maps are constructed bijections, preserving geometric points,
affine intersection parameters, global cyclic order, actual Cycle words,
pairing, actual interlacement and directed determinant signs. Empty crossing
universes and every cut are included. No crossing point can equal any vertex;
incident endpoints and nonincident vertices are separately excluded.

Independent reviewer review_chirotope-independent-20260910 certified the full
source claim in reviews/lem-flat-sides.json, binding 91 supporting files and
semantic dependency hash
390e52915488af936ec194118130b4e6e0e9123922c47211147040be011980f2.
Candidate audit036 passed (1452 local declarations; 24 mapped claims). Only
propext, Classical.choice and Quot.sound are used; no literature interface.
Accepted metadata is recorded and final audit037 passed (original session87244,
exit0; all project/frozen/review bindings verified). No original
source, axiom policy, template, provenance or ZIP was changed. This is one
original proof claim; no helpers are added to the original denominator.
The named-wall laws and soft theorem themselves remain incomplete. No author
question is required. Next source plan: decisions/named-wall-sides-next.md.

## Named-wall geometry — checkpoint038

Twenty new modules compile and pass audit038: 162 SM modules, 1632 local
declarations, 24 mapped claims, 168 project files and 38 frozen files. Receipt
SHA256 23d75299bbcf8305e314e141e45f43f6f1bade0cf4365f5be74fbe31e30941ef.
Original audit session80844 and actual type/axiom trace session89174 are terminal
exit0. All accepted reviews and their full supporting-file bindings remain
current. Only propext, Classical.choice and Quot.sound are used; no literature
interface or new axiom. No Lean or declaration-map file changed after this audit.

SilentSides establishes actual E/C central and nearby geometry and records on
one radius. V helpers prove the exact two-pair support difference and both
bigon/sliding alternatives on the whole connected Generic sides; both necessary
finite-segment sign tests are proved. All unaffected supports persist, their
actual parameter orders persist, no persistent central crossing is any vertex,
and both changing pairs' parameters approach their actual contact values.

At the V centre, raw IsCrossing includes two endpoint-contact pairs. Only the
explicitly unaffected pairs are certified transverse interior crossings there.
Global central CrossingGeometry or Generic records would strengthen the source
incorrectly. Current helpers respect that boundary. One simultaneous finite
contact neighbourhood and actual visit localization still need proof; the
parameter limits alone do not establish those clauses. Exact T exchanges and
the complete F/V/T/E/C source assembly also remain. The next executable plan is
decisions/named-wall-localization-next.md. Full def:walls additionally needs
cusp, side-convention, mutual-exclusivity and cyclic-transport obligations.

Both original rows remain pending and unmapped. Original proofs remain 10/132
(7.58%); original checklist 23/191 (12.04%); expanded checklist 24/192 (12.5%).
All eight main targets remain pending. Independent partial review completed in
reviews/lem-wall-sides-partial-checkpoint038.md, SHA256
f175fedb57264f59d7c4212f8d7c62a588634aaa8923bdaa02ddf725e71085b6.
All 78 supporting files, exact import closure and evidence hashes were verified.
This partial review does not accept a full original source claim.

The sources addendum was reverified: 8 checks, no failures, all 11 PDF hashes
and all 103 manifest entries match. The optional historical sibling-bundle check
was skipped because that directory was absent. This is byte verification, not
proof-depth acceptance. Existing extracts suffice to continue; full originals
of Lickorish–Millett 1987, Lickorish 1997 pp. 168–172, and Geiges 2008 pp. 108–132
would improve independent page/figure checking. Reidemeister proof-depth review
remains open with Queffelec 2024 already supplied. No author answer is needed.

## Full named-wall sides — checkpoints039/040

Full original lem:wall-sides is independently accepted as SM.wall_sides,
source reference/SM/sm-1-polygons.tex:896–1020. Fourteen new modules complete
the earlier partial named-wall work. The theorem supplies every F/V/T/E/C
branch for the same arbitrary actual WallGerm, with one positive interval per
branch. No extra source hypothesis, axiom, derivative or supplied word is used.

V now has one finite positive separation bound for every persistent parameter
on the base and both incident legs, including empty crossing sets. Complete
support persistence and actual parameter continuity exclude every unaffected
nearby visit from the windows. The actual visits in those windows are exactly
the affected ones. A constructed equivalence of all persistent visits preserves
supports and edges and every actual same-edge parameter comparison.

The former V-centre interpretation caveat is closed by an explicit iff in the
final aggregate: IsInteriorCrossing centre s exactly means raw closed-segment
IsCrossing centre s with the two ContactAffected supports excluded. Actual
Cramer endpoint parameters show neither affected pair has common interiors;
every other raw crossing is proved transverse/interior. Generic visit bridges
are used only at punctured parameters where the germ provides G1.

T now classifies a central tie precisely by the singleton concurrence support.
All other comparisons persist. The three source sign changes and all six
support permutations give all and only the triangle order reversals. The
actual-visit theorem quantifies every same-edge pair and classifies it using
the union of actual supports. It combines with the accepted complete-Gauss-list
adjacency theorem on one common punctured interval. Both sides may be evaluated
at independent parameters. No Generic centre word, central G2 or injective
central visit-position map is assumed. F/E/C retain their actual full crossing
and word records at zero and nearby, with every parameter comparison.

Independent full review: reviews/lem-wall-sides.json, reviewer
review_chirotope-independent-20260910. SHA256:
2dfb995b053b40092a740b00127e33524ab0b15b15a9bc1e5bd820ede26958ff.
The review binds the exact107-file source/body import closure and151-entry
semantic hash4437240a488e0fa8f4c9ab0a6446fa19489ba9e81ca971a15a2f9656878e31bd.
Only a reversed prose description of coincident parameters was corrected before
acceptance; the reviewed Lean proof was already correct and unchanged.

Candidate039 and final040 passed. Final040 receipt SHA256:
51e14f71d880a144bd01d0c7dbe60bbe6fca41dab8c0b3d3a54ca7fa4b6a5e7a.
176 SM modules,1717 local declarations,25 mapped claims,182 project files and
38 frozen files. Exact inventory and every project/frozen hash match. All25
accepted reviews and all supporting-file bindings are current. The actual full
type/definition/axiom trace SHA256 is
1abf9ac2684c2c23d3132ca08896d7eb04a263604f62f8aa2f824aa5e0b3f97a.
Sessions92608,47421 and11025 are terminal exit0. Only propext, Classical.choice
and Quot.sound are used; no literature or project axiom. Full-stage acceptance
remains false. All original sources, templates, provenance and ZIPs are unchanged.

Original proofs11/132 (8.33%); original checklist24/191 (12.57%); expanded25/192
(13.02%; reporter13.0%). Helpers add no original claims. All8 main state-sum
targets and unconditional R discharge remain incomplete. Full def:walls remains
pending/unmapped because K and the full side/exclusivity/cyclic conventions are
not proved. Next: the full general cusp lemma, decisions/cusp-sides-next.md.
Both earlier named-wall plans are marked complete to prevent repeated work.
Current STATUS.md was shortened for resumption; its old cumulative contents are
preserved in checkpoints/status-through-038.md. The independent shift repair
remains local and its index points to040. No author question is required.

## Checkpoint041: cusp local geometry, still partial

Nine new modules prove both central cases, exact finite-segment crossing signs,
needle turns, unused-pair disjointness and all other crossing-support comparisons
on one common germ radius. Whole audit041 passed; no project/literature axiom
was added, and all176previous SM modules remain unchanged. The original cusp
row stays pending/unmapped: actual unique side naming, the short traversal arc
with threads, the cyclic-adjacency empty implication and the signed rotation
jump still require proof. Counts remain11/132 original proofs and24/191 original
checklist. Follow decisions/cusp-after-local041.md; no author answer is needed.

The sources addendum was reverified:8checks,11PDFs,103manifest entries pass.
Existing extracts suffice to continue; optional original page/figure checks and
Reidemeister proof-depth review remain as recorded in the intake report.

## Complete cusp candidate and independent acceptance, checkpoints042–043

The full original lem:cusp-sides is implemented as
SM.cusp_sides_of_continuous_curve in lean/SM/CuspCurve.lean. Its explicit raw
continuous-curve hypotheses are the source ones. The actual singleton zero
triple proves the nongeneric centre needed by WallGerm; no extra premise is
introduced. The case and loop side are derived, not requested from the author.

The short arc uses actual crossing visits and complete cyclic traversal. The
source adjacency is expressed by either successor equation in the actual
Gauss visit cycle. Its word is that cycle mapped to crossing labels, and the
newborn has exactly the two proved distinct visits. Independent review found
this directly faithful, including wraparound and two-visit cycles; a separate
word-only equivalent predicate is unnecessary. Any other short-arc visit forces
its actual partner into the complementary arc, proving conditional emptiness
and a crossing-free middle edge on either independently evaluated side.

Rotation uses radius/(m+2) to approach the actual centre on each side. The
rotor's actual determinant sign selects +pi or -pi at the unique antiparallel
corner, while the other principal turns have common limits. Proved integrality
and connected-side constancy then give exactly the signed rotation jump for
independent side parameters. No central rotation or differentiability is used.

Audit042 passed for203SMmodules/1946localdeclarations/26mappedrows. Its exact
project209file and frozen38file hashes match; all185priorSMmodules are unchanged.
All proof dependencies use only propext,Classical.choice,Quot.sound. The raw
main theorem has108semantic entries, SHA256
fc86e8effeeb5b38737a86d14fe2a5191f1eabb2986f88aa886538910940df59.
Independent reviewer review_chirotope-independent-20260910 signed the complete
74-file supporting closure in reviews/lem-cusp-sides.json, SHA256
1e4fe3928dab67e4c8b5f27fc76777bbbfc7b620684fefae96d946d20c665cb0.
The acceptance-map change is being reaudited as043; STATUS.md records its
terminal result and final evidence. No original source, template or ZIP changed.

This accepts one geometric source lemma, not a state-sum wall law. Full
def:walls, the main eight targets and unconditional R remain incomplete. Next
construct the two actual contact halves and prove full lem:children, reusing
the already accepted flat deletion/chamber branch. The exact executable plan
is decisions/children-after-cusp.md. No author question is required.

Final audit043 completed terminal0 (session33786); all current bindings pass.
Receipt SHA256: be4572aa34f404d05a299fa793e4270eec1d7ae7ad68d88d9722d1e29219eb6b.
Original proofs12/132 (9.09%), original checklist25/191, expanded26/192 (13.5%).
All8main targets remain incomplete. Next plan and repaired-shift current receipt
are recorded in STATUS/TASKS/repairs. The active goal is not complete or blocked.

## Complete deletion/halves and children, checkpoints044–045

Full original def:deletion-halves and lem:children are implemented as
SM.deletion_halves_definition and SM.children. For the contact distance
d=(a-M).val, the first half has d+1 vertices and the second n-d. The four
source exclusions force both sizes into [3,n-2]; n>=5 is derived. The first
map is M+i.val, while the second sends zero to M and every other i to a+i.val.
The latter is proved to be a rotation of the consecutive range from a+1.
Both retain the printed source cyclic order, including their closing edges.

The first half omits a+1 and the second omits a, excluding the parent's only
collinear triple. Injective inherited labels give G1. Actual cut parameters
are r*t and r+(1-r)*t with0<r<1; both closed and strict interior inclusions
are proved. Injective parent-edge maps then lift every alleged three-edge
child concurrence into full parent G2, derived from the source central data.
Both children are Generic without an assumed child embedding or genericity.

Marked parent relabelling preserves the actual child functions. The halves'
HEq only transports the proved equality of their natural sizes, then reduces
to coordinatewise equality. No reversal or arbitrary child order is introduced.
The deletion branch covers all parent sizes k+1>=4, reuses its actual fused-edge
Generic proof, and proves that the whole sufficiently small deletion curve,
including zero, stays in the central genuine labelled and quotient chambers.
The full children aggregate also retains same-parent Regular at the V centre.

Candidate audit044 passed:213SMmodules,2090localdeclarations,28mappedrows,
219projectfiles and38frozenfiles. All203pre-childrenSMfiles are unchanged.
The full independently signed reviews bind53definition/63children source-body
files and58/66semantic entries. Source and compiled type trace were reviewed.
Only propext,Classical.choice,Quot.sound are used; no literature interface.
reviews/def-deletion-halves.json SHA256:
b97f5c7bee5b68b84a1bd4dca5cff7a6b3c3ce99ad665e899ceb9d574861b4d0.
reviews/lem-children.json SHA256:
8ca72825e3e0bf6f44df9a134c13aea4a1de38b136f60cf14ab06e100c7d0841.
Reviewer review_chirotope-independent-20260910 did not author or edit Lean/map.
Final acceptance-map audit045 is running; STATUS records its terminal result.

Next finish the full named-wall definition, especially exclusivity, central
classification, named side/empty conventions and cyclic transport, reusing
completed geometry. See decisions/named-wall-definition-after-children.md.
The eight main state-sum targets and unconditional R remain unfinished.
No author answer is required, and no original source/template/ZIP changed.

Final audit045 completed terminal0 (session65314); all project/frozen hashes,
28 accepted review bindings and both exact new import closures pass. Receipt
SHA256:48af0260937e22bad3628a38418cfefe3382198853a73a5d28bfb7d6f2310e21.
Original proofs13/132 (9.85%); original checklist27/191; expanded28/192 (14.6%).
All8 main targets remain incomplete. The active goal is not complete or blocked.


## 2026-09-10 — full named-wall definition, checkpoint047

The preceding sources-answer turn revalidated existing source availability but
made no new mathematical progress. This resumed goal turn fixed the pending
central-classification build and completed original def:walls, without reducing
the wall-law/soft-theorem/R objective. No author answer was needed.

SM.named_walls_definition binds all six exact F/K/V/T/E/C predicates to their
actual central geometry and real SignChanges. Pairwise incompatibility proves
unique type and centre determination between actual simple germs. It does not
claim that a centre determines whether an arbitrary germ is tangent. Unique
contact marks identify the V subtype, while the oriented contact sign is the
actual negative-time chi and is constant on that side, not solely central data.

F right/left signs are uniquely determined and independent of side point.
K has the unique actual central betweenness case and the exact newborn pair.
Its actual loop/no-loop side is proved by crossing membership on the entire
side. CuspEmptyAt is equivalent to cyclic adjacency of the actual two newborn
visits at every side parameter. Actual full Gauss-cycle successor transport
retains wraparound and the two-visit case. Cyclic shifts preserve every named
predicate, F/V convention and K case/support/loop/empty predicate. T/C predicates
are proved invariant for any equal unordered support; all reordered real
sign-change observables are handled by exact sign/parameter-difference algebra.

Three independent partial reviews and the final full source/type/body review
were supplied by review_chirotope-independent-20260910, who did not author or
edit Lean or the declaration map. Full review reviews/def-walls.json SHA256:
1c337dbfccd7961c2360b02e97433d4ec2b4909ed50bf6dd9b8489836f00c0e0.
Its exact closure has92files; the main semantic hash covers134entries:
8ff086fefee29d16819d4feb0335c0d3c6b062abdfaa3e4e9d1dfdea869e1086.

The first candidate root build found a duplicate Silent name from the already
accepted SilentCenter module. Reused that exact existing E-or-C definition;
no old module or mathematical statement was changed. Its failed log is retained
as checks/checkpoint-046-initial-failure.log. Fresh candidate046 and final047
both completed terminal0. Final audit047:226SMmodules,2341localdeclarations,
29mappedclaims,232projectfiles,38frozenfiles. All213previousSMmodules and all226
candidateSMmodules remain byte-for-byte unchanged. All29accepted reviews and
support bindings are current. Only propext,Classical.choice,Quot.sound occur.
Final receipt SHA256:
b8aefcd0b4e37f9d5b4a999ef990725c8777b819b6ab2422232a90af1eed73c3.
Type trace SHA256:
e73cf9216859bba9099042fbeb07cdde2c842aac0d9224ae7b36357c97eed363.

Original proofs13/132(9.85%); original checklist28/191(14.66%); expanded
checklist29/192(15.1%). Main targets0/8. No main state-sum law, soft theorem or
unconditional R has been claimed. The original zero-turn shift obstruction is
unchanged and local. Next execute decisions/transport-polynomials-after-walls.md.
A four-variable determinant irreducibility prototype outside the audited
project is being checked; STATUS records its latest terminal state. It is not
an accepted original claim and does not change either denominator.

## Audit048 — actual Δ/H polynomial irreducibility

Implemented and independently reviewed four new work/lean/SM modules for the
actual scalar-coordinate polynomials, with explicit invertible coordinate maps
and geometric evaluation identities. This proves Δ and auxiliary H irreducible
and nonzero over the whole real coordinate ring, with unused variables retained.
No axiom or pointwise nonvanishing assumption was introduced. The source-size
instance for H is separately kernel checked. All226 prior SM files stay unchanged.

Partial review reviews/transport-area-direction-partial.json, exact8-file closure,
SHA256:1d7a694418f01787171bd5b0b491c8082dda1e4732f309edd82140d0b42395df.
Whole audit048 session43424 terminal0:230SMmodules,2407localdeclarations,
29mappedclaims,236projectfiles,38frozenfiles. Receipt SHA256:
35530b5abc6934f5ffd1e7f3077816b243eba168451e4cdbe982fa25724b14eb.
All existing accepted source reviews and the partial review's exact hashes pass.
Original proofs13/132(9.85%), checklist28/191, expanded29/192; main0/8 unchanged.
T and the rest of lem:transport-polynomials remain open; next executable plan:
decisions/transport-after-area-direction.md. Its proposed T proof route is marked
CANDIDATE and is not evidence of a proved result. No author answer is needed.

The addendum was reverified:8checks,11PDF hashes,103manifest entries pass. Existing
extracts suffice to proceed, with optional originals and unresolved Reidemeister
proof-depth review disclosed in reports/sources-addendum-review.md.

Reporting correction: the exit command initially ran the full-handoff reporter
from the parent directory. Its three newly created parent progress files were
identified by exact timestamp and removed; no pre-existing file was removed.
The focused reporter then ran correctly at2026-09-11T00:01:15UTC:13/132 original
proofs,29/192 expanded checklist. Watcher42482 reported at00:00:09UTC and remains
live for the next01:00UTC report. The erroneous0/209 output is not focused progress.

## Audit049 — actual T irreducibility and separate-coordinate affinity

Proved the actual three-line determinant irreducible/nonzero over the full real
scalar-coordinate polynomial ring with exactly n≥3 and three remote pairs.
The general primitive-linear proof is instantiated with concrete line-row
coefficients, a proved C=0,A=-1 FORMAL tail/direction witness, all actual endpoint
freshness conditions, and a proved algebra automorphism to the actual determinant.
No additional hypothesis, axiom, or pointwise nonvanishing claim was introduced.
Also proved Δ and T have degree at most one in each actual scalar coordinate.

Independent T and affinity reviews each bind their exact23-file closure, source,
pins and successful kernel trace. Reviews/transport-concurrence-partial.json SHA:
9f6974f7c31d7c3749b8f320dbc0bac02081e40216bf36297c4518e55cce99c8;
reviews/transport-affinity-partial.json SHA:
6f3818388626549a2e5b64ed88b4682ba6fb991a4ea18fe20838e515cd42d9a0.
Whole audit049 session82997 terminal0:237SMmodules,2497localdeclarations,
29mappedclaims,243projectfiles,38frozenfiles. All230 prior SM files unchanged.
Receipt SHA:9cb9399e7808c0cf2674cca6a3ce46d4a828c7ff0cb06e1ccbfdeccf95196c79.
The current verification script checks both distinct review closures, all prior
source acceptances, actual pins, trace logs and every project/frozen hash.

Original proofs13/132(9.85%), original checklist28/191, expanded29/192, main0/8.
Full lem:transport-polynomials remains pending. Next execute the exact coefficient,
nonassociation, slope/resultant/root work in decisions/transport-after-irreducibility-affinity.md.
Its alternative prime-divisor and cycle-propagation strategies are explicitly
CANDIDATE, not proofs. No author answer is needed; the same full goal stays active.

## Audit050 — exact coefficients, conditional resultant and specialization

Five new modules prove the remaining-variable ring equivalence, exact affine
coefficients, nonzero slope from genuine dependence, nonzero resultant under
explicit irreducibility/nonassociation, and the source's specialized simple-root
and no-common-root statements. Actual polygon evaluation varies exactly one
scalar, preserving every other coordinate. Concrete family nonassociation is
still required; the full original source row remains unaccepted.

Independent review reviews/transport-coefficients-partial.json SHA256:
4c540c53be0374760517b3048b0d13751566866105f5fa536c34469f115e73a9. Exact28-file closure,22-declaration
independent trace, only the three standard axioms. Whole audit050 session46358
terminal0:242SMmodules,2554declarations,29mapped,248projectfiles,38frozenfiles.
All237 prior SM files unchanged; all original accepted review bindings current.
Receipt SHA256:735f7f3808637e37001a3bb2c851661b48b3aef1f6e13b557aa13e75f3f57538.
Original proofs13/132(9.85%), original checklist28/191, expanded29/192, main0/8.

For the remaining nonassociation proof, independent mathematical review confirms
the diagonal-collapse construction in decisions/transport-after-coefficients.md:
one determinant has a collapsed edge, while the other's rows can be
(0,1,0),(-1,0,0),(-1,-1,1), with determinant1. Other endpoint/row orders change
only its sign. Repeated point values are legitimate polynomial evaluations.
This is a reviewed mathematical STRATEGY, not a Lean proof; all extraction,
injection/extension, orientation and evaluation premises remain to be proved.
The full goal remains active; no author answer is needed.

## Audit052 — full original polynomial-controls lemma accepted

SM.transport_polynomials now proves every source clause at1292–1383: exact finite
name family with one ordered representative, all-order sign coverage, actual
determinant evaluation, nonzero irreducibility/nonassociation, all scalar affinity,
exact remaining-variable coefficients, nonzero slopes/resultants and actual
specialized simple/no-common roots. Concrete nonassociation includes equal
six-endpoint supports via the fully proved diagonal-collapse construction and
cycle-edge orientation argument, including n=6. No new assumption or axiom.

Full independent review reviews/lem-transport-polynomials.json SHA256:
8274567d955ea7337ff008a27555a4cbd198f7551d5c07342cd0e52d009a9839.
Exact39-file closure and60-entry semantic hash,28independent type/axiom traces,
all standard-only. Main semantic hash:
5b75978bcaf47e7ac032c146b24a1f55726d665776ac5311b239f6a44fabedef.
The reviewer recovered from a temporary usage-limit failure and completed the
full review; no author answer or automatic acceptance bypass was used.

Candidate051 and final052 terminal0; final052 has251SMmodules,2749declarations,
30mappedclaims,257projectfiles,38frozenfiles. All242previousSMfiles unchanged;
all251candidateSMfiles unchanged in final052. Only acceptance metadata changed.
Final receipt SHA256:b9cd9804c4c3f4176819cc3ec511bb6e4392ea4c67b52483bfa64cf1ff3b8f7d.
All30accepted review/source/support bindings reverified. No literature interface
is used. Original proofs14/132(10.61%), checklist29/191(15.18%), expanded30/192
(15.6%), main0/8. The full main goal remains active and incomplete.

Next full thm:relgp plan: decisions/relative-general-position-after-polynomials.md.
A separate general finite joint-polynomial avoidance prototype compiled in
session78849 terminal0 with only standard axioms; it awaits final independent
prototype review and porting. It proves no waypoint/path/wall claim yet and adds
no original count. Preserve all reviewed modules; continue implementation in new
files. The zero-turn shift obstruction remains local and explicitly recorded.

The joint-avoidance prototype now also passes independent partial review, report
reviews/multivariate-avoidance-prototype.json SHA256
d2853b0311f247589c24e7183ad6b8e38bed73e6e5ed3da8099264ee3be5c985.
Independent trace13618 terminal0, five standard-only axiom sets, actual common
assignment and empty finite condition family checked. Its precise scope is the
general avoidance principle only; no concrete waypoint pullback or path/wall
claim is certified. All052 project/frozen hashes still match. No original count
changes. Port its reviewed mathematical body next and discharge the concrete
joint-variable constraints; do not restart its proof from scratch.

## Joint waypoint choice after audit052

The joint-variable choice in thm:relgp1429–1458 is now implemented for actual
control polynomials. Independent internal waypoint labels κ and original scalar
labels σ=ZMod n×Fin2 give variables κ×σ. Every hybrid selection retains σ as its
second component, proving injectivity of its polynomial renaming. The fixed
coefficient pullbacks retain exactly the subtype excluding the moving scalar.
Thus all endpoint Δ/T, dependent slopes/resultants, scalar steps and both-coordinate
vertex differences are proved nonzero polynomials before one simultaneous choice
in the nonempty open product of prescribed waypoint sets.

No source-polynomial hypothesis, new axiom, endpoint-collar genericity shortcut
or ambient-isotopy assumption was introduced. The actual supplied overlap sets
and time subdivision still require construction; fixed original endpoints must
remain outside the independent waypoint variables. Generic endpoints may still
have inactive T zeros. The full thm:relgp remains incomplete.

The scalar homeomorphism concerns the actual product topology, without equating
its max metric with the Euclidean metric. Each actual coordinate leg is the
affine scalar line, and its unmoved Fin2 component separates every distinct pair
of vertices for every real leg parameter. These two helpers compiled in28953
terminal0; independent review is being recorded separately. The five-module joint
choice compiled in64346 terminal0 and passed independent trace62188 (23 standard-
only axiom sets), review reviews/joint-waypoint-choice.json. No source count
increment:14/132 original proofs. Preserve all reviewed modules and frozen input.

Both new partial reviews and whole audit053 now pass. Exact44/45-file independent
closures,23/9 standard-only axiom traces and both labelled local endpoints checked.
Audit053 has258SMmodules and2878localdeclarations; all251priorSMfiles and all30
accepted bindings remain unchanged. Receipt SHA256:834abff215428705dd60604d2a9fe5d0c364e7a435c201965e2205c32e5bc276.
No original count increment; full thm:relgp and main goals remain pending. Next
execute decisions/relative-general-position-after-joint-choice.md.

## Audit054 — actual central roots and Generic containment

Actual time polynomials include the scalar step; independent controls remain
nonzero constants. Every root forces true coordinate dependence, has multiplicity1
and a nonzero analytic time derivative, and changes sign. No distinct names share
a root and neither leg endpoint is a root. Actual evaluation-zero sets are finite,
isolated and retain leg labels. Actual nongeneric times are only a subset: inactive
T zeros remain allowed at Generic tuples. Independent exact48-file source/type/body
review,31 standard-only axiom traces and the nonzero derivative example passed.
Whole audit054 passed:263SM/2928declarations,all258priorSMunchanged,30acceptedbindings
current; receipt SHA256:d63e3e443df5756b8120d4e5dc1f8eeacfefe86a74491436e2dcec86e72a89c7.
No original count increment. Full thm:relgp, wall laws, soft theorem and R remain
pending. Prototype scalar boxes with true strict Euclidean diameter compiled
separately and await independent review. No author question is needed.


## Audit054 scalar-box review finalized — 2026-09-11T01:44:22Z

Independent scalar-box review and trace8113 passed. Exact prototype,23-file import closure, pinned sources, trace and audit054 supporting bytes verified; report SHA256 c2af632029508d1b7c8f860dc9e08f7608a2391038c39cc18c7ce432c278d5a5. Local boxes have actual strict Euclidean diameter bound. No original claim is accepted by this partial result. Next: exact port into a new module, then global construction and root neighbourhood obligations in the existing plan. No author input is needed.


## Audit055: actual local germs, cubes and coordinate order

The common root neighbourhood, actual centred WallGerm, Regular/Generic scalar cubes and fixed ordered coordinate legs passed independent source/type review and kernel checks. All263 oldSMmodules remain unchanged;268modules and3028local declarations pass audit055. No source row is newly accepted. Full global timing/subdivision and named-wall classification remain outstanding. The strict uniform-mesh prototype is outside the library and is being checked; its first failure was an explicit-real-bound elaboration issue, not a mathematical change. See STATUS.md and decisions/relative-general-position-after-local-germs.md. No author question is required.


## Audit055 uniform-mesh prototype finalized — 2026-09-11T02:04:14Z

The strict uniform-mesh/open-cover construction is kernel checked and independently reviewed at exact SHA aa11f56fdb9fdfcea3aec07c0803cca03b51902f4fc38b1f50730735aa4ad691. Independent trace35329 passed9 standard-only axiom sets and both examples; report SHA be0f8d94905da8cf833786080ac7181a4060c4e602111a75d094a565e49ff118. It remains outside the theorem library. Next port its unchanged body and instantiate the actual curve/cube domains before global gluing. Original progress remains14/132; full source thm:relgp is incomplete. No author answer needed.

## Audit056 — actual cube subdivision and global timed approximation

Five new modules passed independent review and the whole audit:273SMfiles,
3163local declarations; all268 priorSMfiles and all30 accepted review bindings
remain current. The single-cell timed prototype is independently reviewed. The
global N*(2n)-cell approximation passed root74114, including exact labelled
endpoints, affine cell formulas, Regular membership, synchronous Euclidean bound,
collision freedom and finite nongeneric times. Its final independent trace68093
is running; a separate global endpoint-collar extension is still unchecked.
These are parts of thm:relgp, not a completed source claim. Original proofs remain
14/132. No new axiom, source edit, endpoint restriction or scope reduction was
introduced; no author answer is needed.

## Audit056 prototype evidence finalized — 2026-09-11T02:46:04Z

Global timed approximation, collars/rescaled germs, ambient smooth graph and the
strong same-event certificate all passed independent checks. The certificate
exposes the same actual path point, control, moving coordinate and derivative;
its central other-control nonvanishing must not be mistaken for a whole-radius
product field. All scoped evidence verifiers pass. Original proofs stay14/132.
Next port the exact six reviewed bodies into new modules, preserving all273 old
SM files. Actual-root wall classification and final thm:relgp assembly remain
open. No author input or additional source is necessary for the next work.

## Audit057 — actual timed path and event geometry integrated

Six exact reviewed prototype bodies are now canonical modules. All273 priorSM
files remain unchanged. Root build46292, independent port trace39371 and whole
audit74390 passed. Audit057 covers279SM/3314 local declarations and all30 accepted
source/type/review bindings; no original count increase. The strong event
certificate attaches the actual time, path, control, derivative and ambient graph.
SingleControlCenters passed root68224 and is under independent review, retaining
actual nongenericness in the active-concurrence argument. Full wall branches,
T order changes and source theorem assembly remain; the next plan identifies
existing regular-triangle and cusp obstructions to reuse. No author answer needed.

Audit057 finalization 2026-09-11T02:57:16Z: SingleControlCenters passed independent trace85577
and its scoped verifier (90 imported modules,10 standard-only axiom sets,3 examples).
The certificate-only example derives nongenericness from the actual germ; the
conditional inactive-root example does not infer activity from a polynomial zero.
The prototype is frozen outside the canonical library. All future ports require
exact body binding. Original14/132 remains unchanged; no full wall/type/order
classification is claimed. Checkpoint057 records the next executable step.


## Single-triple source domain — 2026-09-11

INTERPRETATION TO RETAIN FOR FINAL STATEMENT REVIEW: sm-2-amplitude.tex231 calls
the critical vertices pairwise distinct, and239–240 explicitly supplies distinct
real affine coordinates xi. These geometric data must not be inferred merely
from singleton pointZeroTriples at n=3. The source polygon definition permits
coincident points, and the wall-germ definition permits a colliding center.
The independent domain note records the illustrative curve (0,0),(t,0),(0,1),
which shows why the implication from label-triple uniqueness alone is invalid.
This note is not a counterexample to the theorem with its printed distinct-xi
data, nor acceptance of a narrowed source theorem. The final geometric theorem
must make the exact printed data and this reading reviewable. Existing canonical
singlePointTriple_vertices_injective requires n>=4 and will not be applied at3.
All current array source-response proofs work without geometric distinctness.
Continue proofs locally; no author answer or change to source files is needed.

## Checkpoint091: complete soft-family candidate

No author question. All four printed clauses of lem:soft-generic are assembled
in SM.soft_family_generic_source and passed first root kernel44274. The chamber
basepoint is fixed before the common radius shrinks. Actual inherited point and
both parameter identities link the limiting functions to the geometric data;
the loop conclusion includes the oriented path through both inserted vertices.
No Generic assertion is made at epsilon0. The source and accepted map stay
unchanged; stronger statement/definition fidelity and canonical integration
remain separate obligations. The next missing A-soft work is actual duplication
composition fibers and their root-relative geometric specialization, documented
in decisions/amplitude-soft-after-family-assembly.md. This theorem is in scope
through the full cusp/comparison route; the final target remains the actual C
laws, with all soft sectors and R discharged.


## Checkpoint092: duplication candidates, no author decision required

218 implementation declarations in13 groups passed serialized root Lean runs.
They remain in a separate candidate ledger; no source row or final target was
accepted. Accepted proofs19/132 and expanded checklist39/192 are unchanged.
The exact cut/composition fibers, explicit presentation counts, proposed arrays,
scalar cancellations and actual all-root geometric far-data specialization are
checked. The weighted recurrence and complete root output remain to be proved.

Eight failed runs are preserved before repair. Seven repairs are proof-only;
OrderedBoundaryTransport's first repair also introduces statement-local NeZero
instances derived from actual endpoints in one theorem header, without adding
caller premises or changing its mathematical domain. Full-file reviews disclose
all architecture/proof contributions and do not grant stronger fidelity approval.

The implementation orders spanning rows A-only, B-only, both; source/scalar
identities put B-only first. Future weights must follow the actual subsets.
An avoiding interval starting at B needs its actual restricted preimage or the
proved alternate section; the global old section sends s to A outside it.
Actual cyclic neighbor labels already give attachment signs; the formal neighbor
position/eta bridge and all endpoint recurrence cases still require assembly.
Continue decisions/amplitude-soft-after-duplication-data.md without waiting for
an author response. Sources, accepted map and327 canonical modules stay fixed.

## Checkpoint093 — avoiding transform and starting child products

Added92 supporting candidates in six groups; all root kernel checks and six
same-model technical reviews passed (597 file bindings). Source acceptance
increment0, accepted19/132, final0/8. The actual avoiding transform equation
and starting child products are proved; starting gates and the other weighted
rows remain. No source/accepted-map/canonical change or author answer is needed.
Three failed runs21543,45759,86294 retain exact bodies/prototypes/logs; all
repairs preserve declaration headers. Passing child-factor run51575 was first
attempt. The next implementation is the actual starting gate-product plan;
row1 near/far sections differ and are explicitly documented. Full A-soft,
all-sector direct C-soft, corner laws and the R/bridge chain remain active.
Stronger fidelity and integration are pending; same-model reviews do not grant
them. This work unit is substantive progress, not a blocker recurrence.

## Checkpoint094 — complete weighted endpoint candidates

Added103 supporting declarations in ten groups. All serialized root kernel
checks and ten same-model technical reviews passed (3294 quoted file bindings).
Source increment0; accepted19/132; final0/8. Actual complete starting/ending
transforms, their ordinary inverse equations and both full-word endpoint root
outputs are proved. Strict spanning, full inverse identification and geometric
assembly remain. Failed64843/66002 retain exact evidence; proof-only repairs
preserve all headers. All prior passing candidates, sources, accepted map and327
canonical modules remain unchanged. Continue the actual spanning calculation
using existing composition-cover and uniqueness lemmas. No author question.
Stronger fidelity/integration remain pending; this is substantive progress.

## Checkpoint095 — actual no-core-cut spanning branch

Added60 supporting declarations in five groups. All serialized root checks and
five same-model technical reviews passed (890 quoted file bindings). Source
increment0; accepted19/132; final0/8. The full no-core-cut fiber has multiplier k
for ordinary and root tops, with an actual unique spanning child, every other
child, unary composition and zero factor retained. Cut-present actual neighbors
and cut images are checked, but their three-row weighted identity is next.

Failed51756/54430 preserve exact first evidence; only proof notation and a lemma
name changed, with every public header unchanged. Initial review metadata
inspection encountered a different evidence layout; an explicit095 verifier
adapter checks all the same exact receipts, bound files and axioms. The original
reader draft and compatibility note are retained, and sealed reviews unchanged.
No source/canonical/accepted-map edits or author answer are needed. Stronger
fidelity and integration remain separate. This unit is substantive progress;
the full corner soft/wall-law and full-cusp/R/bridge goal remains active.


## Checkpoint096: complete formal duplication candidate

Resolved the actual three-row spanning sum by retaining the full core gate and
child product and annihilating its residual with the actual sign-square relation.
Combined all five ordinary coordinates, used canonical triangular uniqueness,
proved the full auxiliary root identity at every position, and removed both
near arrays by the existing complete-output factorization. This yields formal
far-only duplication, not yet actual geometric A-soft or the corner theorem.

Four failed attempts are preserved; all public header texts remain unchanged.
Two dependency-only repairs add exact previously checked finite-child and
cyclic-neighbor closures. Historical dependency lists were reconstructed from
frozen ordered lists and matched to their original SHA256; original manifests
were not rewritten. A separate verifier checked60 historical bindings.

Eight same-model reviews are technical evidence only, with authorship and
contribution limits disclosed. No stronger fidelity approval or source
acceptance is claimed. Source19/132 and expanded checklist39/192 are unchanged.
Next work is actual geometric coefficient/radius/sector assembly using the
proved common geometric data. No question or permission is needed from the author.


## Checkpoint097: actual A-soft source candidate

Specialized complete formal duplication to actual geometric rooted coefficients,
derived a common positive radius and parent Genericity, bounded the radius by
any given positive epsilon0, and proved the all-nonsoft-root source equation
with unique physical correspondence and all three integer sector laws. This
completes a kernel-checked candidate for thm:A-soft. No wall law, root independence
or residual-polygon G1 is assumed. The source clause/type mapping is retained
separately for stronger review; no source acceptance is granted by this model.

All12 declarations passed first-run Lean. Three independent technical reviews
passed164 file bindings. An incorrect expected38 count from a mechanical checker
template substitution was preserved and repaired to the exact12 from2+7+3;
no proof or acceptance policy changed. All sources, accepted map,327 canonical
modules and1876 baseline files are unchanged.

Continue the actual corner-state-sum construction and direct C-soft, as recorded
in the bounded inventory. Use actual marked vertices/visits and successor swaps,
not supplied carrier bijections. All wall laws, full-cusp/comparison and R/bridge
remain in scope. No author question is needed. Accepted source19/132 and expanded
checklist39/192 remain unchanged pending stronger fidelity and integration.


## Checkpoint098: actual carrier marked traversal and successor

Constructed every original vertex/crossing mark, actual crossing twins and
selected swaps, the complete cyclic successor and its single orbit, then the
actual outgoing reconnection and its component quotient. The empty support
has exactly one component. This advances the finite successor construction in
SM3 lem:carriers, without assuming carrier bijections or cycle counts. Arbitrary
selected supports are legitimate for this permutation algebra; independence
will be discharged in the splitting/count induction. Physical endpoint equality
is proved, but positive geometric segments and actual carrier polygons remain.

All80 declarations passed in four root runs; three failed first attempts and
their exact evidence are preserved. Marks corrects an invalid nonemptiness
header to its explicit intended existential. Successor annotates the zero
index in one header and supplies a membership witness. Smoothing repairs only
two proof elaborations. No source statement or premise changed; invalid first
headers and compiler placeholders were never accepted. Four independent AI
technical reviews passed104 file bindings. Stronger fidelity/integration remain
pending; the accepted map and all327 canonical modules are unchanged.

Continue with the cycle-splitting inventory. It identifies exact pinned APIs
and the outgoing-swap convention, includes singleton components, and explicitly
leaves actual independence, inherited order and quotient count to be proved.
Main C-soft/wall laws and full-cusp/comparison/R/bridge remain incomplete.
Accepted source19/132 and expanded checklist39/192 are unchanged. No author
question or external answer is needed.


## Checkpoint099: actual singleton split and induction prerequisites

Proved the actual singleton selected permutation is its actual twin swap and
that one selected crossing produces two actual successor-orbit components,
with distinct incoming endpoint owners. The full original mark list supplies
the split representation; exact child orbits and full membership discharge
component exhaustion. Empty intervening lists and singleton children are retained.

Actual noninterlacement now yields same-original-open-arc facts. The constructed
quotient forget map and separation/refinement lemmas keep the explicit premise
that the two selected visits share a current orbit. This premise is not silently
identified with original-circle membership. The general independent-support
induction and exact plus-one fiber count remain required.

All45 declarations passed in six successful root runs. Four first failures are
preserved; every repair changes only a proof, leaving all public headers and
dependencies unchanged. Failed compiler placeholders never enter passing evidence.
Six independent AI technical reviews passed153 file bindings. Stronger fidelity
and controlled integration are still pending; source19/132 and expanded
checklist39/192 are unchanged. Sources, accepted map and327 canonical modules
remain frozen. The existing hourly thread heartbeat was verified active.

Continue the precise MarkedArcLists packet and simultaneous filtered-order /
current-orbit induction in the new architecture note. Carrier geometry and
the main C-soft/wall-law/full-cusp/comparison/R/bridge objective remain open.
No author question is needed; no residual G1 or supplied component correspondence
is introduced. The next-step note is implementation research, not proof evidence.


## Checkpoint100: actual arc slices and inherited singleton order

Added29 checked declarations deriving actual owner-filtered component cycles,
physical traversal/open-list equivalence, filtered independent-twin consequences,
and inherited successor order for empty and singleton selected support. The
current-order invariant is explicit; its singleton case is proved from actual
owner filters and child orbits. No general compatibility or remaining-pair
current-owner premise was silently assumed or discharged.

Four root runs passed. Four exact failed attempts are preserved: SortedArcLists
needed Nat-zero annotations in one invalid header; MarkedArcLists required only
a higher prototype heartbeat limit; InheritedOrder required proof-only dependent
rewriting and decision-instance transports. The MarkedArcLists repair note
corrects an earlier mistaken diagnosis: the timeout was in its unchanged sorted
arc dependency, with cascading errors, not in the owner filter. No mathematical
body was changed for that repair. Compiler placeholders are excluded.

Four independent AI technical reviews passed123 full-file bindings. Source
acceptance remains19/132; expanded checklist39/192; main targets0/8. Stronger
fidelity/integration remain pending; sources, accepted map and327 canonical
modules are unchanged. This packet contributes29 candidates, not29 accepted
source claims. No author question or additional premise is needed.

Next implement the exact local permutation-orbit transport described in the
ambient-transport note, then the actual affected/unaffected owner-filter step
and simultaneous independence induction. The note is a proposal, not a proof.
Geometry and the full corner soft/wall/full-cusp/comparison/R/bridge goal remain.


## Checkpoint101: actual ambient insertion and unaffected components

Added22 checked implementation declarations. Local EqOn and proved BijOn now
transport whole ambient orbits, including exclusion of outside marks. The
actual current split representation is derived from the original rotation and
owner filters under explicit inherited order. Applying the generic split to
actual fresh insertion gives the two exact new owner blocks and their successor
actions. Unaffected actual owner blocks and inherited cycles remain unchanged.
Freshness and same-current-owner premises are retained, not replaced by original
circle membership. No affected component is assumed to be the full circle.

Four root runs passed. Two first failures are preserved; proof-only repairs
supply an explicit list argument and eta-expand a membership application.
All22 passing traces use only permitted foundational axioms; public headers and
dependencies are unchanged. Four independent AI technical reviews passed109
bindings. Stronger fidelity/integration remain pending; accepted source19/132,
expanded checklist39/192 and targets0/8 are unchanged. Sources, accepted map
and327 canonical modules remain frozen. No author clarification is required.

Next derive affected inherited-cycle equality by filter absorption on the full
original circle and exact child filters; use this with unaffected transport for
the inherited-order insertion theorem. Then maintain remaining pair co-location
using the actual filtered physical-arc results. The next-step note specifies
these proofs but is not itself evidence. Exact counting, geometry and the full
corner soft/wall/full-cusp/comparison/R/bridge objective remain open.


## Checkpoint102: general independent-support cyclic-order induction

The actual induction is now checked for every processed subset of an independent
support. It maintains inherited cyclic order and same-current-owner equality for
all remaining selected twin pairs. Full original-circle filter absorption proves
both affected inherited-cycle identities, so insertion preserves the order
invariant. Actual filtered physical-arc membership preserves co-location. Final
independent-support statements discharge the intermediate induction premises.
Selected final-owner separation follows by erasing that crossing, processing
all others, and applying the exact actual last split. Singleton children remain.

All11 declarations passed in three root runs. One failed first attempt is
preserved; its repair changes only support-index proof transport, with no header
or dependency change. CLI heartbeat allowances for the unchanged sorted-arc
closure are recorded; no mathematical trust setting was changed. The initial
wrong-directory metadata write was corrected without changing execution.
Three independent AI reviews passed107 bindings. Source19/132, expanded39/192,
and targets0/8 remain unchanged; stronger fidelity/integration remain pending.
The carrier source lemma still needs exact count and geometric/other clauses.
Sources, accepted map and327 canonical modules remain frozen.

Next prove literal fibers of the actual quotient forget map, then one-step and
general component count using the newly checked partial invariants. The count
note is an implementation route, not count evidence. Geometry and the full
corner soft/wall/full-cusp/comparison/R/bridge objective remain open.
No author clarification is needed.


## Checkpoint103: exact independent-support successor component count

The actual quotient forget map now has proved literal affected-pair and
unaffected-singleton fibers. Finite-fiber summation gives the one-step increase.
The general induction derives its order and current-owner premises from the
checked partial invariants and proves support cardinality plus one actual
successor orbits for every processed subset of an independent support. Final
count, inherited order and selected-owner separation are bundled. This does
not identify components with connected components of their plane image union.

All7 declarations passed first time in three root runs; all axiom traces use
only permitted foundational axioms. No failures or repairs. The count closure's
larger elaboration heartbeat allowance is recorded separately without changing
mathematics or trust. Three independent AI technical reviews passed86 bindings.
Accepted source19/132, expanded39/192 and targets0/8 remain unchanged. Stronger
fidelity/integration remain pending; sources, accepted map and327 canonical
modules are unchanged. No whole carrier lemma has been accepted.

Next use the geometry note as an unproved implementation plan: derive positive
actual marked-successor subsegments including wraparound; transport them using
proved twin evaluation equality; construct affine smoothing segments and
closed component traces. True corners/regularity/turns, retained crossings,
full visit noncrossing and the full corner soft/wall/full-cusp/comparison/R/bridge
objective remain open. No author clarification is needed.


## Checkpoint104: positive smoothing segments and finite marked traces

The original successor now has a proved positive original-edge interval,
including wraparound. Exact selected-slot plane equality transfers that
interval to the actual affine smoothing segment. Nonzero original edges give
positive Euclidean length; unit parameters stay on the same original edge.
Local segment injectivity and absence of fixed actual smoothing marks follow.
Actual owner-filtered component lists inherit order under independent support,
so every modular next edge, including the closing edge, is exactly a checked
smoothing segment. Plane mapping keeps entries and does not merge owners.

All23 declarations passed in four root runs. Two failed first attempts are
preserved; explicit subtype equality and an EqOn application repair change only
proofs. No public headers/dependencies changed. All passing traces use only
permitted foundational axioms. ClosedTrace CLI allowances are recorded without
changing mathematical assumptions or trust. Four independent AI technical
reviews passed126 bindings. Verifiers passed first execution; a stale output
metadata group count was corrected before execution, with first draft preserved.
Accepted source19/132, expanded39/192 and targets0/8 remain unchanged. Stronger
fidelity/integration remain pending; sources, accepted map and327 canonical
modules are unchanged. The whole carrier lemma is not yet accepted.

Next prove actual true-corner existence using hypothetical cornerless-block
orbit transport, then construct the nonempty corner filter and prove actual
positive block compression with trace-image equality. This leads to the source
compressed cyclic tuple, regularity and the three-corner bound. A global
parameter-circle map is optional unless a concrete consumer needs it. Exact
crossings/noncrossing and the full corner soft/wall/full-cusp/comparison/R/bridge
objective remain open. No author clarification is needed.


## Checkpoint105: actual true corners and first retained blocks

A cornerless actual owner block would follow the original complete successor
circle and hence contain a vertex. This contradiction proves all-support true-
corner existence and the exact nonempty corner filter. The local visit geometry
now fixes the shared incoming/outgoing parameter on one original edge across
an unselected visit. Finite scanning constructs first retained blocks including
closing and singleton cases. The actual consumer derives its rotation, endpoint
owner, omitted noncorners, closed prefix, corner-cycle next and current successor
action from the constructed component and actual support independence.

All18 declarations passed in four root runs. FirstCornerBlock first32316 is
fully preserved; its proof-only repair avoids dependent generalization by a
proposition split and explicit cons witness. No headers/dependencies changed.
The actual block's pre-assembly simp choice is disclosed separately. All passing
traces use only permitted foundational axioms; the larger actual-block CLI
allowance changes no assumptions or trust. Four independent AI technical reviews
passed116 bindings. Source19/132, expanded39/192 and targets0/8 remain unchanged;
stronger fidelity/integration remain pending. Sources, accepted map and327
canonical modules are frozen.

The planning agent hit model capacity before writing the next-step note. Root
completed the unproved compression plan locally; mathematical progress was not
blocked. Next derive actual adjacent steps on the constructed prefix and prove
positive finite same-edge block compression with image-union equality. Then
construct the source corner tuple and prove signs, regularity and the three-
corner bound. Crossings/noncrossing and the full corner soft/wall/full-cusp/
comparison/R/bridge goal remain. No author clarification is needed.


## Handover to a new executor and SM15 realignment — 2026-09-12

The previous executor stopped at checkpoint 105. The commissioning user shipped
this package cold to a new executor with no contact to the author or anyone
else. Before shipping, the package was realigned from frame SM12 to the author's
frame SM15 (see ../SM15_REALIGNMENT.md): four reference files replaced, blueprint
regenerated, 41 source line numbers refreshed in lean-declarations.json, the
38 accepted source rows' reviews given the SM15 source hash with a byte
comparison of their statement excerpts (32 identical, 3 tag-only, 3 reworded
with a recorded re-read). lem:shift is now provable as printed; the blocked
task became ready. The library was rebuilt and the development checker passed
on the origin machine (39 mapped, 4263 audited, standard axioms only). The
reporter now reports claims verified / 132 every 15 minutes. No author answer
exists or is needed for anything above.

## Resume verification on a bare machine — 2026-09-12 (executor: Claude Code cold-start session)

- Machine: Debian 12 (bookworm) x86_64 VM, 8 cores, 31 GB RAM, 55 GB free, Python 3.11.2; no git, unzip, gcc or make installed. `unzip` was absent, so the archive was extracted with `python3 -m zipfile -e LEAN_HANDOFF_20260912_RESUME.zip .` (both sha256 sidecars verified OK first). Note: python's zipfile does not preserve executable bits, so `setup.sh` and the tools are run through `bash`/`python3` explicitly, as the documents already instruct.
- `bash setup.sh` (run as `nohup bash setup.sh > work/setup.log 2>&1 &` because the command runner has a time limit) started 2026-09-12T10:03:21Z and printed `== SETUP COMPLETE` at 10:08:20Z: about 5 minutes end to end, no stop. Passwordless sudo was available; apt installed git 2.39.5 and unzip 6.00; elan 4.2.4 installed the pinned toolchain leanprover/lean4:v4.34.0-rc2 (Lake 5.0.0); `lake update` cloned the dependencies (lake-manifest.json unchanged, byte-identical to work/lake-manifest.shipped.json); `lake exe cache get` fetched 8747 Mathlib files; `lake build` completed 3538 jobs; `verify_bundle.py` printed `FOCUSED BUNDLE VERIFIED: 87 files`; `tools/check_lean.py work/lean` printed `checker passed: True | mapped 39 | audited 4263` (receipt work/setup-check.json); the first progress line was `claims verified 19/132 (14.4%)`.
- Decision (nobody to ask): the 15-minute reporter `tools/progress.py --watch` cannot be kept as a foreground process in this command runner; `tools/progress.py --once` is run at startup and at every checkpoint instead, and its line is relayed in the execution channel.
- Decision: the re-review of the 39 accepted rows (work/STATUS.md step 4) is not part of this session's unit; this session takes one claim (step 5, lem:shift) end to end.

## lem:shift proved as printed on SM15 and accepted — 2026-09-12 (cold-start executor)

- Claim chosen by the package's process: `python3 tools/claims.py --pending-only` lists lem:shift (#41) with no unaccepted dependency, work/STATUS.md step 5 names it as the next executable unit, and SM15_REALIGNMENT.md marks it provable as printed with `SM.shift_reversal_corrected` as a helper. The rows ahead of it in the list (CV:lem:carrierword, lem:gauss-two-discs, lem:carriers, lc:single-crossing, ce:rounding, ...) show an empty dependency column only because the graph is incomplete: their source context needs Chapter 3 / CV definitions (carriers, LM evaluation, PL discs, smooth embeddings) with no accepted row yet, so none of them is a single tractable unit today.
- New module work/lean/SM/ShiftTheorem.lean (imports SM.ShiftReversal): `SM.zeroTurns` (z(P), the number of zero turns), `SM.leftTurns_add_rightTurns_add_zeroTurns` (ℓ + r + z = n, from the SignType trichotomy), `SM.leftTurns_reversal_int` (ℓ(P̄) = n − ℓ(P) − z(P) in ℤ, from `leftTurns_reversal_eq_right`), `SM.zeroTurns_eq_zero_of_generic` (from `g1_turn_nonzero`), and the row's theorem `SM.shift_reversal (hn : 3 ≤ n) (P : LabelledTuple n)` with the four printed clauses: (i) chi, edge and edgePoint identities under `shift 1` and `reversal`; (ii) Generic iff, surjectivity of `genericShift 1` and `genericReversal`, labelled and cyclic chamber images, crossingSet relabellings; (iii) the turn identities, the ℤ count identity and its generic specialisation; (iv) on Regular P: closure under both maps and the two rotation identities. Every conjunct except the counting ones is an existing lemma; no accepted declaration was touched.
- Decisions (nobody to ask): the count identity is stated in ℤ so that the printed subtraction is genuine (in ℕ it would be truncated). "Map chambers onto chambers" is stated on the cyclic quotient (`genericPolygonReversal '' chamber Q = chamber (genericPolygonReversal Q)`; σ acts as the identity on the quotient, `polygonProjection (genericShift 1 Q) = polygonProjection Q`) and, in addition, on labelled chambers. The theorem is on labelled tuples with the source's standing n ≥ 3; `[NeZero n]` is only the instance the finite sums over ZMod n need. The row's historical `scope_issue` field was kept; `sm15_note` records the acceptance.
- Kernel check: `lake build +SM.ShiftTheorem` succeeded; `#print axioms SM.shift_reversal` = propext, Classical.choice, Quot.sound; `python3 tools/check_lean.py work/lean` passed twice (work/coldstart-check1.log with the row at `implemented`, to obtain the statement hash; work/coldstart-check2.log after acceptance): 40 mapped, 4271 audited; all 40 accepted rows' map hashes equal the fresh audit hashes.
- Independent review (AI, disclosed): a separate Claude Code subagent, `reviewer-coldstart-claude-fable-5-1-20260912`, received only reference/SM/sm-0-legend.tex, reference/SM/sm-1-polygons.tex, the lem:shift excerpt (lines 496–513), the theorem type with the proof replaced by `sorry` (the copy it saw is kept as work/reviews/lem-shift-reviewer-input-statement.lean.txt) and the accepted Lean definition modules; it did not see the proof or the executor's reasoning. Verdict faithful, no discrepancies; its reason is verbatim in work/reviews/lem-shift.json. No human has read it. The re-review of the 39 earlier rows (STATUS step 4) remains open.
- Reporter after acceptance: `claims verified 20/132 (15.2%)`; checklist 40/192; targets 0/8.
- Notes for the package's maintainers, from a machine and a person that never heard of Lean: (a) `unzip` was absent and `python3 -m zipfile -e` works but drops executable bits (harmless: everything is run through `bash`/`python3`); the archive extracts flat into the current directory, with no wrapper folder, which START_HERE does not say. (b) setup.sh needed no intervention and took 5 minutes, not 15–90. (c) `tools/progress.py --watch` cannot run inside a non-interactive command runner; `--once` at each checkpoint was used. (d) The "ready" order of tools/claims.py puts rows first whose prerequisites have no accepted definition; work/STATUS.md step 5 was the real pointer to the next unit. (e) lean/ENVIRONMENT.md does not say that the statement hash only appears in work/checks/declaration-audit.json after the row is set to `implemented` and the checker is run; this was read off tools/check_lean.py. (f) BUILD_LOG.md cites a COLD_TEST.md that is not in the package. (g) The review-file schema in ENVIRONMENT.md lists the required keys but not the AI-disclosure and reviewed-files conventions of the existing files; those were copied from work/reviews/lem-rot.json.

## Session start on Mark's RunPod home pod — 2026-09-13 (executor: Claude Code, claude-fable-5-1)

- Machine: Linux x86_64 CPU pod, 8 vCPU, 124 GB RAM, network volume at /workspace (petabyte-scale
  filesystem, ~1 TB free quota). Package unzipped with `unzip` into
  /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/ (zip sha256 matched the sidecar;
  `sha256sum -c MANIFEST.sha256`: 3429/3429 OK).
- Decision (nobody to ask): the system python3 is 3.8.10, below the 3.9 floor of the tools, so a
  `uv` virtual environment with Python 3.11.8 was created at /workspace/envs/lean/py and put first
  on PATH before `bash setup.sh`; setup.sh then accepted it. Decision: elan was installed into
  /workspace/envs/lean/elan (`ELAN_HOME`, with `/root/.elan` a symlink to it) so that the
  toolchain survives pod re-creation; setup.sh's `$HOME/.elan/bin` PATH entry resolves through
  the symlink. Both are recorded in /workspace/envs/lean/env.sh, sourced in every shell.
- setup.sh started 2026-09-13T13:03Z as `nohup bash setup.sh > work/setup.log 2>&1 &`
  (tool-limited command runner). Progress lines are relayed by `tools/progress.py --once`
  at each checkpoint; startup line: `claims verified 20/132 (15.2%)`.
- Plan for the first unit (tools/claims.py --next = thm:single-triple, sm-2-amplitude.tex:234):
  port the previous executor's kernel-checked candidate closure of
  `SM.WallGerm.single_triple_integer_response_of_support` (32 bodies, 2,709 lines, prototype
  UnorderedIntegerSingleTripleResponse, kernel session 17021, standard axioms only) verbatim into
  32 chained modules under work/lean/SM (generator: work/port/make_single_triple_modules.py), then
  add work/lean/SM/SingleTripleWallResponse.lean with the row theorem
  `SM.WallGerm.single_triple_wall_response`, stated with lem:farout's `𝓔_J`/`𝓑_J` written out
  over ℚ (`gapE`/`gapB`, `wallU`/`wallV`) rather than the candidate's integer gap values, so
  that the type reads as printed; then independent review, acceptance, checker, checkpoint.
- Decision (2026-09-13T13:26Z, nobody to ask): the first setup.sh run stalled in Mathlib's
  `cache get`, which reads the Mathlib sources through io_uring; on this pod's FUSE-mounted
  network volume that ran at about 100 KB/s with no download started after ten minutes. The
  Lean build tree was therefore relocated to the pod's local disk: `work/lean/.lake` is now a
  symlink to /root/lean-lake and the toolchain lives in /root/.elan (real directory), with the
  volume copy /workspace/envs/lean/elan kept for re-creation. Everything else (sources, work/,
  receipts) stays on the volume. If the pod is re-created, re-run `bash setup.sh` (it re-clones
  and re-downloads; the cold test measured 5 minutes on a local disk). setup.sh was re-run after
  the relocation; its log continues in work/setup.log.

## thm:single-triple proved as printed on SM15 and accepted — 2026-09-13 (pod executor)

- Setup: `bash setup.sh` completed at 13:40Z after the relocation of the build tree to local disk
  (above): lake build 3538 jobs, verify_bundle OK, `checker passed: True | mapped 40 | audited 4271`,
  `claims verified 20/132`.
- Unit chosen by `python3 tools/claims.py --next`: thm:single-triple (sm-2-amplitude.tex:234, six
  labels thm:single-triple, afr:wall-data, afr:wall-epsilons, afr:wall-uv, afr:wall-proper,
  afr:wall-full).
- Port (ACCEPT_CYCLE step 2): the previous executor's kernel-checked closure of
  `SM.WallGerm.single_triple_integer_response_of_support` (receipt
  work/checks/UnorderedIntegerSingleTripleResponse-prototype-result.json, session 17021, all 32 body
  hashes re-verified against the receipt) was copied byte-for-byte into 32 new modules
  work/lean/SM/<Body>.lean in the prototype's concatenation order, each importing the prototype's
  header and every predecessor body (generator: work/port/make_lane_modules.py; the generator
  refuses collisions and hash mismatches). No body text was changed; only import headers and a
  provenance docstring were added. The whole chain compiled first try (`lake build`, 3156 jobs).
- Row module work/lean/SM/SingleTripleWallResponse.lean, main declaration
  `SM.WallGerm.single_triple_wall_response`. Decisions (nobody to ask):
  (1) The gap values are written as lem:farout(iii)'s objects over ℚ — `gapE H J = F_H(c)_J`,
  `gapB H J = F_{-H}(c)_J` with `c = farOnlyCoordinates H = F_H⁻¹(E)` — and `wallU`/`wallV` are the
  afr:wall-uv switches on them, so the type reads as printed; the candidate's integer gap values
  (closed-gap tree coefficients) are not in the type (they are lem:farout(iii)'s content).
  (2) The identity is stated in ℚ (casts of the integer tree coefficients), the ring in which the
  source's E/B values live ("the auxiliary coordinates c may be rational").
  (3) "a single triple of pairwise distinct vertices" is transcribed as pairwise physical
  distinctness of the three centre points (`hK`); label distinctness is already part of Z_pt, and
  the printed affine writing with distinct ξ_v presupposes it. For n ≥ 4 it follows from Z_pt = {K};
  it binds only at n = 3. All five reviewers concurred.
  (4) The sign change is stated for one ordering a,b,c of K (χ is alternating, so equivalent).
  (5) The conclusion asserts existence and uniqueness of the increasing reading t of K at root g,
  existence of an affine writing, the response for EVERY affine writing (ε_L, ε_R are invariant
  under affine reparametrisation), δ as one d ∈ {−1,1} with H⁺ − H⁻ = 2d on all sufficiently close
  independent side parameters, and for Q (proper case) G1, ≥ 3 vertices and root retention as
  `Q 0 = μ_g`, `Q 1 = μ_{g+1}`, `edge Q 0 = edge P(0) g`. Gap and contracted values are at the centre.
- Kernel check: `#print axioms SM.WallGerm.single_triple_wall_response` = propext, Classical.choice,
  Quot.sound; `tools/check_lean.py work/lean` passed with the row at implemented (41 mapped, 4579
  audited; statement hash 09f0f368…0350) and again after acceptance; all 41 accepted hashes equal the
  fresh audit.
- Independent review (AI, disclosed): one workflow of five separate Claude Code subagents — three
  reviewers with distinct lenses (hypotheses; quantifiers/conclusions/evaluation convention;
  definition expansion) and two adversarial refuters — each given only the printed source, the type
  with proofs replaced by sorry (work/reviews/thm-single-triple-reviewer-input-statement.lean.txt) and
  the definition modules. Verdicts: faithful, faithful, faithful, no discrepancy found (both
  refuters). Review file work/reviews/thm-single-triple.json (primary reason plus countersignatures
  and refutation reports verbatim; raw workflow output in
  thm-single-triple-review-workflow-raw.json). No human has read them.
- Reporter after acceptance: `claims verified 21/132 (15.9%)`; checklist 41/192; targets 0/8.
- Note on the candidate lane: the same generator ports the other prototypes (flat, cusp,
  vertex-edge, triple/silent, soft-generic, soft amplitude) with body reuse; ported modules are
  reused, never duplicated.

## def:induced-roots accepted — 2026-09-13 (pod executor)

- Row def:induced-roots (sm-2-amplitude.tex:385): module work/lean/SM/InducedRootsDefinition.lean,
  main declaration `SM.induced_roots_definition : InducedRootsDefinitionData`, with
  `SM.deletionRoot j g := fusionIndex j g` (= D_j(g)) and `SM.halfRoots M a g := contactHalfRoots M a g`
  (= H(g)); the bundles `DeletionRootData` (fused edge for incident roots; same-endpoint edge, unique,
  otherwise) and `HalfRootsData` (d₁, d₂, the three root rows, exhaustive/exclusive cases) state the
  printed case descriptions. Supporting candidate bodies ported verbatim: ContactRootPartition,
  ContactHalfRoots (receipt ContactHalfRoots, session 90785) and PhysicalDeletionRoots (session 15649).
- Decisions (nobody to ask): the deletion-map data is stated for every P with n+1 ≥ 4 vertices and
  every j (D_j is combinatorial; the source scopes it to flat/cusp walls, whose centres are such P);
  the half-map data at every simple vertex–edge wall (VertexEdgeAt), mirroring the accepted
  def:deletion-halves row. Arcs {M,…,a−1} and {a+1,…,M−1} are `(g − M).val < contactDistance M a`
  and `contactDistance M a < (g − M).val` with `contactDistance M a = (a − M).val`.
- Kernel check: axioms propext, Classical.choice, Quot.sound; checker passed at implemented (42
  mapped, 4643 audited; hash f0982b94…1ed3) and after acceptance (45 mapped incl. three implemented
  rows, 4988 audited); all accepted hashes match.
- Independent review (AI, disclosed): workflow of five subagents (lenses: deletion map; half map;
  domain/quantifiers/form; two adversarial refuters) — faithful ×3, no refutation. Two reviewers noted
  that uniqueness of "E_g in λ₁/λ₂" is inherited from the accepted HalvesData injectivity rather
  than restated; recorded in reviews/def-induced-roots.json. Checklist 42/192.
- Pipeline note: the rows thm:A-S3 (SM.FlatLawTree), thm:A-S4 (SM.CuspLawTree), thm:A-S7
  (SM.VertexEdgeLawTree) and thm:A-R3E (SM.TripleSilentLawsTree) are implemented on top of the
  ported lanes FlatSourceResponse, CuspSourceResponse, ContactSourceResponse, TripleSilentTreeLaws
  (bodies shared between lanes are reused, never duplicated) and are under independent review; they
  are accepted one at a time as each review returns.

## thm:A-S3 (flat law for A_g) accepted — 2026-09-13 (pod executor)

- Module work/lean/SM/FlatLawTree.lean, declaration `SM.WallGerm.flat_law_treeCoefficient`, on the
  ported lane FlatSourceResponse (14 new modules, 32 reused from the single-triple lane). Statement:
  unique right/left sides (FlatRightSide/FlatLeftSide), G1 of P(0)∖j, and the identity at every point
  of each side with D_j = deletionRoot. Review: five subagents (hypotheses; sides and quantifiers;
  definitions; two refuters) — faithful ×3, no refutation; reviews/thm-A-S3.json. Checker after
  acceptance: 46 mapped (43 accepted + 3 implemented awaiting review), 5023 audited; claims 22/132.

## thm:A-S4 (cusp law) and thm:A-S7 (vertex–edge law) accepted — 2026-09-13 (pod executor)

- thm:A-S4: module SM.CuspLawTree, declaration `SM.WallGerm.cusp_law_treeCoefficient`, lane
  CuspSourceResponse (5 new modules, 46 reused). Statement: unique cusp case b, the loop side as the
  side on which the newborn pair {cuspFirst b j, cuspLast b j} is a crossing (at every point) and not
  on the other side, κ ∈ {−1,1} as the rotation-number difference at every pair of side points, the
  law −κ·A_{D_j(g)}(Q) at every pair of side points, with the printed hypothesis hQ : G1 Q explicit.
  Review: five subagents, faithful ×3, no refutation (reviews/thm-A-S4.json).
- thm:A-S7: module SM.VertexEdgeLawTree, declaration `SM.WallGerm.vertex_edge_law_treeCoefficient`,
  lane ContactSourceResponse (9 new, 38 reused). Statement: bigon ∨ sliding, s = contactSign (χ_{a,a+1,M}
  on the negative side, nonzero and constant there), G1 of both halves, and the law at every pair of
  side points with (h₁,h₂) = halfRoots (def:induced-roots). Review: faithful ×3, no refutation
  (reviews/thm-A-S7.json). Claims verified 24/132; checklist 45/192.
- Soft lanes ported verbatim: SoftInsertionTuple (4 new, 1 reused), SoftFamilyAssembly (28 new, 5
  reused), SoftAmplitudeSource (45 new, 11 reused). Rows implemented and under review: def:soft
  (SM.SoftInsertionDefinition, `SM.softInsertion_definition`; the lane already had a lemma named
  soft_insertion_definition, hence the camel-case name), lem:soft-generic (SM.SoftGenericLemma,
  `SM.soft_family_generic`, the candidate's four-clause statement restated verbatim as the row),
  thm:A-soft (SM.SoftTheoremTree, `SM.SoftDuplication.soft_theorem_treeCoefficient`, the candidate's
  statement restated verbatim: for every ε0 > 0 one ε₁ ∈ (0, ε0] for all roots, A_a(P_ε) =
  ((χ₋+χ₊)/2)·A_g(P) in ℚ plus the three integer sector laws).

## def:soft accepted — 2026-09-13 (pod executor)

- Module SM.SoftInsertionDefinition, declaration `SM.softInsertion_definition : SoftInsertionDefinitionData`
  (bundle SoftInsertionData: label bijection and cyclic order of P_ε, vertices, the three edge classes,
  both attachment-sign identities as chirotope entries and as determinant formulas, admissibility), for
  every P, j, q and ε > 0. Review: five subagents (tuple/labels; edges/signs; admissibility/domain; two
  refuters, one with hand computations for n = 4 and n = 5) — faithful ×3, no refutation; two reviewers
  noted that the parenthetical gloss "(they are the turns at the two ends of the soft edge, with the
  sign reversed)" is not in the bundle (it is lem:soft-generic (ii)), and that the bundle pins the
  labelling cyclically while the definitions carry the literal labels. reviews/def-soft.json.
  Checklist 47/192; claims 25/132.

## thm:A-soft accepted — 2026-09-13 (pod executor)

- Module SM.SoftTheoremTree, declaration `SM.SoftDuplication.soft_theorem_treeCoefficient` (the
  candidate soft_amplitude_source of lane SoftAmplitudeSource restated verbatim). Review: five
  subagents (hypotheses/epsilons; root correspondence with hand-computed index maps; identity and
  sector multipliers; two refuters) — faithful ×3, no refutation; all noted the Lean is stronger
  (arbitrary ε0 > 0, one ε₁ for all roots, genericity of P_ε asserted, ∃! parent root). reviews/thm-A-soft.json.
  Claims 26/132; checklist 48/192.

## lem:soft-generic accepted — 2026-09-13 (pod executor)

- Module SM.SoftGenericLemma, declaration `SM.soft_family_generic` (the candidate
  soft_family_generic_source of lane SoftFamilyAssembly restated verbatim, with a notation
  docstring). Review: six subagents (one lens per clause group (i)–(iv), two refuters) — faithful ×4,
  no refutation. Two reviewers flagged a documentation-only note: the docstring described the
  Tendsto clauses as one-sided limits while the type proves two-sided limits at 0 of globally
  defined functions (stronger than printed); the docstring was corrected before acceptance
  (statement hash unchanged). reviews/lem-soft-generic.json. Claims 27/132; checklist 49/192; no
  row awaiting review. State of the tree-amplitude chapter (sm-2): every row except
  prop:A-reversal is accepted; prop:A-reversal has no candidate and is being proved from scratch
  (drafts in work/drafts).

## prop:A-reversal proved from scratch; row implemented — 2026-09-13 (pod executor)

- No candidate existed in the lane. Two independent Claude Code prover subagents (workflow
  prove-A-reversal) each produced a compiling, sorry-free draft in work/drafts, checked only with
  `lake env lean` (no shared build writes). Both proved `treeCoefficient_shift_one` (from the accepted
  treeCoefficient_shift) and `treeCoefficient_reversal : A_{1-g}(P̄) = (-1)^n A_g(P)` by the source's
  argument: reversal of intervals and compositions (a bijection), negation of every near and far sign
  under the reversed reading (chi_swap_outer), hence V^±(π) ↦ (-1)^(parts-1) V^±(π), and induction on
  leaves for the open sums (b ↦ (-1)^(leaves-1) b), then the rooted sum. Attempt B, which isolates an
  abstract sign-twisted transport lemma for openTreeRec/rootedTreeRec with arbitrary weights, was
  ported verbatim as work/lean/SM/TreeReversal.lean (provenance docstring added, #print lines
  removed); both drafts were then deleted from work/drafts (rule: finished or deleted). The executor
  re-compiled both drafts and re-scanned them for sorry/admit/native_decide/axiom before porting.
- Row module work/lean/SM/ReversalShiftLaw.lean, declaration `SM.treeCoefficient_reversal_shift_law`:
  (i) A_g(shift 1 P) = A_{g+1}(P); the recorded definition ∀ i, reversal P i = P (2 - i); (ii)
  A_{1-g}(reversal P) = (-1)^n A_g(P); for every P with G1 and every root g, n ≥ 3. Axioms standard;
  checker passed at implemented (50 mapped, 6379 audited; hash 18c1ce2a…583f). Review workflow launched.

## Carrier lane ported; def:decomposition implemented — 2026-09-13 (pod executor)

- The previous executor's Carrier lane (prototypes CarrierComponentCount, 24 new modules, and
  CarrierActualCornerBlock, 7 new modules; 21 bodies shared) was ported verbatim into work/lean/SM.
  One module, SM.CarrierSortedArcLists, hit the default heartbeat limit as a separate module although
  its body compiled inside the one-file prototype (instance-search order differs between the two
  environments); `set_option maxHeartbeats 1600000` was added at the top of that module with a note.
  No declaration text was changed. Nothing in the lane is accepted; rows will cite it.
- Row def:decomposition (sm-3-statesum.tex:9): module SM.DecompositionDefinition, declaration
  `SM.decomposition_definition`, with `IsDecomposition hn hP S := S ∈ independentSupports hn hP` and
  `decompositions := independentSupports` over the accepted def:interlace objects; stated for every
  generic P with n ≥ 3 (the chapter's standing assumption). Checker passed at implemented; review
  workflow to follow.
- Scouting maps for Chapter 3 and the transport/comparison chapters (four reader subagents) are in
  work/reports/chapter3-scout-20260913.json. Plan adopted: two parallel lanes — (a) the
  Chapter-3-free transport chain (def:star, lem:star-generic, lem:transport-angle-interval,
  lem:transport-lengths, lem:soft-rotation, def:anchors, …; fresh proofs, prover subagents in
  work/drafts) and (b) Chapter 3 definitions over the Carrier lane (def:decomposition,
  conv:selected-visits, def:smoothing), then lem:carriers split into supporting rows.

## prop:A-reversal accepted — 2026-09-13 (pod executor)

- Module SM.ReversalShiftLaw, declaration `SM.treeCoefficient_reversal_shift_law`, on the fresh proof
  module SM.TreeReversal (prover subagent attempt B, see above). Review: five subagents (shift clause;
  reversal clause; domain/form; two refuters, one with a hand computation) — faithful ×3, no
  refutation; two reviewers noted only the redundant `[NeZero n]` instance. reviews/prop-A-reversal.json.
  Claims 28/132; checklist 50/192. Every claim row of sm-2-amplitude.tex is now accepted.

## def:decomposition accepted — 2026-09-13 (pod executor)

- Module SM.DecompositionDefinition, declaration `SM.decomposition_definition`; IsDecomposition :=
  membership in the accepted independentSupports (Ind(G_P)). Review: two reviewers + one refuter,
  faithful / not refuted; reviews/def-decomposition.json. Checklist 51/192; claims 28/132.

## Re-review of the 39 handover rows launched — 2026-09-13 ~15:40Z (pod executor)

- STATE_OF_WORK.md section 4 asks for a re-review of the rows accepted before this session by a
  separate reviewer session, and a countersignature of the three SM15 re-reads (lem:chi-basic, lem:g1,
  prop:A-chamber). A workflow of 39 independent reviewer subagents (one per row; list in
  work/port/rereview_rows.json; each reads the SM15 extract and the Lean statement, proofs skipped,
  and may compare with the existing review only after forming its own judgement) is running. On
  return, a `countersignature_20260913` block will be appended to each review file, and any row
  flagged not faithful will be re-examined (statement fixed and re-reviewed, or a repair note filed).

## conv:selected-visits accepted; seven prover drafts ported — 2026-09-13 (pod executor)

- conv:selected-visits: module SM.SelectedVisitsConvention, declaration `SM.selected_visits_convention`
  (finite successor model of the source proof; see the module docstring). Review: five subagents —
  faithful ×3, no refutation; reviewers noted the closing meta-sentence is reflected structurally.
  reviews/conv-selected-visits.json. Checklist 52/192; claims 28/132.
- Seven prover drafts (all compiled sorry-free with standard axioms; re-compiled and token-scanned by
  the executor) ported verbatim into work/lean/SM with provenance headers, drafts deleted:
  TransportAngleInterval (lem:transport-angle-interval), StarPolygons (def:star K_r, lem:star-generic
  (i)-(iii)), BowTie (K_0, lem:star-generic (iv)), TransportLengths (lem:transport-lengths),
  SoftRotation (lem:soft-rotation), CarrierCrossings (def:smoothing: crossings of a carrier, m_Q,
  corner directions, unselected non-neighbour ownership), CarrierNeighborSeparation (a crossing
  interlacing a selected crossing has its visits on different carriers — the N(S) sentence of
  def:smoothing / lem:carriers (iii)). Rows to be stated on top of them next.

## Six rows implemented on the prover modules — 2026-09-13 ~15:55Z (pod executor)

- Rows implemented (kernel-checked, hashes in work/checks/dev-check-six-implemented.json, 58 mapped,
  7054 audited; review workflow running): lem:transport-angle-interval (SM.TransportAngleIntervalLaw,
  `SM.transport_angle_interval_law`), def:star (SM.StarDefinition, `SM.star_definition`: u_k, K_r t =
  u_{r(t−1)} with the source label t as the residue t and N ≡ 0, K_{−r} = reversal K_r, the bow-tie at
  labels 1..4), lem:star-generic (SM.StarGenericLaw, `SM.star_generic_law`: clauses (i)–(iii) from
  SM.StarPolygons and (iv) from SM.BowTie; clause (ii) "tangent at the midpoint" stated as midpoint norm
  ρ, edge ⟂ midpoint, all other points of the edge line farther), lem:transport-lengths
  (SM.TransportLengthsLaw, `SM.transport_lengths_law`, for any finite index type of directions on
  Set.Icc a b), lem:soft-rotation (SM.SoftRotationLaw, `SM.soft_rotation_law`), def:smoothing
  (SM.SmoothingDefinition, `SM.smoothing_definition`: carriers = cycles of ρ_S, traced curve
  componentPlaneCycle, corners IsTrueCorner/componentCornerCycle, arrival/leaving directions at vertex
  and smoothing corners, crossings of a carrier and m_Q, the N(S) sentence — both halves proved).
- Name clashes between independently written prover modules were resolved by renaming helpers only:
  StarPolygons.planeDot_add_right → star_planeDot_add_right (clashed with the accepted
  DirectionProjection.planeDot_add_right), TransportLengths.planeDot_smul_left / planeDot_sub_right →
  tl_planeDot_smul_left / tl_planeDot_sub_right (clashed with StarPolygons). No statement changed.

## Re-review of the 39 handover rows complete — 2026-09-13 ~16:15Z (pod executor)

- All 39 rows accepted before this session were re-reviewed by independent reviewer subagents (one per
  row; SM15 extract vs the Lean statement, proofs skipped, own judgement formed before reading the
  existing review). Verdicts: 39 × faithful. Two rows carried reviewer notes listed under
  "discrepancies" that the reviewers themselves marked benign/non-disqualifying: def:weak (helper
  definitions defined for every n; G2 read on distinct indices, inherited from def:generic; both chamber
  readings provided; rfl clauses; an untranslated terminology sentence) and lem:treesum-trees (the
  "specializes to every evaluation" clause is rendered as evaluation of the formal recursion, with the
  evaluated identity following from the formal one by ring-homomorphism bookkeeping and separately
  proved in SM.PlaneTreeExpansion.rootedTreeRec_eq_signed_planeTreeSum). No statement was changed.
- A `countersignature_20260913` block (verdict, reason, notes, files read, AI disclosure) was appended to
  each of the 39 review files, and the three SM15 re-reads (lem:chi-basic, lem:g1, prop:A-chamber) received
  `source_realignment.re_review.countersign_20260913`. STATUS step 3 (re-review) is done. Raw output:
  work/reviews/rereview-handover-rows-20260913-raw.json. The development checker passes after the edits.

## def:star, lem:star-generic, lem:transport-lengths, lem:soft-rotation accepted; two rows revised — 2026-09-13 ~16:30Z

- Accepted (five-agent reviews, all faithful / not refuted): def:star (SM.StarDefinition), lem:star-generic
  (SM.StarGenericLaw), lem:transport-lengths (SM.TransportLengthsLaw), lem:soft-rotation (SM.SoftRotationLaw).
  Claims 31/132; checklist 56/192.
- lem:transport-angle-interval: one adversarial refuter (of five agents) objected that the printed
  "Conversely" sentence is an unconditional statement while the row asserted it under the theorem-level
  step hypothesis. Decision: restate — the step hypothesis is now a premise of the forward direction only
  and the converse is stated for every finite real sequence (the module's transport_angle_interval_converse).
  New hash; second review round.
- def:smoothing: two of three reviewers judged the first bundle not faithful — it did not tie the traced
  curve (componentPlaneCycle) to the ρ_S-cycle, did not certify straight passage through unselected
  visits (hence that the corners are exactly the printed ones), and did not state the turning at
  smoothing corners. Decision: strengthen the bundle with traced_marks (componentMarkList lists exactly the
  owned marks, in the inherited cyclic order, = componentCycle), traced_successor (consecutive entries are
  ρ_S-successors, cyclically), traced_sides (componentTraceEdge: straight sides between consecutive marks,
  nonzero, continuous, closing up), unselected_visit_straight (incoming and outgoing pieces at an owned
  unselected visit lie on E_{v.2} with positive direction) and smoothing_corner_transverse
  (det(ℓ_{v.2}, ℓ_{twin.2}) ≠ 0, from the accepted crossing_edgeParameter_det_ne_zero; an import of
  CarrierSelfIntersections was avoided because that module imports the smoothing row). New hash; second
  review round.
- lem:carriers (i)–(iv) implemented as SM.CarriersLemma (`SM.carriers_lemma`) on the lane plus the three
  prover modules CarrierNoncrossing (iv), CarrierCornerPolygon (ii), CarrierSelfIntersections
  (iii)-geometric, all compiled sorry-free by prover subagents and ported verbatim; review running.

## lem:carriers accepted; anchors / small-values / mycyclic ported and stated — 2026-09-13 ~16:50Z (pod executor)

**lem:carriers accepted** (row `SM.carriers_lemma`, module `SM.CarriersLemma`, hash
e752941b…). Review workflow: four lens reviewers (one per printed clause) all faithful, two
adversarial refuters (one worked a square with one crossing) found nothing; review file
reviews/lem-carriers.json. Two reviewers attached MINOR/non-blocking notes on encoding choices, all
"judged adequate" by their authors; recorded here as optional strengthenings, not done, because each
would change the statement hash and need a fresh review: (a) "independent of the order of
reconnections" is structural (ρ_S is defined from S alone, as in the printed proof sm-3:106-109 and
the accepted def:smoothing row); the commutation facts `selectedMarkPerm_commute` and
`smoothingSuccessor_union_of_disjoint` exist in CarrierSmoothing and could be bundled; (b) the
carrier/corner-polygon identification is a trace set equality plus `inherited_order`, not a
parametrised equality; (c) "transverse" is encoded by the outgoing germs at the two visits plus
det(d_i,d_j) ≠ 0; the incoming-germ conjuncts proved in
`CarrierSelfIntersections.carrier_selfIntersection_transverse` are not in the bundle (they follow
from "none is a corner" with (ii)). `write_review_and_accept.py` now derives the reviewer/refuter
counts from the data (it had "five/three/two" hard-coded).

**Transport-lane-2 drafts ported verbatim** (header added, `#print axioms` lines removed):
work/drafts/Anchors.lean → SM/Anchors.lean; SmallValues.lean → SM/SmallValues.lean;
MyCyclicB.lean → SM/MyCyclicB.lean. `lake build` of the three succeeded. No declaration-name
collisions with the library (checked by a sorted-name diff before porting). Decision: of the two
independent compiling proofs of thm:mycyclic, the JoinedIn-based MyCyclicB is the library module
(its assembly `mycyclic_B` / `mcB_four_components` / `mycyclic_B_orbit_polygon` matches the printed
clauses most directly); the Path-based MyCyclicA stays in work/drafts as a cross-check and is not
imported anywhere. Rule 5 (no accumulation of unaccepted candidates): only one proof is in the tree.

**Rows implemented** (statement modules written by the executor, proofs by the ported modules):
- def:anchors → `SM.anchors_definition : AnchorsDefinitionData` (SM/AnchorsDefinition.lean): a
  specification of the structures SoftAnchorData / ZeroAnchor / LoopAnchor / LoopAnchorZero /
  Anchor — common data with the lem:soft-generic bound as data (`bound`, `bound_spec`: generic and
  one chamber on (0, ε₀)), the soft edge E_j at label `softOldIndex j j`, the (Z)/(L)/(L₀)
  conditions, the exhaustive `cases` of the inductive, and the projections. Notation: (n, r) =
  ((m : ℤ) + 1, r) with m the parent's vertex count. Hash 3837a5ad….
- prop:anchors-exist → points directly at the prover's bundle `SM.anchors_exist` (SM/Anchors.lean),
  whose docstring is already a sentence-by-sentence map; a separate row module would only duplicate
  a 30-line type. Its sixth conjunct (prescribed parent and vertex in (L₀) and (L)) is unprinted;
  the brief asks the reviewers to classify it. Hash 2a51d2f6….
- lem:A-small-values → `SM.A_small_values_lemma` (SM/SmallValuesLemma.lean): clause (i) with
  ∃ τ ≠ 0 common to all turns and A_g = −τ at every root g : ZMod 3; clause (ii) for every integer
  k with σ^k = `shift (k : ZMod 4)`. Hash 107815bf….
- thm:mycyclic → `SM.mycyclic : MycyclicData n r` (SM/MycyclicTheorem.lean) under
  `Admissible n r`: `joined` ((n,r) ≠ (4,0): JoinedIn in {Q | Regular Q ∧ rot Q = r}),
  `joined_shift` ((4,0): ∃ k, JoinedIn … P (shift k P')), the bow-tie clause as four fields
  (`bowTie_mem`, `bowTie_components` (joined ↔ equal), `turn_word_constant`, `bowTie_turn_words`),
  and `orbit_fibre_pathConnected` on `Polygon n hn` with `instTopologicalSpaceQuotient` (the fibre
  is the set of orbits of REGULAR tuples of rotation r — the theorem's own context ℛ_n; the brief
  asks the reviewers to judge this reading against 𝒰_{n,r} of def:admissible). The sets are written
  literally so the reviewers need no local fibre definition. Hash ad5a2733….
Checker (dev mode, 16:44Z): mapped 63, audited 7703, passed. Review workflow for the four rows
launched 16:45Z (3+2 / 3+2 / 2+1 / 3+2 agents; briefs work/port/review_prompt_{def-anchors,
prop-anchors-exist,lem-A-small-values,thm-mycyclic}.md; reviewer inputs and source excerpts in
work/reviews/). Second-round reviews for def:smoothing and lem:transport-angle-interval launched
16:33Z on the revised statements (hashes 5109db8b…, ced7b9f3…).

## lem:transport-angle-interval and def:smoothing accepted (second round) — 2026-09-13 ~17:00Z (pod executor)

Both second-round reviews returned clean: lem:transport-angle-interval (2 lenses faithful, 0
discrepancies; 1 refuter tried steps of exactly π, N = 0, spans of exactly π — nothing) and
def:smoothing (3 lenses faithful; 2 refuters, one re-ran the quadrilateral-with-one-crossing
example — nothing). Review files reviews/lem-transport-angle-interval.json and
reviews/def-smoothing.json carry the first-round history in executor_notes. One actionable note
from the def:smoothing reviewers was fixed before acceptance: the docstring of the field
`unselected_visit_straight` claimed the outgoing piece lies on the visited edge while the field
only fixes its direction; the docstring now matches the field (the checker re-ran: hash 5109db8b…
unchanged, docstrings are not hashed; mapped 63, audited 7703, passed). The remaining notes are
representation remarks (finite successor model for Γ(P); the traced curve given as cyclic vertex
list plus glued straight sides; corners as marks) — recorded in the review file, no action.
Progress: claims verified 33/132 (25.0%), checklist 59/192.

## def:anchors, prop:anchors-exist, lem:A-small-values, thm:mycyclic accepted; lem:transport proved; def:uniform stated — 2026-09-13 ~17:10Z (pod executor)

**Four acceptances** (review workflow of 16:45Z, 18 agents: 3+2 / 3+2 / 2+1 / 3+2 lenses+refuters):
every reviewer faithful with zero discrepancies, every refuter empty-handed. Review files
reviews/{def-anchors,prop-anchors-exist,lem-A-small-values,thm-mycyclic}.json. Two interpretive
notes adopted from the reviewers: (a) def:anchors — `bound_spec` renders the printed gloss "on
(0, ε₀) the insertion is generic and lies in one chamber" (clause (i) of lem:soft-generic), not an
ε₀ for which all of (i)–(iv) hold; the reviewers checked that in the mixed and loop sectors (the only
ones anchors use) the readings coincide; (b) thm:mycyclic — "every fibre of cyclic polygon orbits" is
read as the orbits of REGULAR tuples of rotation r (the theorem's own context ℛ_n), not the generic
fibre 𝒰_{n,r} of def:admissible; the reviewers judged this the reading the printed theorem
supports. prop:anchors-exist's unprinted sixth conjunct (prescribed parent and vertex in (L₀) and
(L)) is a faithful strengthening. Checker before acceptance: mapped 65, audited 7730, passed.
Progress: claims verified 36/132 (27.3%), checklist 63/192.

**lem:transport proved.** Statement fixed by the executor in work/drafts/TransportLemma_statement.lean
(vertex count written n + 1 so that `deleteVertex` types; admissibility of (n+1, r) NOT assumed —
it follows from lem:fibres; conclusion: ∃ k with (k = 0 unless (n+1, r) = (4, 0)), a continuous
regular path from P to shift k Z, affine `a + t • b` on the closed cells of a uniform mesh, finitely
many nongeneric parameters, at each a simple WallGerm whose curve is the path near t, of type
FlatAt / VertexEdgeAt / TripleAt / ExtensionAt / PureCutAt, with generic deletion at (F) and generic
halves of size < n + 1 at (V)). Two independent prover subagents both produced sorry-free proofs
(assembly of `mycyclic`, `relative_general_position`, `children`; admissibility via
`genericFibre_nonempty_iff` / `generic_rotation_exists_iff`). Draft A (129 lines) ported verbatim as
SM/TransportLemma.lean (row `SM.transport_lemma`); draft B kept in work/drafts as a cross-check.
Review launched 17:03Z (3 lenses + 2 refuters; brief work/port/review_prompt_lem-transport.md).

**def:uniform stated** (SM/UniformDefinition.lean, row `SM.uniform_definition :
UniformDefinitionData`): `CarrierUniform` (∃ τ ≠ 0, all turns of the corner polygon
`ccpCornerPolygon` equal τ), `CarrierMixed`, `UniformDecomposition`, `carrierRotation` (rotationNumber
of the corner polygon; lem:rot applicable by lem:carriers (ii) — clause `regular_carrier`),
`carrierLeftTurns` (leftTurns of the corner polygon), and m_Q = `carrierCrossingCount` (already in
CarrierCrossings). The corner-polygon reading follows the accepted lem:carriers row. Review launched
17:03Z (2 lenses + 1 refuter; brief work/port/review_prompt_def-uniform.md). Definitions are stated
for any S (not only decompositions); the brief asks the reviewers whether the wider domain is harmless.

**Next:** thm:root-indep-proof. A scout is producing work/reports/root-indep-plan-20260913.md
(exact statements of prop:A-chamber, thm:A-S3/S7/R3E, thm:A-soft, prop:A-reversal,
lem:star-generic; the telescoping argument along the transport path; gaps such as rotation
invariance of the tree coefficient). Provers follow the plan.

## lem:transport and def:uniform accepted — 2026-09-13 ~17:20Z (pod executor)

Both reviews clean (lem:transport: 3 lenses faithful, 2 refuters empty; def:uniform: 2 lenses
faithful, 1 refuter empty, who worked the bow-tie quadrilateral with S = {x} and S = ∅). Review
files reviews/lem-transport.json and reviews/def-uniform.json. Decisions recorded there and here:
lem:transport is stated with vertex count n + 1 (forced by `deleteVertex`'s type; nothing lost);
admissibility is not a hypothesis (derivable); the uniform-mesh affine clause is the same rendering
of "piecewise-affine" as the accepted thm:relgp row. def:uniform's definitions are stated for every
finite S (the source: decompositions); only `regular_carrier` needs IsDecomposition; the module
docstring was reworded to say so before acceptance (docstrings are not hashed).
Progress: claims verified 37/132 (28.0%), checklist 65/192. Checker re-running on the accepted map.

## Design decision: diagram / crossing-record / Laurent-ring layer for Chapter 3 — 2026-09-13 ~17:35Z (pod executor)

A judge panel (three independent proposers, three judges with the lenses fidelity / feasibility /
reuse; workflow launched ~16:00Z) has decided the representation question behind def:positive-lift,
def:gauss-record, the lp:*/rp:*/lc:*/mp:* block, def:adeg and the three literature interfaces
(lit:homfly, lp:lm, lp:lm-uniqueness). All three judges rank **Proposal #1 — polygonal oriented
link diagrams** first (totals 25/24/22 against 16/17/16 for the abstract-record Proposal #2; the
hybrid smooth-immersion Proposal #3 was not ranked by any judge). Decision adopted, with the
judges' grafts from #2. Full text: work/reports/design-decision-diagram-record-20260913.md (the
proposals, scores and syntheses), work/reports/design-panel-proposal1-sketch.lean.txt (the type
sketch, elaborated by the proposer against the pinned toolchain), and the raw panel output
work/reports/design-panel-diagram-record-20260913.json.

Core choices. (1) Diagram type: a `Shadow` is a finite family (`c ≥ 1` in the type) of closed
oriented generic polygons in the plane (`LabelledTuple k`, `k ≥ 3`), i.e. the SM's own PL class
(sm-3:337-341, lem:gauss-pl-model), with `Strand`, multi-component `IsCrossing`/`Crossing`/`Visit`
copying the accepted one-polygon notions; `Shadow.Generic` = regular components, no corner on a
non-incident edge, transverse pairwise meetings, no triple point; a `Diagram` adds an over-strand
choice at every crossing. Signs are det-based as printed (def:positive-lift). Positive lifts of
carriers are literal `Diagram` values over `Carrier.ccpCornerPolygon` (re-aim graft: reuse the
accepted ccpCornerCount / ccpCornerPolygon / CarrierUniform / carrierRotation / carrierLeftTurns /
carrierCrossingCount instead of the proposal's duplicates). (2) Crossing record: a combinatorial
`Record` (components, occurrence set M, successor, pairing involution, over bits, signs, with the
printed axioms) derived from a diagram (`Diagram.record`), never part of the diagram type;
`RecordIso` enters theorem statements only (so CV:ax:gausscode is never used to conclude link
equivalence); record-level operations (switch, smooth, restrict, join) first, with bridge theorems
to the diagram-level operations; agreement theorem with the accepted gaussList/visitTwin data for one
polygon; `IsRealizable` as a theorem-side predicate for mp:blocks / cb:products. (3) Ring layer:
`Laurent₂ K := AddMonoidAlgebra K (ℤ × ℤ)`, `R = Laurent₂ ℤ` for ℤ[a^{±1}, z^{±1}], a DISTINCT `def T`
for ℤ[l^{±1}, m^{±1}] (so l is never identified with a), the Gaussian detour `RG`, `TG` over
`GaussianInt` with the substitution ring homs φ, ψ via `AddMonoidAlgebra.lift`, `coeffAt` as Finsupp
evaluation, def:adeg via Mathlib `supDegree`/`infDegree` (graft). (4) Literature interfaces: single
`axiom` declarations in ∃-form with field-named Prop structures for the printed clauses
(`HomflyClauses`, `LMClauses`, `LMCompetitor`; graft), `homfly`/`lmF := Classical.choose`,
uniqueness relative to the chosen witness; planar isotopy = EqvGen(Reparam ∨ Deform) in the PL class,
Reidemeister moves as counting-characterised local replacements, skein triples with D₋ = D₊.switch x
(the reading of LM's theorem, SOURCES/audit/L-1_EXIT/work/lm1987.txt pp. 112-113) — each of these
readings must be accompanied by the sanity lemmas the proposal lists (crossing-count deltas,
reversal/mirror transport, one concrete instance per move, `lit_homfly_descent_redundant`) before
the axiom rows are accepted. Fidelity risks 1-5 of the proposal are recorded in the decision file and
will be re-read at each affected row.

Effort (proposer's estimate, one prover lane each): ring layer 500-700 lines; Shadow/Diagram core
600-900; moves/isotopy/skein 700-1000; records 500-700; the ε-smoothing construction and its record
bridge (gate for lp:core, rp:record-polynomial, mp:stack, cb:products) 1200-1800; positive lift
250-350. Plan: implement in that order as compiling drafts, state the definition rows
(def:positive-lift, def:gauss-record, def:adeg, def:C) on top, review, accept; the interfaces come
last, each reviewed against blueprint/AXIOM_REGISTRY.md.

## thm:root-indep-proof proved and stated; cor:A-lawful statement fixed — 2026-09-13 ~17:45Z (pod executor)

**thm:root-indep-proof.** A scout subagent produced work/reports/root-indep-plan-20260913.md — the
exact library statements of every ingredient (prop:A-chamber, thm:A-S3/S7/R3E, thm:A-soft,
prop:A-reversal, lem:star-generic, lem:A-small-values, lem:transport, the anchors) and, beyond the
plan, a complete ~500-line proof (Appendix A) conditional on the conclusion of lem:transport. Design
of the proof: Δ_gh(Q) := A_g(Q) − A_h(Q) on generic tuples (junk value 0 elsewhere) is eventually
constant at every generic parameter of a continuous family (chi is eventually constant by
continuity of the area determinants; `treeCoefficient_eq_of_chi`), has zero jump at each F/V/T/E/C
wall of the transport path (flat: thm:A-S3 for g and h with the same sides, the deletion generic by
the transport conjunct, IH at arity n−1; vertex–edge: thm:A-S7, halves generic and of smaller
arity, IH; T/E/C: thm:A-R3E), hence is constant along the whole path by a locally-constant-off-a-
finite-set lemma on the preconnected unit interval (Mathlib `IsLocallyConstant`); targets: a zero
anchor whose soft edge avoids g and h (new lemma: `softOldIndex j j` is injective in j; ε below the
lem:soft-rotation and thm:A-soft bounds) has A_g = A_h = 0 in the mixed sector; K_r via a new
rotation-invariance lemma (`det`/`chi`/`treeCoefficient` invariant under `rotationMap`, which the
library lacked) with lem:star-generic (i) and prop:A-reversal (i); K_{−r} via prop:A-reversal (ii)
and the bijection h ↦ 1 − h; K_0 via lem:A-small-values (ii). Strong induction on n wraps it
(`Nat.strong_induction_on`; case split by `anchor_cases_exhaustive`). A second subagent made the
theorem unconditional on the accepted `transport_lemma` (the `TransportConclusion` wrapper was
dropped; the [NeZero n] "gap" was moot). Ported verbatim as SM/RootIndependence.lean (helpers all
prefixed `ri_`); row `SM.root_independence (n) [NeZero n] (hn : 3 ≤ n) (P) (hP : Generic P) (g h) :
treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn`. Review launched ~17:40Z (3 lenses + 2
refuters; brief work/port/review_prompt_thm-root-indep-proof.md). The independent
finite-exception lemma proved by two provers (work/drafts/FiniteExceptionsA/B.lean:
`constant_of_finite_exceptions`) turned out unnecessary (the scout's route uses Mathlib's
IsLocallyConstant) and is kept in drafts, unported.

**cor:A-lawful** statement fixed in work/drafts/ALawful_statement.lean (compiles): `amplitude P hP hn
:= treeCoefficient P hP 0 hn` (the main text's A_n, rooted at the last edge) and the bundle
`ALawfulData` with fields root_independent, shift_invariant, descends (∃ A' on GenericPolygon n),
chamber_constant (labelled and cyclic chambers), silent (E and C walls), flat_law (deletion
generic; A(P_right) − A(P_left) = A(deletion)), cusp_law (per induced root deletionRoot j g, and
with A(deletion) when the deletion is generic — the printed "when the deletion satisfies (G1)"
only guarantees the per-root form, since A of a merely-(G1) tuple need not be root-independent),
vertex_edge_law (halves generic; s·A(λ₁)A(λ₂)), triple_law, soft_theorem (every sector, via
softAmplitudeMultiplier), reversal_law, triangles (A(star 1) = −1, A(starNeg 1) = +1). Two provers
launched ~17:45Z on the fixed statement.

**Chapter 3 layer.** Three implementers launched ~17:35Z on the adopted design (ring layer,
polygonal diagrams, crossing records) as compiling drafts.

## thm:root-indep-proof accepted — 2026-09-13 ~17:45Z (pod executor)

Review clean: three lens reviewers faithful with no discrepancies, two refuters empty-handed (the
only difference found: the Lean includes the trivial case g = h). Review file
reviews/thm-root-indep-proof.json. Progress: claims verified 38/132 (28.8%), checklist 66/192.
Checker re-running on the accepted map. Next in the chain: cor:A-lawful (two provers on the fixed
statement), then thm:uniqueness (statement to be fixed on top of `amplitude`; the proof repeats the
transport argument for Δ = F − A with the hypotheses (a)–(f); the anchor step needs the abstract
form of prop:anchor-values, to be proved as a helper — the prop:anchor-values ROW itself contains
the sentence "The function C satisfies these hypotheses", which needs prop:C-chamber and thm:C-soft
from Chapter 4, so that row waits).

## cor:A-lawful proved and stated; thm:uniqueness statement fixed — 2026-09-13 ~17:50Z (pod executor)

**cor:A-lawful.** Two provers produced sorry-free proofs of the fixed bundle; attempt A (269 lines)
ported as SM/ALawful.lean (row `SM.A_lawful : ALawfulData`, with `amplitude P hP hn :=
treeCoefficient P hP 0 hn`); attempt B kept in work/drafts as a cross-check. Proof: every field is
the corresponding accepted law row at root 0 plus `root_independence` to move roots (the deletion
and the halves are generic by lem:children; the soft field uses the return edge
`softParentEdge j j ≠ softOldIndex j j` as the evaluation root); `descends` is `Quotient.lift` on
`GenericPolygon n` with shift invariance as compatibility. Checker: mapped 67, audited 7815, passed.
Review launched ~17:48Z (3 lenses + 2 refuters; brief work/port/review_prompt_cor-A-lawful.md).

**thm:uniqueness** statement fixed in work/drafts/Uniqueness_statement.lean (compiles): `F : ∀ (n : ℕ)
[NeZero n], GenericPolygon n → ℤ` — literally a function on the space of generic polygons, so
"function on polygons" needs no shift-invariance hypothesis; a generic labelled tuple presents
`polygonProjection ⟨P, hP⟩`. Hypotheses as a Prop structure `UniquenessHypotheses F` with one field
per printed clause: (a) `chamber` (constant on chambers of the polygon space) and `silent`
(ExtensionAt, PureCutAt), (b) `flat` (sides by the turn at j as in thm:A-S3; the deletion with an
arbitrary genericity witness — the source's deletion is generic by lem:children, so quantifying over
the witness neither weakens nor strengthens), (c) `vertex_edge` (VertexEdgeAt covers both branches;
s = contactSign; halves with genericity witnesses), (d) `triple`, (e) `soft` (∃ δ > 0, ∀ ε < δ, ∀
genericity witness of P_ε, the identity in ℚ with softAmplitudeMultiplier), (f) `triangles` on
`star 1`, `starNeg 1`. Conclusion `F n (polygonProjection ⟨P, hP⟩) = amplitude P hP.1 hn` for n ≥ 3.
Two provers launched ~17:50Z; the proof is the transport argument for Δ = F − A (template:
SM/RootIndependence.lean), with the abstract anchor-values argument (prop:anchor-values, sm-5:461)
as a helper for zero and loop anchors. The prop:anchor-values ROW waits for Chapter 4 ("The function
C satisfies these hypotheses").

## cor:A-lawful accepted; thm:uniqueness proved and stated — 2026-09-13 ~18:10Z (pod executor)

**cor:A-lawful accepted** (row `SM.A_lawful`, hash 40bad437…): three lens reviewers faithful with no
discrepancies, two refuters empty-handed; readings endorsed (amplitude at root 0 = the main text's
A_n; the per-induced-root cusp law for a (G1)-only deletion; the generic deletion/halves as extra
information; soft theorem without sector hypothesis). Reviewer notes without action: the flat field
relies on the accepted def:walls row for the existence of both named sides; soft_theorem omits
thm:A-soft's ε₁ ≤ ε₀ clause (not part of the corollary). Progress: claims verified 39/132 (29.5%),
checklist 67/192.

**thm:uniqueness proved.** Two provers succeeded on the fixed statement. Attempt A (458 lines)
ported verbatim as SM/Uniqueness.lean (row `SM.uniqueness`); attempt B (543 lines, a symmetric
formulation: any two functions satisfying (a)–(f) agree, then A packaged as such a function via
`alA_polygonAmplitude`) kept as a cross-check. Proof design (A): Δ(P) := F(polygon of P) − amplitude P
on generic tuples; eventual constancy at generic points from openness of labelled chambers
(`genericTuple_locallyPathConnected`, `isOpen_Generic`, `projection_labelledChamber_eq_chamber`) and
hypothesis (a) plus `ri_treeCoefficient_eventually_eq_of_generic`; zero jumps at F/V/T/E/C walls from
(b)/(c)/(d)/(a)-silent against the cor:A-lawful fields and the induction hypothesis; constancy along
the lem:transport path by the generic lemma `ri_eq_of_locallyConstant_off_finite`; shift invariance
absorbs the (4,0) shift; the anchor step is the abstract prop:anchor-values argument
(`unA_softAnchor_delta`: for any SoftAnchorData, (Δ(P_ε) : ℚ) = softAmplitudeMultiplier · Δ(parent),
via bound_spec's chamber clause, (a) and (e) at a smaller parameter), giving 0 at zero anchors and
τ_j·Δ(parent) = 0 at loop anchors by the induction hypothesis; base n = 3 by transport to star 1 /
starNeg 1 and (f). Review launched ~18:08Z (3 lenses + 2 refuters; brief
work/port/review_prompt_thm-uniqueness.md). With thm:uniqueness the sm-5/sm-6 transport–comparison
chain is complete except prop:anchor-values (its C sentence, Chapter 4), thm:comparison and
cor:C-inherits (Chapter 4).

## Chapter-3 representation layer, phase 1 ported — 2026-09-13 ~18:15Z (pod executor)

The three implementers finished (all sorry-free, standard axioms, every declaration in `SM.Link`):
work/drafts/LinkLaurentRing.lean (1538 lines: Laurent₂, R, distinct T with CommRing/IsDomain, RG/TG,
generator units, coeffAt, zRow, def:adeg degrees via supDegree/infDegree with integer forms
degAZ/mindegAZ/degZZ/mindegZZ and their specs, multiplicativity of degrees by a lexicographic
extreme-monomial argument (Mathlib's supDegree_mul is unusable: it needs AddLeftStrictMono (WithBot ℤ)),
InSupportM, R.toRG injective, re/im splitting over ℤ[i], substHom, φ ∘ ψ = id and ψ ∘ φ = id
(phiEquiv), the ℚ(a) specialisation), LinkDiagram.lean (1764 lines: PolyComp, Shadow, Strand,
IsCrossing/Crossing/Visit, crossingPoint, Shadow.Generic, Diagram, sign/writhe, switch, and one
StrandMap/pullback construction giving restrict/reverse/mirror with their sign laws; Basing, basedRank,
UnderFirst; one-component comparison with the accepted SM.Crossing/SM.Visit partly proved),
LinkRecord.lean (1633 lines: Record with explicit Fintype/DecidableEq fields, RecordIso, Record.Crossing,
writhe, switch, smooth via first return of the reconnected successor with emptied circles kept as
components, restrict, joinRecord on marked circles). Deviations from the sketch and open items are
recorded in the workflow output (work/reports: see the phase-1 result) — notably: smoothing's
component count (c ± 1) not yet proved; RecordIso transport only for switch; Diagram-level
involutivity of reverse/mirror not proved; visitPt vs the accepted visitPosition agreement not
proved. Ported verbatim into work/lean/SM/{LinkLaurentRing,LinkDiagram,LinkRecord}.lean (headers
added, #print lines removed) and built. No row points at them yet; def:adeg is the first row to be
stated on the ring layer, then def:gauss-record (needs the Diagram.record bridge, phase 2) and
def:positive-lift (needs the positive lift of carriers, phase 2).

## thm:uniqueness accepted; def:adeg stated — 2026-09-13 ~18:30Z (pod executor)

**thm:uniqueness accepted** (row `SM.uniqueness`, hash 9b3e29a9…): three lens reviewers faithful with
no discrepancies, two refuters empty-handed; review file reviews/thm-uniqueness.json. Readings
endorsed: F as a function on `GenericPolygon n` (the cyclic orbit space), unconstrained below arity 3;
genericity witnesses as binders in (b), (c), (e); the soft identity in ℚ; amplitude = A_n. With this,
Theorem 1 of the main text is formalized: every integer-valued chamber function on generic polygons
obeying the flat, vertex–edge, triple and soft laws with the two triangle values equals the tree
coefficient. The sm-5/sm-6 chain now lacks only prop:anchor-values (its C sentence), thm:comparison
and cor:C-inherits (Chapter 4). `write_review_and_accept.py` was patched to skip reviewer file
entries that are not paths (a reviewer had listed "definition lines only (grep) …" as a file name).

**def:adeg stated** (SM/AdegDefinition.lean, row `SM.adeg_definition : AdegDefinitionData`) on the
ring layer: R = ℤ[a^{±1}, z^{±1}] is an integral domain; (d, k) ↦ a^d z^k via the units; coeffAt is
the coefficient of a^d z^k (pinned on monomials and separating); for f ≠ 0 the a-degree and
a-mindegree are the integers degAZ/mindegAZ, attained, bounding, unique; likewise for z. Nothing is
asserted at f = 0 (the source defines nothing there). Review launched ~18:25Z (2 lenses + 1 refuter).

## def:adeg accepted — 2026-09-13 ~18:35Z (pod executor)

First row on the Chapter-3 representation layer. Two lens reviewers faithful, one refuter empty;
the one recorded "discrepancy" is a self-declared strengthening (IsDomain for the whole ring
ℤ[a^{±1}, z^{±1}] where the source names the coefficient ring ℤ[z^{±1}] an integral domain; no
separate subring term exists under the adopted reading). Review file reviews/def-adeg.json.
Progress: checklist 69/192 (definitions do not count as claims; claims verified 40/132).

## CV lane: scout plan and the domain decision (F2) — 2026-09-13 ~18:55Z (pod executor)

The CV-lane scout finished work/reports/cv-lane-plan-20260913.md (1570 lines; a type-level skeleton of
the CV definitions compiled against the library). Its start-now list (accepted SM library only):
CV:def:polygon, def:regular, def:guarded, def:generic, def:diagrammatic, def:interlace, def:event,
lem:guardconst, def:silent, Bridge:B1–B3, prop:chamberinv(i), def:rot, lem:turnlift, lem:uniformrot,
and the X₁-free cores of the R:* rows. Blocked by the diagram/record layer: def:record's last clause,
def:homfly, def:piecediagram, lem:piececurve, def:X1, chamberinv(ii), lem:silence, the carrier-floor
chain, pieceintrinsic, cor:groupedknot, lem:fulltwist, Bridge:B4, most R:* rows. Blocked by the
interfaces: CV:ax:homfly, CV:ax:gausscode, lem:homflyrows, rounding/curl/carrierfloor, ax:etnyre,
ax:slbound, singleton_D_i.

**Decision F2 (genericity domains).** CV's genericity ("guarded", constraining only vertex triples that
contain a cyclically consecutive pair) is strictly weaker than SM's all-triple genericity (witness at
sm-1:548–560). The scout suggested stating carrier-dependent CV rows on the SM locus with a
"documented narrowing". Decision: NO narrowing for any row. CV definition rows are stated on CV's own
guarded locus exactly as printed (`CV.Generic`, with the theorem `SM.Generic → CV.Generic` = Bridge
B1(1)); CV lemma rows whose printed statements quantify over CV-generic polygons but whose proofs rest
on the Carrier lane (bound to `SM.Generic`) are deferred until either the Carrier lane is
re-parametrized to the geometric API (`CrossingGeometry`, Gap G1, estimated 2–3 weeks) or an explicit
domain-transfer lemma is proved; the final assembly (Bridge:theorem, SM:corner_laws_and_soft) needs
only the SM domain, so this ordering costs nothing there. A row is never accepted on a domain
smaller than printed.

**Phase-1 extras ported**: SM/LinkRecordExtras.lean (smoothing component count c ± 1, RecordIso
transport for smooth/restrict/join, switchAt/smoothAt, kink and Hopf examples) and
SM/LinkDiagramExtras.lean (involutivity of reverse/mirror, agreement of visitPt with the accepted
visitPosition and of Shadow.other with visitTwin, positivity lemmas), both from sorry-free drafts.
CV implementers launched on the start-now definition rows (modules under work/lean/CV/ after porting).

## Chapter-3 layer, phase 2 delivered and ported — 2026-09-13 ~19:30Z (pod executor)

Three implementers finished (all sorry-free, standard axioms): work/drafts/LinkDiagramRecord.lean
(1488 lines: `Diagram.record` as an `abbrev` — per-component cyclic successor of visits via the
lifted gaussList pattern, twin pairing, over bits, signs; record_writhe = writhe, record_crossingCount;
`switchRecordIso`, `restrictRecordIso` (both bridges proved); `IsRealizable`; `record_of_single_polygon`
(agreement with the accepted nextGaussVisit / visitTwin / crossingSign data); the cyclic-order
equivalence of def:gauss-record proved in both directions; the PL-extension clause
`recordIso_extend_statement` STATED as a Prop only — open item, 300–500 lines), LinkMoves.lean (3348
lines: OutsideMatch with an explicit outer-crossing bijection, IsDisc = convex compact with nonempty
interior (rectangles qualify), Clean frames, Reparam, Deform (constructive, over data kept),
PlanarIsotopic, RI/RII/RIII as symmetric closures of one-directional site data with Δcrossings = ±1/±2/0
and components fixed, IsOrientedSmoothing / SmoothingRecordClause parameterised by a record map,
IsSkeinTriple, LinkEquiv, IsSplitCircleAddition, IsMarkedInterval; reversal transport proved for all;
no concrete kernel-checked move instance yet — open item), LinkPositiveLift.lean (846 lines:
`carrierShadow hn hP S q hS`, `carrierShadow_generic` (tail_off, transversality, no triple point from
the accepted CarrierSelfIntersections lemmas), `positiveLift`, `positiveLift_isPositive`,
`positiveLift_writhe`, `carrierCrossingEquiv`, `positiveLift_writhe_eq_carrierCrossingCount` = "Its
writhe is m_Q"). Decisions recorded from the implementers (reviewers of the affected rows will see
them in the docstrings): the direction clause of OutsideMatch is restricted to points strictly
outside U with an added arriving-direction clause; moves carry an explicit component bijection;
`carrierShadow` needs `hS : IsDecomposition` (the ≥ 3 corners bound is lem:carriers (ii)). All three
ported verbatim into work/lean/SM/. Next rows: def:positive-lift (on positiveLift) and def:gauss-record
(on Diagram.record / RecordIso; the extension clause's proof is an open item to be closed before that
row can be accepted if the printed definition includes it as content).

## def:positive-lift stated — 2026-09-13 ~19:35Z (pod executor)

Row `SM.positive_lift_definition : PositiveLiftDefinitionData` (SM/PositiveLiftDefinition.lean) on the
Chapter-3 layer: an oriented link diagram is a `Link.Diagram` (c ≥ 1 regular polygonal components,
crossings = non-adjacent meeting strands, transverse, no triple point, over strand at each crossing);
positive ↔ det(u_o, u_u) > 0, sign = sgn det (never zero; −1 = "negative otherwise"); writhe = Σ sign;
the positive lift of a carrier `q` of a decomposition `S` (`positiveLift hn hP S q hS`) has one
component, the corner polygon of the carrier (the accepted reading of lem:carriers (ii) and
def:uniform), its crossings correspond bijectively to `carrierCrossings` with equal crossing points,
every crossing is positive, and its writhe is `carrierCrossingCount = m_Q`. The polygonal class is
this document's own ("A diagram here is a finite polygonal immersion", sm-3:337-341); the brief asks
the reviewers to judge that reading and the `IsDecomposition` hypothesis. Review launched ~19:35Z
(3 lenses + 2 refuters).

## CV definition rows stated; record extension proved — 2026-09-13 ~19:55Z (pod executor)

**CV lane.** The implementers delivered work/drafts/CV_Setup.lean (1727 lines: CV:def:polygon,
def:regular, def:guarded (the guarded list as the indexed type `Member` with the printed index side
conditions, d8a identities, continuity), def:generic (`CV.Generic`, generic locus, chambers as
connected components; theorems `SM.Generic → CV.Generic` = Bridge B1(1), `CV.Generic →
CrossingGeometry`, `CV.Regular ↔ SM.Regular`), def:diagrammatic (stated literally on the traversal
circle: self-intersections = points with exactly two preimages, transverse, none a corner, vertex
clause; equivalent to `CrossingGeometry ∧ vertex clause` for n ≥ 3), each with a bundle
`CV.<Row>Data` and theorem `CV.<row>_definition`) and CV_Events.lean (912 lines: CV:def:interlace on
the accepted geometric interlacement graph, CV:def:event with the added field `center_polygon`
(the printed "path of polygons" makes the centre a CV polygon; not implied by the other fields),
CV:lem:guardconst, CV:def:silent) — the latter with `Ev`-prefixed duplicates of the guarded list that
a subagent is now unifying with CV.Setup. CV_Setup ported verbatim as work/lean/CV/Setup.lean (built);
rows CV:def:polygon/regular/guarded/generic/diagrammatic mapped to `CV.<row>_definition` in `CV.Setup`;
reviewer input work/reviews/cv-setup-reviewer-input-statement.lean.txt (the module with the five
row proofs replaced by sorry), source excerpts cv-def-<row>-source-excerpt-*.tex.txt, one brief
work/port/review_prompt_cv-setup.md for all five (the workflow names the row). Review to be launched
per row (2 lenses + 1 refuter each; def:guarded 3 + 2).

**def:gauss-record.** Two provers proved `recordIso_extend_statement` (the PL-extension clause) as
packaged in LinkDiagramRecord — both remark that the predicate `ExtendsToCircleMaps` does not say
"piecewise-linear / positive affine between successive marks" although their witness is exactly that
map. Decision: strengthen before stating the row — a third prover is adding the predicate
`ExtendsPiecewiseAffine` (offset from a mark scales linearly along each arc between successive marks;
linear rescaling on a mark-free circle) and its proof on top of draft B; the row
`gauss_record_definition` (draft work/drafts/GaussRecord_statement.lean, compiles with the
extension field pending) will use it.

## def:positive-lift: first review round not faithful; row revised — 2026-09-13 ~20:05Z (pod executor)

Three lens reviewers returned "not faithful" (both refuters found nothing). Their points and the
decisions taken:
1. The bundle's `diagram` field only listed properties every `Diagram` has (no converse, and the
   type clause `tail_off` — no vertex on a non-incident edge — was not surfaced). FIXED: the field
   now characterises the type (eta; every generic shadow with an over-strand choice is a diagram;
   `Shadow.Generic` ↔ its four printed clauses including `tail_off`; `IsCrossing` ↔ the pair
   description; the crossing is `{over, under}`).
2. "THE oriented knot diagram": no uniqueness clause. FIXED: field `lift_unique`
   (`eq_positiveLift_of_isPositive`).
3. The class is polygonal only; the bridge paragraph (sm-3:337-343) also allows "a regular smooth
   immersion with finitely many transverse double points and possible finitely many corners away
   from crossings". DECISION (recorded, not fixed by code): the formal class is the document's
   polygonal class. The document itself reduces the smooth case to finite PL models
   (lem:gauss-pl-model, sm-3:371-427 — not a selected row of this focused stage), and every diagram
   used by the selected rows (positive lifts of carriers, diagrams of polygons, the lp/rp/lc/mp
   blocks on such diagrams) is polygonal. Formalizing regular smooth immersions with corners would be
   a separate development with no consumer in the selected chain. The row docstring states the scope;
   the second-round brief lets the reviewers read the bridge paragraph, lem:gauss-pl-model and the
   selection, and asks them to judge the polygonal reading as this document's class. If the second
   round still returns "not faithful" on this point alone, the row stays unaccepted with this note
   (an incomplete stage is reported as incomplete).
4. `c ≥ 1` in the type is not in def:positive-lift's first sentence. DECISION: keep; it is the
   document's convention for its diagrams ("Here c ≥ 1", lp:lm sm-3:951; "Algebraic empty products
   are not empty links", sm-3:933); recorded as field `components` with the citation; the brief now
   allows reading sm-3:929-960.
5. Labelled representatives (base vertex, component order) versus the printed unlabelled diagram:
   permitted by the formalization remark sm-1:56-62; recorded in the docstring; no invariance clause
   is added to this definition row (crossings, signs and writhe are label-independent by
   construction; a relabelling-invariance lemma can be added when a consumer needs it).
6. `tail_off` also excludes a double point at a straight-through (zero-turn) subdivision vertex,
   which the printed class arguably permits; edge case with no consumer (carrier corners have
   nonzero turns); recorded in the docstring.

## CV.Events ported and stated; CV rows under review — 2026-09-13 ~20:00Z (pod executor)

The unification subagent replaced the `Ev`-prefixed duplicates of CV_Events.lean by the CV.Setup
declarations (no semantic change in the bundles; one supplement lemma `G2_eq_zero_iff`); the result
compiled and was ported verbatim as work/lean/CV/Events.lean (built). Rows mapped:
CV:def:interlace → `CV.interlace_definition : InterlaceData hP` (stated for a polygon with the
accepted `CrossingGeometry`, which `Diagrammatic` implies — the brief asks the reviewers whether the
wider domain is harmless), CV:def:event → `CV.event_definition : EventData E` (the structure
`CV.Event` carries the field `center_polygon`, a fidelity addition relative to the plan's skeleton:
the printed "path of polygons" makes the centre a CV polygon), CV:lem:guardconst → `CV.guardconst`,
CV:def:silent → `CV.silent_definition : SilentData E`. Reviewer input
work/reviews/cv-events-reviewer-input-statement.lean.txt (module with the four row proofs replaced
by sorry), excerpts cv-{interlace,event,guardconst,silent}-source-excerpt-*.tex.txt, brief
work/port/review_prompt_cv-events.md. Reviews launched ~19:58Z for the four Events rows
(2+1 / 3+2 / 2+1 / 2+1) and ~19:52Z for the five Setup rows (2+1 each, def:guarded 3+2).
Second-round review of def:positive-lift launched ~19:56Z.

## def:gauss-record stated on the strengthened extension — 2026-09-13 ~20:05Z (pod executor)

The third prover added `RecordIso.ExtendsPiecewiseAffine` (orientation-preserving bijections of the
parametrizing circles extending Φ that are, in oriented key coordinates, the positive affine map on
each arc from an occurrence to its successor — forward distance `Diagram.cyclicOffset` from the
mark scaled by the ratio of the arc lengths `rexPL_arcLen`, the single-mark arc being the whole
circle — and the linear rescaling k'/k on an occurrence-free circle) and proved it
(`rexB_recordIso_extend_pl`); ported verbatim as SM/LinkRecordExtension.lean (draft A kept as a
cross-check). Row `SM.gauss_record_definition : GaussRecordDefinitionData`
(SM/GaussRecordDefinition.lean): occurrences, successor (no occurrence strictly between), pairing,
bits, signs (sgn det(u_O, u_U), stored on both occurrences, nonzero), the named record isomorphism
clauses, cyclic-order preservation (`RecordIso.visitBetween_iff`), and the extension clause with
`ExtendsPiecewiseAffine`. Readings the brief asks the reviewers to judge: the many-circles
generalisation of the printed one-circle statement; sphere versus plane; the extra circle bijection
`e` of RecordIso; "does not permit traversal reversal" via cyclic-order preservation; the Lean fixes
one positive parametrization (the linear rescaling) where the source says "choose any". Review
launched ~20:05Z (3 lenses + 2 refuters).

## Five CV definition rows, CV:lem:guardconst and def:positive-lift accepted — 2026-09-13 ~20:25Z (pod executor)

CV:def:polygon, def:regular, def:guarded, def:generic, def:diagrammatic (module CV.Setup) and
CV:lem:guardconst (CV.Events): every reviewer faithful, every refuter empty. Discrepancy entries
were documentation-only (docstring line citations drift by 1–13 lines from the frozen d1_setup.tex —
a docstring pass is scheduled), companion identities attributed to d8a_dictionary.tex (outside the
brief), or non-defining prose/non-examples not rendered as fields. Review files
reviews/cv-def-*.json, reviews/cv-lem-guardconst.json.

CV:def:interlace, CV:def:event, CV:def:silent: mixed verdicts (one "not faithful" each), all on scope
and completeness of the bundles, none on the encodings: interlace — `CV.U`/`mem_U` and the
SM-agreement field go beyond the printed row, and the vertex set "[m]" (the double points) is not
identified with `SM.Crossing P` on the diagrammatic domain; event — the printed tangency example
(sm d1_setup.tex 1088-1096) is not formalized (terminology sentences and a forward reference to
conv:events are non-defining); silent — the ax:R fields `isSimpleRIII_iff` and `silent_not_simpleRIII`
belong to CV:ax:R, not to def:silent. Actions: SilentData trimmed by the executor (the RIII bundle
stays in the module for the ax:R rows) and the def:event citation ranges fixed to 1072–1097 (module
recompiled); a prover is revising InterlaceData (drop `mem_U` and the U clause, move the SM agreement
to a standalone theorem, add the vertex identification Crossing P ≃ selfIntersections under
Diagrammatic) and adding the tangency example (`CV.tangencyExample : Event 4`) with its printed
claims as fields of EventData. Second reviews follow.

def:positive-lift accepted on the second round (3 faithful, 2 refuters empty; readings (i)–(iv)
classified as supported); reviewer caveat recorded: the rounding/front/contact rows
(ce:rounding, cf:lem-rounding, fd:*) must be checked against the polygonal scope when reached.
Progress: claims verified 41/132 (31.1%), checklist 76/192.

**Interfaces.** work/drafts/LinkInterfaces.lean (implementer): `axiom SM.lit_homfly : ∃ H : Diagram → R,
HomflyClauses H`, `axiom SM.lp_lm : ∃ F : Diagram → T, LMClauses F`, `axiom SM.lp_lm_uniqueness : ∀ Q,
LMCompetitor Q → Q = lmF`, with `homfly`/`lmF := Classical.choose`, and the sanity theorems
`lit_homfly_descent_redundant` / `homflyClauses_iff_printed` (the descent clause follows from the
other clauses, so the axiom is not stronger than printed), `LMClauses.competitor`,
`eq_lmF_of_lmClauses` (any lp:lm witness equals lmF), `lmF_unknot`. Ported as SM/LinkInterfaces.lean
(built; the only non-standard axioms are the three policy names); rows lit:homfly, lp:lm,
lp:lm-uniqueness mapped; review against blueprint/AXIOM_REGISTRY.md to follow.

## def:gauss-record accepted; duplicate declarations fixed — 2026-09-13 ~20:35Z (pod executor)

def:gauss-record accepted (3 faithful, 2 refuters empty; all discrepancy entries non-blocking, see
reviews/def-gauss-record.json). Checklist 77/192 (claims verified 41/132).

Checker incident: the first checker run after mapping the interface rows failed at the joint import
step — `SM.Link.Diagram.switch_visitPt` (LinkDiagramRecord and LinkMoves) and
`mirror_overStrand`/`mirror_underStrand` (LinkDiagramExtras and LinkMoves) were declared twice by
implementers working in parallel; each module built on its own but not together. Fixed by renaming
the three LinkMoves copies with the suffix `_mv` (no other module used them); LinkMoves and
LinkInterfaces rebuilt; a joint import of every Chapter-3, interface and CV module now succeeds and
the checker passes (mapped 83, audited 11116). Lesson recorded: after porting parallel drafts, run a
joint-import test (/tmp/t_all.lean pattern) before the checker.

## The three literature interfaces accepted — 2026-09-13 ~20:55Z (pod executor)

lit:homfly, lp:lm, lp:lm-uniqueness (SM/LinkInterfaces.lean, policy axioms `SM.lit_homfly`,
`SM.lp_lm`, `SM.lp_lm_uniqueness`) accepted after an independent review against the registry
text (3+2+2 lens reviewers, all faithful; 2+1+1 adversarial refuters, none refuted; see
reviews/{lit-homfly,lp-lm,lp-lm-uniqueness}.json). Readings recorded (all adopted earlier in
work/reports/design-decision-diagram-record-20260913.md): polygonal diagram domain (def:positive-lift
reading); "the crossing-free circle" = every one-component crossing-free polygonal diagram (D10;
PL Schoenflies used mathematically, not in Lean); skein triples = switch-and-smooth triples (D3, LM
pp. 112-113) — for lp:lm-uniqueness a narrower competitor hypothesis is formally a stronger axiom,
no effect in this frame; planar isotopy = EqvGen(Reparam ∨ Deform); descent over LinkEquiv
(redundant, `lit_homfly_descent_redundant`).

Documentation defects to fix at the next rebuild of the layer (no content effect): (a)
LinkLaurentRing.lean:80-81 and LinkInterfaces.lean:55-60 claim the elaborator never confuses `T`
with `R`; `T` is a plain `def`, so `T = R` is `rfl` at default transparency — the separation is a
policy enforced by review (distinct names and generators; only the documented bridges convert),
and the docstrings will say so; (b) LinkInterfaces.lean:180-181 "The source function itself is the
witness fixed by lmF" overstates — the identification is via lp_lm_uniqueness only; (c) header
field-name drift ("skein" vs `sourceSkein`). Checklist now 80/192.

Decision on lem:gauss-two-discs (claims.py #57, next in document order): it is the constructive
polygonal Jordan–Schoenflies theorem on the sphere with positive PL disc extensions (sm-3:428-542).
Mathlib has no Jordan curve theorem; a faithful formalization is a multi-week topological
development (finite triangulations, F₂ chains, collapses). It is cited only by lem:gauss-sphere-isotopy
and lem:gauss-pl-model (not claims of the 132) and by line 4767. Under AUTONOMOUS_EXECUTION.md the
work continues on every independent claim: lem:gauss-two-discs is DEFERRED behind the algebraic and
combinatorial Chapter-3 rows (lp/rp/lc/mp blocks on the accepted interfaces, def:C) and the
carrier/CV lanes; it stays `pending`, never `implemented` without a proof. A dedicated lane will be
opened for it once the smoothing-existence lane (the gate for lp:core / rp:record-polynomial /
mp:stack; design panel started 20:50Z) is under way.

## lp:coefficient-transport proved; the local polynomial P defined — 2026-09-13 ~21:00Z (pod executor)

lp:coefficient-transport: statement fixed by the executor (work/drafts/CoefficientTransport_statement.lean:
Prop bundle `RCompetitor` = HomflyClauses without the descent field; theorem `SM.coefficient_transport :
RCompetitor Q → RCompetitor Q' → Q = Q'`), proved independently by two provers (drafts
CoefficientTransportA.lean 154 lines, B 142 lines; both follow the printed Gaussian transport: ψ∘toRG,
re/im split, lp_lm_uniqueness twice, φ∘ψ = id, injectivity of R → R_G). B ported verbatim to
SM/CoefficientTransport.lean; axioms: propext, Classical.choice, Quot.sound, SM.lp_lm,
SM.lp_lm_uniqueness (lit:homfly not used, as printed). Row mapped `implemented`; review launched (3+2).

Design decision — the local campaign polynomial P (lp:core, sm-3:1041-1063; consumed by
lc:single-crossing, lp:split-circle, lc:presentations, mp:*): `SM.P D := reMap (phi (T.toTG (lmF D)))`
(SM/LocalPolynomial.lean), the coefficientwise real part of the Gaussian evaluation φ(F_D). Rationale:
the printed P_D is "the evaluation of the same source construction in R" = φ(F_D), which lp:core proves
lies in R ⊂ R_G (integral descent). Taking the real part gives an element of R for every diagram
without presupposing the descent; lp:core's bundle will record `R.toRG (P D) = phi (T.toTG (lmF D))`
(imaginary part zero), so P D is exactly the element of R whose image is φ(F_D). Alternatives rejected:
P := homfly (then "P = H" would be a definition, not the printed theorem); P := Classical.choose of the
descent (needs lp:core's induction before P can be named, blocking lc:single-crossing).
lc:single-crossing statement fixed (work/drafts/SingleCrossing_statement.lean; "for either crossing
sign" = no hypothesis on the sign; "just one self crossing" = `∀ y, y = x`); two provers launched.

## CV:def:interlace, CV:def:event, CV:def:silent accepted (second round) — 2026-09-13 ~21:05Z (pod executor)

Revision (work/drafts/CV_Events_rev.lean → work/lean/CV/Events.lean): interlace — `mem_U` and
`generic_agree` removed from the bundle (standalone `CV.interlace_generic_agree` etc.), fields `vertices`
(crossingPoint : Crossing P ≃ selfIntersections P on diagrammatic polygons, 3 ≤ n) and `vertex_ncard`
added; event — the printed tangency example formalised (`tangencyPath`, `tangencyExample : Event 4`,
bundle `EventExampleData` as field `tangency_example`; explicit zero set {G1_1, G2_{0,2}, G2_{1,0}};
genericity for all t ≠ 0; even; same side chamber; not transversal; no CV crossing for any t; the SM
closed-segment `IsCrossing` at t = 0 through the shared vertex is documented); silent — the ax:R fields
removed. Second round: 3/3 faithful per row, refuters clean, all discrepancies non-blocking; docstring
citation fixes (303-313, 1265-1271, IsSimpleRIII marked outside the row) applied after the review,
module rebuilt. Executor dispositions recorded: the sentences "We say the event is guarded relative to Z",
"Every named event of the convention that lists them is required to be transversal" (conv:events) and
"A tangency is not a wall crossing" are non-definitional prose without a Lean counterpart; "changes sign
at t = 0" is `Event.SignChanges` (germ reading). Checklist 83/192.

## lp:coefficient-transport accepted; lc:single-crossing proved — 2026-09-13 ~21:20Z (pod executor)

lp:coefficient-transport (SM.coefficient_transport) accepted: 3 lens reviewers faithful, 2 refuters
clean, all notes non-blocking (D10 circle reading; field order). Claims verified 42/132.

lc:single-crossing: two independent proofs (work/drafts/SingleCrossingA.lean 147 lines, direct
construction of the basepoint on the under edge; SingleCrossingB.lean 187 lines, via the reusable
lemma `SM.Link.Diagram.exists_basing_first : ∀ v, ∃ B : D.Basing, every other visit on v's component
has a strictly larger based offset` with helpers `finite_crossing_params`, `exists_param_before`,
`basingAt`). Deviation from the port-the-shorter rule: B is ported (SM/SingleCrossing.lean) because
its general basing lemma is exactly what the (N, b) inductions of rp:record-polynomial / lp:core /
mp:join need ("choose the basepoint in the interval just preceding the first occurrence"); A kept as
the cross-check. Both use only SM.lp_lm among the interfaces. Row mapped `implemented`; review launched.

Statements fixed ahead of their proofs (drafts typecheck with sorry; all wait for the smoothing
gate except mp:zero-link, which is independent geometry): work/drafts/LpCore_statement.lean
(LpCoreData: gaussian, skein, underFirst_init, eq_homfly, unique, support, ne_zero, circle,
knot_support, planar, RI/II/III), Stack_statement.lean (blocks as a surjection blk : Fin c → Fin q,
BlockOrdered, blockRestrict; split_union corollary), SplitCircle_statement.lean, RecordPolynomial_
statement.lean (lmF_eq, subst_eq for every ring hom out of T, P_eq, coeff_eq), Presentations_statement
.lean (P D = P D′ from a RecordIso), ZeroLink_statement.lean (Shadow.MixedPair; fixed-order determinant
sum zero; half-sum of decorated signs integral; zero when one component is always over).

## CV chamberinv(i), Bridge B1/B2 delivered — 2026-09-13 ~21:22Z (pod executor)

CV:prop:chamberinv clause (i) (𝓤_n^CV open; chambers open and path connected) proved and ported
(work/lean/CV/ChamberInv.lean, 188 lines, standard axioms; fields `open_locus`, `chamber_open`,
`chamber_pathConnected : ∀ P, Generic P → IsPathConnected (chamber P)`; stated for every NeZero n with
`chamberinv_i_of_three_le` on the printed domain). Row 147 stays pending until clause (ii) (X₁
constant on chambers; blocked on CV:def:X1) — a row is accepted whole.

Bridge:B1 and Bridge:B2 (rows 179-180) proved by one implementer (work/drafts/Bridge_B1.lean, 439
lines, standard axioms) and ported to work/lean/Bridge/B1.lean (module `Bridge.B1`, both rows).
Shape decisions (recorded from the implementer, to be judged by the reviewers): the existential curve
identity of B1 is stated pointwise on the real parameter with both membership proofs (the two parameter
subtypes are only propositionally equal for a bound E; for the constructor `eventOfTriple` the identity
`curve = g.curve` is rfl); `eventOfTriple` takes `hn : 3 ≤ n`; B2 is stated for the increasing
representatives `rep e < rep f < rep k` (BRIDGE.md §0 naming), with `exists_sorted_tripleAt` showing
this is without loss. Rows mapped `implemented`; review launched (3+1 per row). B3 implementer launched.

## lc:single-crossing accepted — 2026-09-13 ~21:27Z (pod executor)

3 lens reviewers faithful, 2 refuters clean. Recorded non-blocking note (all three reviewers): at
primitives `P D = 1` says Re φ(F_D) = 1; the printed P_D = 1 also entails Im φ(F_D) = 0, which is
lp:core's integral descent (presupposed by the printed definition of P_D ∈ R). Disposition: keep the
definition `P := reMap ∘ φ ∘ toTG ∘ lmF` (AUTHOR_NOTES 21:00Z) and record the descent once, for every
diagram, as the field `gaussian : R.toRG (P D) = phi (T.toTG (lmF D))` of lp:core's bundle
(work/drafts/LpCore_statement.lean); no per-row imaginary-part clause. Claims verified 43/132.

## def:C and Bridge:B3 implemented — 2026-09-13 ~21:31Z (pod executor)

def:C: work/drafts/CornerStateSum.lean (implementer, 308 lines, axioms + lit_homfly) ported to
SM/CornerStateSum.lean; row mapped `implemented`, review launched (3+2). Rendering decisions to be
judged by the reviewers (from work/drafts/CornerStateSum_PLAN.md): r_Q is the accepted REAL
`carrierRotation`; the integer slot uses `carrierRotationInt := round carrierRotation` (hypothesis-free;
equals the rotation on decompositions by `rotationNumber_integer`), so `cornerSlot : ℤ` and the printed real
identity is a bundle field; `cornerCoefficient` carries the decomposition proof `hS` (the positive lift needs
it), and `cornerStateSum` sums over `(uniformDecompositions hn hP).attach` (Ind filtered by
UniformDecomposition), with a dite form over all of Ind as a theorem for lem:C-X1; ℓ(P) is the accepted
`leftTurns`. Statement of lem:C-X1 fixed on these definitions (work/drafts/CX1_statement.lean: carrierWeight,
wind, CX1Data with weight_right/left/mixed, wind_eq, selector_form; right turn = turn −1, left = 1).

Bridge:B3: work/drafts/Bridge_B3.lean (213 lines, standard axioms) ported to Bridge/B3.lean; `Bridge.B3`
(sorted representatives) and `Bridge.B3_unsorted`; SM's witness radius reused because activations are
constant on the whole germ interval (B2's `crosses_const`). Row mapped `implemented`, review to launch.

## CV def:rot (polygon part) and turnlift(ii) proved; rows 144/145 wait for F6 — 2026-09-13 ~21:36Z (pod executor)

work/drafts/CV_Rotation.lean (624 lines, standard axioms) ported to CV/Rotation.lean: the printed ε_i
formula (`epsRot`), admissible directions exist (`exists_admissible`, vectors (1, x)), `rotRay`, `rot`,
`rotAbs`, the printed 7-vertex counterexample (returns −1 and 0 for two rays on a non-regular polygon,
kernel-checked), and Gap G2 closed: `turnlift_ii : 2π · rotRay L r = Σ principalTurn L i` for every
regular polygon and admissible ray (hence independence of r and `rot = rotationNumber`), with the
consequences path constancy / flat subdivision / reversal / triangles from the accepted lem:rot.
Conventions: 0-based indices as printed (δ_i = edge L i); det(r, δ_i) > 0 ⇔ δ_i counterclockwise of r;
no `3 ≤ c` hypothesis on the consequences (`Regular.three_le`). NOT mapped: row 144 (CV:def:rot) also
prints "Direction loops and smooth curves" (tw(T) of a direction loop via a tangent-angle lift; rot(γ) of
a closed C¹ regular curve; R = |rot|), and row 145 has clauses (i),(iii) about those loops/curves. Per
decision F6 these are defined ONCE, in SM cf:def-turning (row 95, sm-3:3514), shared with cf:lem-turnlift
(row 96) and CV rows 144-145; a scout is mapping the Mathlib path-lifting API for that unit
(work/reports/turning-number-scout-20260913.md). Rows 144/145 will be mapped when the shared
definitions exist; the polygon part stays in the library meanwhile.

## Bridge:B1 and Bridge:B2 accepted — 2026-09-13 ~21:38Z (pod executor)

Both rows 3/3 faithful, refuters clean, all notes non-blocking (recorded in reviews/bridge-b1.json,
bridge-b2.json): [NeZero n] instance binder; redundant ¬ CV.Generic g.center conjunct; SignChanges with
δ ≤ radius; TripleAt through the total Cramer function edgeParameter (equal to the printed crossing
parameters wherever they exist, both conditions eventual); "central conditions of type T" read as the
whole item (T); Member.g4's f ≠ g (row 131); B2 on the concrete constructor eventOfTriple and the sorted
naming as hypotheses. Provenance note from the reviewers: BRIDGE.md cites SM11 line numbers of
sm-1-polygons.tex (+27 offset against the frozen SM15 file; quoted text identical) — a defect of the frozen
bridge file, recorded here, not patched. Checklist 87/192.

## lem:C-X1 proved — 2026-09-13 ~21:42Z (pod executor)

work/drafts/CX1A.lean (prover A, 292 lines; axioms + lit_homfly through homfly) ported to SM/CX1.lean; row
mapped `implemented`, review launched (3+2). The counting identity of the printed proof
(Σ_L carrierLeftTurns = ℓ(P) + |S|: every vertex on exactly one carrier retaining its turn; each selected
crossing one left and one right smoothing corner) was proved from the accepted corner-mark structure
(ccpCornerMark injective / exists / owner / isTrueCorner) — no library lemma existed. Draft B pending
as cross-check. Acceptance order: def:C first (under review), then lem:C-X1.

## Bridge:B3 and def:C accepted — 2026-09-13 ~21:48Z (pod executor)

Bridge:B3: 3/3 faithful, refuter clean (notes: δ ≤ radius; total edgeParameter; B3_unsorted WLOG).
def:C: 3/3 faithful, 2 refuters clean; all "stronger" entries are extra true consequences in the Prop
bundle; the integer-slot device (carrierRotationInt := round carrierRotation) judged faithful since
round is the identity on the integer rotations of decomposition carriers and nothing printed consumes the
values elsewhere. C is now available on the actual positive lifts: prop:C-chamber, prop:C-silent,
thm:C-S3/S5/S7, thm:C-soft, prop:anchor-values, thm:comparison, cor:C-inherits can be stated.
Next lane opened: prop:C-chamber (sm-4:36) via the accepted prop:chambers (constant crossing data along
labelled paths), lem:carriers, lem:rot(ii) and homfly's planar-isotopy invariance (Deform) on the
positive lifts, then the cyclic-quotient descent as printed. Claims verified 46/132, checklist 89/192.

## Flat-carriers lane: statement design adopted, five prover units launched — 2026-09-13 ~22:00Z (pod executor)

Design panel (two independent designs + judge, work/drafts/flatcarriers/PLAN_{A,B,FINAL}.md): winner B,
intrinsic definitions on `CrossingGeometry` ("geo*" mark/successor/carrier/corner-polygon machinery,
re-stated from the accepted Generic-parametrized Carrier lane so that the non-generic centre P(0) and the
deletion are handled "by the same words, no genericity being assumed", with `geo* = accepted*` on generic
polygons through `geoComponentEquivGeneric`), grafted with A's transport lemmas. Statement decisions,
STRONGER/WEAKER list and the reading right side = τ_j = −1, left = +1 are in PLAN_FINAL §2-§3 (to be
judged by the reviewers). The definitions and the two bundles `FlatCarriersDefinitionData` /
`FlatCarriersData` are ported sorry-free as SM/FlatCarriersDefs.lean (the row theorems are proved in
units U1-U5, work/drafts/flatcarriers/U*_*.lean, then assembled in SM/FlatCarriers.lean).
Also: lem:C-X1 draft B (279 lines, independent) finished after A was ported; kept as cross-check.

## Turning-number scout: Mathlib path lifting available; cf:def-turning implementer launched — 2026-09-13 ~21:52Z

work/reports/turning-number-scout-20260913.md: the pin has `IsCoveringMap.existsUnique_continuousMap_lifts`,
`liftPath`, `liftHomotopy`, `const_of_comp`, `Circle.isCoveringMap_exp`, and simply-connectedness of ℝ, ℝ²
(via contractibility), so tangent-angle lifts exist globally on ℝ and every independence clause of
cf:lem-turnlift (i) is a few lines. No winding/degree API exists. Design adopted: DirectionLoop =
1-periodic continuous T : ℝ → Plane of unit length; exists_lift as a theorem before `tw := (lift 1 − lift 0)/2π`
(Classical.choose; the printed text itself orders the definition after the lift existence, D7);
ClosedC1Curve with HasDerivAt fields; rot := tw of the normalised derivative; R := |rot|. Shared by SM rows
95-96 and CV rows 144-145 (F6). Implementer launched for the def row; lem-turnlift (i),(iii) next.

## lem:C-X1 accepted — 2026-09-13 ~21:56Z (pod executor)

3/3 faithful, 2 refuters clean, notes non-blocking (total-definition generalisation of wt/wind; "mixed"
as ¬all-right ∧ ¬all-left; weight_left unconditional since k(L) ≥ 1). Claims verified 47/132.

## cf:def-turning implemented — 2026-09-13 ~22:00Z (pod executor)

work/drafts/TurningNumber.lean (347 lines, standard axioms) ported to SM/TurningNumber.lean; row mapped
`implemented`, review launched (3+2). Rendering decisions (from work/drafts/TurningNumber_PLAN.md): direction
loop = 1-periodic continuous unit-length T : ℝ → Plane; the printed [0,1] tangent-angle lift is `IsSeamLift`;
`tw` is computed from a chosen global lift (Classical.choose of `exists_lift`, Mathlib covering-space lifting)
and the bundle proves tw = (θ(1) − θ(0))/2π for EVERY printed seam lift, so the definition is an instance of
the printed one; tw ℝ-valued with integrality (like rotationNumber); the sentence "for a polygon in the regular
locus, rot remains that of lem:rot" rendered as: the polygon rotation is the accepted rotationNumber (no
polygon-to-direction-loop construction is printed). Lift-choice and seam independence proved here (cheap and
needed for well-posedness); reparametrisation/homotopy invariance belong to cf:lem-turnlift (row 96,
implementer launched with models: reparametrisation = continuous strictly increasing φ with φ(s+1) = φ(s)+1;
homotopy through direction loops = continuous H on ℝ×ℝ with each H(t,·) a loop; reversal γ(−s)). CV row 144's
smooth paragraph is being completed on these shared definitions (CV_RotationSmooth.lean).

## CV:def:rot completed (row 144) — 2026-09-13 ~22:06Z (pod executor)

work/drafts/CV_RotationSmooth.lean (162 lines, standard axioms) ported to CV/RotationSmooth.lean: the
"Direction loops and smooth curves" paragraph of def:rot rendered through the shared SM/TurningNumber.lean
definitions (value-level aliases CV.tw / rotCurve / Rcurve; RotSmoothDefinitionData with 11 fields, incl.
`polygon_R_eq_SM` (CV rot = SM rotationNumber, as a theorem per F2, never an identification) and
`shared_with_SM` (F6 checkable)); row declaration `CV.rot_definition_full : RotDefinitionFullData extends
RotDefinitionData, RotSmoothDefinitionData`. Row mapped `implemented`; review launched (3+2). Row 145
(CV:lem:turnlift) waits for cf:lem-turnlift (i),(iii) (implementer running) — its (ii) is already
`CV.turnlift_ii`.

## mp:zero-link proved by the design panel; flat-carriers U5 done — 2026-09-13 ~22:08Z (pod executor)

The zero-link design panel's designer A proved the whole lemma (work/drafts/zerolink/Skeleton_A.lean, 73
lemmas: a one-dimensional entry/exit balance for affine families, barycentric triangle geometry, the apex
fan with radial cancellation, then the diagram-level sums; judge-merged as Skeleton_FINAL.lean, 1347 lines,
standard axioms, no Jordan-type input). Ported to SM/ZeroLink.lean with the fixed statement header
(work/drafts/ZeroLink_statement.lean verbatim); row mapped `implemented`; review launched (3+2). Design B
(ray-casting route, partial) kept as cross-check.
Flat-carriers U5 (selector) delivered: work/drafts/flatcarriers/U5_Selector.lean, 738 lines, sorry-free,
selector_def unconditional; selector_identity / other_selectors_agree under the explicit interface
hypotheses correspond_sides, central_vs_deletion_through_mu_j, others_unchanged, same_turn_signs,
extra_corner (turns_nonzero not needed: the table is exhaustive over SignType). Adds a `LawfulBEq (α ⊕ β)`
instance needed by `List.erase` on marks (U1/U2 will reuse it).

## cf:def-turning accepted — 2026-09-13 ~22:12Z (pod executor)

3/3 faithful, 2 refuters clean; notes non-blocking (seam fixed at 0 with shift; total-function lifts; the
Classical.choose device made invisible by the every-lift field; well-definedness fields delegated by the
printed text to cf:lem-turnlift (i); polygon sentence = accepted rotationNumber). Checklist 91/192.

## cf:lem-turnlift proved — 2026-09-13 ~22:15Z (pod executor)

work/drafts/TurnLift.lean (652 lines, standard axioms; plan work/drafts/TurnLift_PLAN.md) ported to
SM/TurnLift.lean: `SM.turnlift : TurnLiftData` (17 fields, all three printed clauses). Models of the informal
printed notions (to be judged by the reviewers): orientation-preserving reparametrisation = continuous
strictly increasing φ with φ(s+1) = φ(s)+1 (`Reparam`); homotopy through direction loops = `DirectionHomotopy`
(H : ℝ×ℝ → Plane, each H(t,·) a loop; the printed [0,1] case via projIcc); regular homotopy = jointly
continuous Γ, Γ′ with HasDerivAt in s, Γ′ ≠ 0, periodic; reversal γ(−s); (iii-a) rounding = subdivision
a k ≤ b k ≤ a(k+1) with corner arcs of lift increment ϑ_k and straight pieces along edge k; (iii-b) arc
replacement = arcs on [0,λ] / [0,μ] with a shared complementary arc up to a monotone ψ and equal tangents;
(iii-c) GL⁺(2) paths as four continuous entries with det > 0 and identity at 0. Row mapped `implemented`;
review to launch. CV row 145 (CV:lem:turnlift) is being assembled from these fields plus CV.turnlift_ii.

## Flat-carriers U3 delivered — 2026-09-13 ~22:17Z

work/drafts/flatcarriers/U3_CentreGeometry.lean (1339 lines, sorry-free, standard axioms): the centre
corner geometry ported from Generic to CrossingGeometry (direction lemmas, block compression
`geoCornerPolygon_edge`, `turn = sign det(in, out)`), the flat-centre facts (turn = 0 iff the corner is μ_j;
no antiparallel corner; StrictBetween at μ_j), and the turn-sign fields (same_turn_signs,
centre_turn_signs, extra_corner), bundled as `flat_carriers_U3` under explicit hypotheses: U2's centre
`GeoCarrierSpec` (only traced_successor used), U1's independence transfer for the sides and the deletion,
and the side facts extracted from FlatSidesData. U5 (selector) done earlier; U1, U2, U4 running.

## mp:zero-link accepted — 2026-09-13 ~22:18Z (pod executor)

3/3 faithful, 2 refuters clean (hand counts on small diagrams), notes non-blocking. Claims verified 48/132.

## Flat-carriers U1 delivered — 2026-09-13 ~22:22Z

work/drafts/flatcarriers/U1_Records.lean (1013 lines, sorry-free, standard axioms): common supports and
records from FlatSidesData, the mark identifications `geoMarkList_map_transport` (sides) and
`geoMarkList_deleteVertex_rotation` (deletion), the intrinsic successor gap on any CrossingGeometry,
`GeoCarrierSpec.of_core` (full spec from traced_successor + inherited_pieces) and the generic-side specs,
sides_are_smoothing_carriers / centre_deletion_same_words / named_sides / same_signs / selector_def, and the
ASSEMBLY theorems `flat_carriers_definition_of` / `flat_carriers_of` with the exact row statements, taking
the other units' interfaces as `OnSmallRadius` hypotheses (U2Interface, U3Interface, U4Interface,
U5Interface). Status: U1, U3, U5 done; U2 (correspondences) and U4 (rotation) running; then an assembler
combines the files into SM/FlatCarriers.lean.

## Flat-carriers U4 delivered — 2026-09-13 ~22:24Z

work/drafts/flatcarriers/U4_Rotation.lean (866 lines, sorry-free, standard axioms): `same_rotation` (side =
centre by a continuous corner family on the centre's index type with `markPointOn`, eventually constant
rotation via the regular-locus path constancy; deletion = centre via `rotationNumber_erase_flat`, erasing a
positively flat vertex through `appendVertex`), `exists_rotation_radius` uniform over all supports and
carriers. Takes U2's owner-iff / successor / corner-cycle identities and a side corner-list identification
(`hcorr`, which U2 must state) and U3's centre regularity facts as explicit hypotheses. Adds `LawfulBEq (α ⊕ β)`
and a canonical NeZero instance for corner-list lengths. Now only U2 (correspondences) is outstanding.

## CV:def:rot accepted; CV:lem:turnlift assembled; smoothing plan adopted — 2026-09-13 ~22:26Z (pod executor)

CV:def:rot (row 144): 3/3 faithful, 2 refuters clean (one recomputed ε_i on the printed counterexample);
notes non-blocking. Checklist 93/192.
CV:lem:turnlift (row 145): work/drafts/CV_TurnLift.lean (218 lines, standard axioms) ported to
CV/TurnLift.lean — `CV.turnlift_full : TurnLiftFullData` (18 fields: (i),(iii) from SM.turnlift on the CV
aliases; (ii) from CV.turnlift_ii / turnlift_ii_data; rounding lands on CV.rot via rot_eq_rotationNumber);
mapped `implemented`, review to launch.
Smoothing-existence lane: design panel finished (work/drafts/smoothing/PLAN_{A,B,FINAL}.md, Skeleton_FINAL.lean,
1758 lines, compiles in ~7 s with 144 sorried chain lemmas; winner A grafted with B's record-bridge
architecture; two defects of A fixed in the merge). Design finding recorded: the relational form
`IsOrientedSmoothing D x D₀ → RecordIso …` is NOT provable from the fixed OutsideMatch (no cyclic-order data);
the deliverable is the constructive `exists_smoothing_record : ∀ D x, ∃ D₀, IsOrientedSmoothing D x D₀ ∧
RecordIso D₀.record (D.record.smooth v)` (+ counts), which is what the (N,b) inductions consume; the skein
clauses of the accepted interfaces apply to every smoothing, so this suffices for lp:core / rp:record-polynomial
/ mp:*. Eight prover units launched on the shared skeleton (U1-U5, U6a/6b/6c), each proving its lemmas in place
in its own copy; an assembler will merge the proofs into SM/Smoothing.lean.

## Flat-carriers U2 delivered; assembler launched — 2026-09-13 ~22:30Z

work/drafts/flatcarriers/U2_Correspondence.lean (1643 lines, sorry-free, standard axioms): the centre
GeoCarrierSpec by transport, correspond_sides / correspond_deletion (skip-μ_j conjugation, owner-iff through
fusionMark, surjectivity), unique_through_mu_j, the mark/corner/plane-cycle identities, same_retained_crossings;
both pairing facts proved (not assumed); only U1's two mark identifications and independence transfer assumed.
All five units are in (U1 1013, U2 1643, U3 1339, U4 866, U5 738 lines); an assembler is merging them into one
file with the two row theorems `flat_carriers_definition` / `flat_carriers` (statements of Statement_FINAL.lean,
bundles in SM/FlatCarriersDefs.lean), de-duplicating the four independent `LawfulBEq (α ⊕ β)` instances.

## cf:lem-turnlift accepted — 2026-09-13 ~22:31Z (pod executor)

3/3 faithful, 2 refuters clean; every model of the informal printed notions (Reparam, DirectionHomotopy,
RegularHomotopy, reverse, rounding subdivision, arc replacement with a monotone ψ, GLPlusPath) explicitly
accepted by the reviewers; notes non-blocking (3 ≤ n implied by Regular; unused printed hypotheses carried by
the bundle). Claims verified 49/132.

## Smoothing U6b delivered — 2026-09-13 ~22:36Z

work/drafts/smoothing/U6b_model.lean: all 9 model-level record-bridge lemmas proved in place (origVisit
injective / exists / twin / overBit / visitCoord, compOf_eq_iff_of_cls, the successor law `succ_of_coord`,
oldCls_eq); two helpers added (a strand of a Γ₀-crossing is never an arc; origParam ∘ liftParam = id on
non-arc kinds — the plan's sketch was false on arcs, the statement itself is true). Skeleton sorry count
146 → 137. Other seven units still running.

## prop:C-chamber: proof design adopted, six prover units launched — 2026-09-13 ~22:40Z (pod executor)

Design panel (work/drafts/cchamber/PLAN_{A,B,FINAL}.md; Skeleton_FINAL.lean, 678 lines, 52 sorried chain lemmas,
compiles in ~6 s): winner B (path-based route) grafted with A. Route: a mark transport between two generic
polygons with the same combinatorics transports the Carrier lane's successor/carrier/crossing data, corner
lists and corner polygons (up to rotation of the index), uniformity, ℓ(P), slots, coefficients and the state
sum; the path instance comes from the accepted `SM.chambers` (constant chirotope, crossing set and parameter
orders along a labelled path) with the corner polygons a continuous regular family (rotation and turn signs
constant) and the positive lifts Deform-related (homfly constant by lit:homfly's planar clause, avoiding the
unproved rp:record-polynomial); the cyclic-shift instance is a Reparam of the one-component positive lift;
the descent to the quotient chambers is closed in the skeleton. Units U1a, U1b, U2, U3, U4, U5 launched on the
shared skeleton (prove in place). Statement fixed: work/drafts/CChamber_statement.lean.

## CV:lem:turnlift accepted — 2026-09-13 ~22:42Z (pod executor)

Row 145: 3/3 faithful, refuter clean; the CV/SM content difference (polygon rot = the ε_i ray formula) judged
correctly rendered through CV.turnlift_ii and rot_eq_rotationNumber; notes non-blocking. With rows 144-145
the CV rotation block is complete; decision F6 (shared turning-number definitions) worked as intended.

## Smoothing U2 delivered — 2026-09-13 ~22:46Z

work/drafts/smoothing/U2_disc.lean: all 28 disc / D-arc lemmas proved in place (disc radius, frontier
parameters, cyclic-order lemmas on traversal points, cleanness of D, the two arcs through the crossing);
helpers marked "(U2 helper)"; 475 lines added; no statement changed. Units done: U2, U6b; running: U1, U3,
U4, U5, U6a, U6c.

## def:flat-carriers / cor:flat-carriers assembled and ported — 2026-09-13 ~22:46Z (pod executor)

work/drafts/flatcarriers/FlatCarriers_Assembled.lean (5667 lines, 243 declarations, standard axioms, 11 s;
ASSEMBLY_REPORT.md records the de-duplication — four independent LawfulBEq (α ⊕ β) instances, several
lemmas proved twice, two renames — and the wiring of the units' interfaces with radii δF, δS, δR) ported to
SM/FlatCarriers.lean; both row theorems byte-identical to Statement_FINAL.lean. Rows mapped `implemented`;
review launched (3 lens + 2 refuters per row; reviewers may read PLAN_FINAL §2-§3 as the executor's
dispositions). Total flat-carriers effort: design panel + 5 units + assembler, ≈ 5.6k lines in ~1.5 hours.

## C-chamber U4 delivered — 2026-09-13 ~22:50Z

work/drafts/cchamber/U4.lean: the three link-layer lemmas proved in place (crossingGeometry_of_single_generic;
Deform.of_family — a continuous family of one-component generic shadows with constant crossing pairs and over
data is a Deform, via projIcc; isPositive_deform_of_family — positivity persists by the constant sign of a
continuous nonzero determinant). Sorry count 50 → 47. Other five C-chamber units running.

## Smoothing U1 delivered; one false chain lemma — 2026-09-13 ~22:51Z

work/drafts/smoothing/U1_clearance.lean: 50 of 51 lemmas proved (clearance radius, ε, cut points, kind laws,
model-level segment/adjacency laws), 687 lines added. `seg_arc_subset_ball` is FALSE as stated (sup norm on
Plane: the arc may lie on the sphere — counterexample recorded); the correct `seg_arc_subset_closedBall` is
proved and PLAN_FINAL §5 now carries the assembly rule (closedBall + the strict `arc_lt_discRadius`). Units
done: U1, U2, U6b; running: U3, U4, U5, U6a, U6c.

## C-chamber U1a delivered — 2026-09-13 ~22:53Z

work/drafts/cchamber/U1a.lean: all 9 transport lemmas (twin, markSuccessor, selectedMarkPerm,
smoothingSuccessor, SameCycle across the mark equivalence — proved by a zpow induction since Mathlib has no
SameCycle-along-Equiv lemma —, carrierCrossings, carrierCrossingCount, IsDecomposition, IsTrueCorner) proved in
place; no helpers added. C-chamber units done: U1a, U4; running: U1b, U2, U3, U5.

## C-chamber U3 delivered — 2026-09-13 ~22:54Z

work/drafts/cchamber/U3.lean: all 13 path-instance lemmas proved in place (mark order transport along a path,
the mark-list transport, continuity of crossing points and of the transported corner polygons, regularity,
rotation constancy, turn-sign constancy, crossing-pair constancy by local constancy on the connected interval,
the Deform of the positive lifts); one helper `turn_recastTuple_cast` added. C-chamber units done: U1a, U3,
U4; running: U1b, U2, U5.

## C-chamber U1b delivered — 2026-09-13 ~22:55Z

work/drafts/cchamber/U1b.lean: all 11 recast / corner-polygon transport lemmas proved in place (five helpers:
ZMod cast values, a rotation-filter-map engine, two getElem-up-to-equality readers). C-chamber units done:
U1a, U1b, U3, U4; running: U2, U5.

## C-chamber U2 delivered; one misstated chain lemma — 2026-09-13 ~22:56Z

work/drafts/cchamber/U2.lean: 7 of 8 lemmas proved (uniformity, index set, slot / coefficient / product and the
state-sum transport). `leftTurns_transport` as written omits `τ` from its statement (Lean's variable inclusion),
making it a false universal claim — counterexample machine-checked; the intended content is proved as
`leftTurns_eq_of_transport` and PLAN_FINAL §5 carries the assembly rule. C-chamber units done: U1a, U1b, U2,
U3, U4; running: U5. Smoothing units done: U1, U2, U6b; running: U3, U4, U5, U6a, U6c.

## Smoothing U5 delivered — 2026-09-13 ~22:57Z

work/drafts/smoothing/U5_models.lean (+1179 lines): both concrete splice models (`mixedModel`, `selfModel`, all
seven laws each) proved with a ZMod.val toolbox, strand case principles and code-based injectivity; no law was
false for the printed layouts. Smoothing units done: U1, U2, U5, U6b; running: U3, U4, U6a, U6c.

## C-chamber U5 delivered; assembler launched — 2026-09-13 ~22:58Z

work/drafts/cchamber/U5.lean: all six shift-instance lemmas proved (the cyclic re-indexing of the one-component
positive lift is a Reparam via a shift StrandMap pullback; markList_shift_rotated via the accepted
sorted_map_cut_rotation, which needed `import SM.SortedCut`). All six C-chamber units are in; assembler
launched to merge them into work/drafts/cchamber/CChamber_Assembled.lean (with the `include τ in` fix).

## Smoothing U3 delivered — 2026-09-13 ~23:00Z

work/drafts/smoothing/U3_generic.lean (+1135 lines): all 16 genericity and crossing-correspondence lemmas of
the splice model proved (coordinate lemmas p + α·es + β·et via `module` and `coords_unique`; meeting-pair
classification; strand determined by its orig and the crossing point). It cites U1's `seg_arc_subset_ball`
(false as stated) among its sorry inputs — the assembler applies the closedBall rule (PLAN_FINAL §5 addendum).
Smoothing units done: U1, U2, U3, U5, U6b; running: U4, U6a, U6c.

## Smoothing U6a delivered — 2026-09-13 ~23:01Z

work/drafts/smoothing/U6a_cyclic.lean (+684 lines): all 7 cyclic-order core lemmas (first-return no-between by
induction on the return time, the smoothed coordinate rkey and its injectivity per block, reconnect_no_between
in the self and mixed cases, the self-case cycle classification via a forward-closed word under succ ∘ swap,
sameCycle_of_comp_ne, visitBetween_iff_of_rot_lt_iff), all standard axioms; 36 helpers (a cycBetween toolbox
and swap-orbit lemmas, candidates for LinkDiagramExtras). Smoothing units done: U1, U2, U3, U5, U6a, U6b;
running: U4, U6c.

## Smoothing U6c delivered — 2026-09-13 ~23:03Z

work/drafts/smoothing/U6c_cases.lean (+1110 lines): all 8 per-case lemmas (mixed/self base membership,
classification bijections, visit classification, the rotated-coordinate order `key_lt_iff` per block) proved via
explicit block data and a generic block-monotonicity lemma; the four goal theorems already close from the chain.
Smoothing units done: U1, U2, U3, U5, U6a, U6b, U6c; only U4 (outside match and D₀ arcs) running.

## prop:C-chamber assembled and ported — 2026-09-13 ~23:05Z (pod executor)

work/drafts/cchamber/CChamber_Assembled.lean (1384 lines, 99 declarations; 49 sorry replacements + 7 helper
insertions from the six units, pairwise-disjoint hunks; the `include τ in` fix of `leftTurns_transport`; axioms
propext/Classical.choice/Quot.sound/SM.lit_homfly) ported to SM/CChamber.lean; `CChamberData` and the signature
of `C_chamber` byte-identical to the fixed statement. Row mapped `implemented`; statement review already running.
Total prop:C-chamber effort: design panel + 6 units + assembler ≈ 1.4k lines in ~1.3 hours; the route avoids
rp:record-polynomial by using lit:homfly's planar-isotopy clause on the Deform of the positive lifts.

## Fixed target name: prop:C-chamber → `SM.prop_C_chamber` — 2026-09-13 ~23:07Z

The checker rejected the mapping `SM.C_chamber` ("fixed declaration name mismatch"): the eight target rows of
work/lean/axiom-policy.json `targets` have FIXED declaration names (prop:C-chamber = `SM.prop_C_chamber`).
Renamed the theorem in SM/CChamber.lean, the statement draft and the reviewer input (name only; bundle and
statement unchanged), rebuilt, remapped. Lesson recorded: consult axiom-policy.json `targets` before naming a
target row's declaration (the other seven: see the block; the memory note now lists them).

## prop:C-chamber accepted — 2026-09-13 ~23:10Z (pod executor)

3/3 faithful, refuter clean; the chamber notion and the labelled-representative quantification judged exact;
[NeZero n] redundant (non-blocking). First Chapter-4 target row closed (fixed name SM.prop_C_chamber). Claims
verified 51/132. The proof route (Deform of the positive lifts + lit:homfly planar clause; cyclic-shift Reparam;
descent by local constancy on the quotient) is recorded in work/drafts/cchamber/PLAN_FINAL.md.

## def:flat-carriers and cor:flat-carriers accepted — 2026-09-13 ~23:12Z (pod executor)

Both rows 3/3 faithful, 2 refuters clean each; all PLAN_FINAL §2-§3 dispositions judged correct (readings
recorded in reviews/def-flat-carriers.json, cor-flat-carriers.json). The flat-carriers lane (design panel, five
prover units, assembler; ≈ 5.7k lines) closed in about 1.7 hours. Claims verified 52/132, checklist 98/192.

## Smoothing U4 delivered; all eight units in; assembler launched — 2026-09-13 ~23:15Z

work/drafts/smoothing/U4_outside.lean (+1076 lines): all 21 outside-match / D₀-arc lemmas proved (over data
and signs, cleanness of D₀, the two smoothing arcs, the bijection of outside traversal points and the
OutsideMatch fields); the §5 fallbacks were not needed. All eight smoothing units are sorry-free on their own
lemmas; the assembler merges them (with the closedBall rule for the false `seg_arc_subset_ball`) into
work/drafts/smoothing/Smoothing_Assembled.lean → SM/Smoothing.lean, after which lp:core, rp:record-polynomial,
lp:split-circle, lc:presentations and mp:* can be proved on the fixed statements.

## thm:C-S5 statement fixed; two provers launched — 2026-09-13 ~23:16Z (pod executor)

work/drafts/CS5_statement.lean: `WallGerm.EmptyCusp g h hc` renders def:walls (K) "the cusp is empty if on the
loop side the two visits of the newborn crossing are cyclically adjacent in the Gauss word" as
`∀ s : g.SideParameter, GaussVisitsAdjacent … (twoStepFirstVisit (cusp_loop_crossing h hc s))
(twoStepLastVisit …)` on the loop side `g.cuspLoopSide b j` (the accepted lem:cusp-sides bundle's own
hypothesis form; the ∀-reading of "on the loop side" as a property of the whole side); `P_no` is every polygon
of the other side `g.sideTuple (!(g.cuspLoopSide b j)) t`; `CS5Data.empty_cusp_zero : … → cornerStateSum … = 0`.
Fixed target name `SM.thm_C_S5`. Route: lem:cusp-sides (ii)+(iii) (needle_turns, empty_middle_edge) ⇒ every
decomposition has a mixed carrier through the consecutive corners ⇒ uniformDecompositions = ∅ ⇒ C = 0.

## thm:C-S3 statement fixed; design panel launched — 2026-09-13 ~23:19Z (pod executor)

work/drafts/CS3_statement.lean (fixed target name SM.thm_C_S3): at a simple flat wall germ g at j on n+1 ≥ 4
vertices (the lem:flat-sides hypotheses hz hb hc hsc, as in the accepted flat_sides / flat_carriers), there is a
radius δ such that for all side parameters tR, tL < δ with IsRightSide (τ_j = −1) / IsLeftSide (τ_j = +1),
cornerStateSum (P_right) − cornerStateSum (P_left) = cornerStateSum (deleteVertex g.center j) (generic by
generic_deleteVertex). Planned route (panel): lem:C-X1's selector form on the three configurations; the accepted
cor:flat-carriers correspondences (equal slots via same retained crossings and same rotation; selector_identity and
other_selectors_agree); equal HOMFLY of the positive lifts via lit:homfly's planar clause — a Deform across the
flat centre (the centre corner polygon is a generic one-component shadow with a zero turn) and a Reparam for the
flat subdivision at μ_j (insert-vertex on a straight edge) — avoiding the unproved rp:record-polynomial/lp:core
as in prop:C-chamber.

## thm:C-S5 proved (draft A) — 2026-09-13 ~23:23Z (pod executor)

work/drafts/CS5A.lean (123 lines; axioms + lit_homfly through def:C) ported to SM/CS5.lean; row mapped
`implemented` under the fixed name SM.thm_C_S5; review launched (3+2). Proof follows the printed one: cusp_sides
(needle_turns on the no-loop side, empty_middle_edge), a new helper `Carrier.markSuccessor_vertex_of_no_crossing`
(the successor of a vertex mark whose edge carries no crossing is the next vertex), so every decomposition has a
carrier owning both corners with opposite turns ⇒ no uniform decomposition ⇒ C = 0. Draft B pending as
cross-check.

## thm:C-S5 draft B (cross-check) — 2026-09-13 ~23:26Z

work/drafts/CS5B.lean (215 lines, same axioms) independently proves the row via the reusable
`cornerStateSum_eq_zero_of_consecutive_opposite` (a generic polygon with two consecutive corners of opposite turn
whose connecting edge carries no crossing has C = 0) — a candidate for the library when a later row needs it
(thm:C-soft / prop:anchor-values may). Draft A (123 lines) stays ported; B kept as cross-check.

## Smoothing gate closed: SM/Smoothing.lean ported — 2026-09-13 ~23:30Z (pod executor)

work/drafts/smoothing/Smoothing_Assembled.lean (8213 lines, 661 declarations; eight units merged in order with four
de-duplications; the false `seg_arc_subset_ball` deleted and its five uses adapted to the closedBall form; 25 s
compile; standard axioms) ported to SM/Smoothing.lean (library module, no row). Delivered: `exists_smoothing`,
`exists_smoothing_record` (∃ D₀, IsOrientedSmoothing D x D₀ ∧ RecordIso D₀.record (D.record.smooth (overVisit x))),
`exists_smoothing_record_visit`, `exists_smoothing_counts`. The smoothing-existence lane (design panel + 8 units +
assembler; ≈ 8.2k lines) took ≈ 2.7 hours. Next: the (N, b)-induction lane for rp:record-polynomial, lp:core,
lp:split-circle, lc:presentations, mp:stack on the fixed statements (work/drafts/{RecordPolynomial,LpCore,
SplitCircle,Presentations,Stack}_statement.lean).

## thm:C-S5 accepted; thm:C-S3 design adopted — 2026-09-14 ~00:34Z (pod executor; the shell tool was rate-limited from ~23:30Z to ~00:30Z, the acceptance step waited)

thm:C-S5: 3/3 faithful, 2 refuters clean; notes non-blocking (StrictBetween vs "lies between"; ∀ loop-side
parameter; C(P_no) at every no-loop-side germ point; case quantified). Second target row closed (targets 2/8).
thm:C-S3 design panel (work/drafts/cs3/PLAN_{A,B,FINAL}.md, Skeleton_FINAL.lean compiles): winner A grafted with
B — Deform along the accepted corner family with genericity at the centre derived from the deletion copy
(reindexing for carriers not through μ_j; a positive-flat subdivision (appendVertex) for the carrier through
μ_j), the subdivision as a hand-built Reparam of the one-component positive diagram, two side parameters reduced
by chamber and turn constancy; the judge closed the state-sum reindexing and the assembly, leaving three units
(subdivision genericity, subdivision Reparam, list surgery at μ_j; ≈ 1000 lines). Units launched on the shared
skeleton. Claims verified 53/132, checklist 99/192.

## C-S3 unit U1 delivered — 2026-09-14 ~00:47Z

work/drafts/cs3/U1.lean (+409 lines): the four subdivision-genericity lemmas proved (regular_adjacent_meet,
edgeSegment_appendVertex_union, appendVertex_new_pairs_disjoint, Link.single_generic_appendVertex — a generic
one-component shadow stays generic after a positive-flat subdivision of its closing edge at a point on no other
closed edge). Units U2 (subdivision Reparam) and U3 (list surgery at μ_j) running.

## Polynomial block ported: SM/PolynomialBlock.lean (lp:core, rp:record-polynomial, lc:presentations, lp:split-circle) — 2026-09-14 ~00:57Z (pod executor)

The design panel (work/drafts/polyblock/PLAN_{A,B,FINAL}.md; winner B — a RECORD-LEVEL based order `Record.RBasing`
with one induction principle `skein_induction_based` — grafted with three ideas of A) delivered
work/drafts/polyblock/Skeleton_FINAL.lean with the chains of four rows fully proved; the sorry-free part (§0-§5 and
the four row theorems of §7, 1182 lines) is ported verbatim (header added, docstring `z²` restored to the statement
file's spelling, §7 heading reworded) as SM/PolynomialBlock.lean, built (`lake build SM.PolynomialBlock`, no errors),
and the four rows mapped `implemented`: lp:core → SM.lp_core (bundle LpCoreData), rp:record-polynomial →
SM.record_polynomial (RecordPolynomialData), lc:presentations → SM.presentations, lp:split-circle →
SM.split_circle (SplitCircleData). Bundles are byte-identical to work/drafts/{LpCore,RecordPolynomial,
Presentations,SplitCircle}_statement.lean. Axioms: record_polynomial / presentations / split_circle use the
standard three + SM.lp_lm; lp_core additionally SM.lit_homfly (field eq_homfly) and SM.lp_lm_uniqueness (via the
accepted lp:coefficient-transport / RCompetitor). Review (3 lens reviewers + 2 refuters per row; brief
work/port/review_prompt_polyblock.md; reviewer input work/reviews/polyblock-reviewer-input-statement.lean.txt =
the module with the four row proofs replaced by sorry and the four statement-file notation maps attached)
launched 00:57Z.

Proof-route deviations from the printed proofs, recorded for the reviewer of the proofs (statements untouched):
1. The printed (N, b) induction on rp:record-polynomial switches "the first bad crossing"; the Lean induction
   (`skein_induction_based`) allows switching ANY bad crossing — the lexicographic measure (N, b) still drops, and
   the partner diagram D' is carried inside the motive, so no first-return enumeration is needed.
2. lp:core's `gaussian` (P_D ∈ R with R.toRG (P D) = φ(F_D)) and `support` are proved by the printed integral
   descent as a `skein_induction` on the Gaussian evaluation G = φ(F) (grafted from A), not through
   lp:coefficient-transport; `eq_homfly` uses the accepted lp:coefficient-transport (RCompetitor) as printed
   (round-3 identification paragraph); `unique` and `ne_zero` are direct `skein_induction`s.
3. lp:split-circle is proved at the record level (`Record.addFree`: the record with one crossing-free
   component added) by `skein_induction_based`, the diagram side entering only through the accepted
   `exists_smoothing_record`, `switch_record` and the Reparam record iso of `IsSplitCircleAddition`.
4. New helper definitions of the module (RBasing, key, IsBad, badCount, RUnderFirst, Record.addFree, G, …) are
   proof infrastructure and appear in no row statement; the row statements use only the accepted notions
   (P, lmF, homfly, RecordIso, IsSkeinTriple, UnderFirst, InSupportM, coeffAt, IsSplitCircleAddition, moves).
mp:stack's chain (§6, 13 open lemmas) stays in the draft; five prover units (U1 perm, U2 record isos, U3 init,
U4 block bookkeeping, U5 step) launched on the shared skeleton 00:50-00:57Z; assembly → SM/Stack.lean.

## C-S3 unit U3 delivered — 2026-09-14 ~00:58Z

work/drafts/cs3/U3.lean (+185 lines): exists_appendVertex_of_erase_flat, mu_j_unique_edge (+ helper
mu_j_unique_edge_ccp), exists_appendVertex_central proved; remaining sorries exactly U1's and U2's lemmas. U2
(subdivision Reparam) still running; then the assembler merges U1-U3 into the judge-closed skeleton.

## mp:stack units U1, U4 and C-S3 unit U2 delivered; C-S3 assembler launched — 2026-09-14 ~01:01Z

mp:stack: U1 (work/drafts/polyblock/U1.lean, +154 lines) proves firstReturn_firstReturn and firstReturn_mul_swap
(helpers firstReturn_val_eq_of_pow, firstReturn_congr_pred, mul_swap_pow_apply_of_forall_ne, firstReturn_pow_val_spec,
firstReturn_mul_swap_apply_left; standard axioms). U4 (U4.lean, +70 lines) proves rBlockOrdered_of_blockOrdered,
BlockOrdered.switch_of_internal, blockRestrict_switch_of_internal/external, blocks_of_smoothing (the last inherits
sorryAx only through smoothBlock's well-definedness proof = U2's beta_comp_eq_of_reconnect_sameCycle). U2 (record
isos), U3 (init), U5 (step) running.
thm:C-S3: U2 (work/drafts/cs3/U2.lean, +546 lines) proves subdivPt_bijective, traversalKey_subdivPt_lt_iff (via a
strictly monotone key map subdivKeyMap) and reparam_positiveDiagram_single_appendVertex (ReparamData with e = refl,
φ = subdivPt; a general exists_crossing_overVisit_eq does the over-strand bookkeeping). Deviation from the plan sketch:
the Reparam proof does not use the hypothesis hoff nor U1's edgeSegment_appendVertex_union /
appendVertex_new_pairs_disjoint (those remain needed by single_generic_appendVertex); hoff stays in the fixed
statement (unused-variable lint silenced locally). All three C-S3 units done → assembler launched (target
work/drafts/cs3/CS3_Assembled.lean, sorry-free, axioms standard + lit_homfly).

## thm:C-S3 assembled and ported; mp:stack U3 delivered; two panels launched — 2026-09-14 ~01:07Z (pod executor)

thm:C-S3: the assembler merged U1-U3 into work/drafts/cs3/CS3_Assembled.lean (2509 lines, 0 sorry, 12 hunks, no
de-duplication needed; `#print axioms SM.thm_C_S3` = propext, Classical.choice, Quot.sound, SM.lit_homfly; bundle
CS3Data byte-identical to work/drafts/CS3_statement.lean; ASSEMBLY_REPORT.md). Ported verbatim (header added) as
SM/CS3.lean, `lake build SM.CS3` clean; row mapped `implemented` under the fixed name SM.thm_C_S3; reviewer input
work/reviews/thm-C-S3-reviewer-input-statement.lean.txt (proof withheld, notation map attached), excerpt sm-4:153-159,
brief work/port/review_prompt_thm-C-S3.md; review (3 lenses + 2 refuters) launched next. Proof route as designed:
selector form of C (lem:C-X1), cor:flat-carriers correspondences, equal HOMFLY of positive lifts via lit:homfly's
planar clause on a Deform through the flat centre and a Reparam for the subdivision at μ_j — no use of
rp:record-polynomial / lc:presentations (then unaccepted).
mp:stack: U3 (work/drafts/polyblock/U3.lean, +96 lines) proves restrict_underFirst and stack_init (axioms standard +
lp_lm). Open: U2 (record isos) and U5 (step).
prop:C-silent: statement fixed in work/drafts/CSilent_statement.lean (bundle CSilentData: fields extension (E) and
cut (C); ∀ pairs of side parameters, C(sideTuple true tp) = C(sideTuple false tm); no δ, since each side lies in one
chamber and prop:C-chamber makes C constant there — the CS5 precedent); design panel (2 architects + judge, output
work/drafts/csilent/) launched 01:05Z. Marked-product block (mp:join, mp:lowest, mp:blocks, lem:homflyrows):
statement-design panel (2 designers + judge, output work/drafts/markedproducts/Statements_FINAL.lean +
NOTES_FINAL.md) launched 01:05Z; I fix the statements after reading the judge's notes.

## mp:stack U5 delivered; CV and R-lane side work opened — 2026-09-14 ~01:11Z

mp:stack: U5 (work/drafts/polyblock/U5.lean, +100 lines) proves stack_step exactly along PLAN_FINAL §6.5 (solvedR_of_skein
handles both crossing signs; block bookkeeping via blockRestrict_switch_of_internal/external and blocks_of_smoothing;
record-iso chains through restrictSmoothIso / restrictSmoothDisjointIso; P transported by P_congr). Only U2 (record
isos) is open; then the assembler merges U1-U5 → SM/Stack.lean.
CV lane (F2(A) unchanged): provers launched for CV:lem:uniformrot (work/drafts/CV_uniformrot.lean, from the accepted
SM.uniform_rotation / rotation_number and CV.rot_eq_rotationNumber) and for the two CV axiom rows to be DERIVED:
CV:ax:homfly (CV.ax_homfly from lit_homfly + lp_core (+ coefficient_transport for uniqueness)) and CV:ax:gausscode
under the F4 replacement (CV.gausscode_polynomial: RecordIso → homfly D = homfly D' for one-component diagrams, from
record_polynomial.P_eq + lp_core.eq_homfly) — the printed "present the same oriented link" is outside the formal scope
(design decision D2/11); consumers read only the polynomial (cv-lane-plan F4). Both wait for the polynomial-block
acceptance before their rows are mapped. R lane: statement-design panel launched for the four X₁-free obligation rows
R:localization, R:parity, R:fibre_partition, R:generic_table (fixed names RProof.*; output work/drafts/rlane/).

## Polynomial block ACCEPTED (lp:core, rp:record-polynomial, lc:presentations, lp:split-circle) — 2026-09-14 ~01:21Z (pod executor)

Review (work/reviews/{lp-core,rp-record-polynomial,lc-presentations,lp-split-circle}.json; raw workflow outputs
/workspace/scratch/lean_results/<slug>-round1.output): 12/12 lens reviews faithful, 8/8 refuters found nothing; every
discrepancy labelled non-blocking (recorded in the review files: P as real part + gaussian descent field; D10 circle
reading; eq_homfly on the chosen witness; IsSkeinTriple per D3; coeff_eq displayed for P; subst_eq over A : Type;
RecordIso.comp_eq implicit; lc:presentations' instance sentence illustrative; IsSplitCircleAddition via Reparam of
the restriction). Rows set accepted with the audit hashes of the 01:05Z checker run; checker re-run started 01:21Z.
Claims verified 57/132 (43.2%), checklist 103/192. write_review_and_accept.py now stamps the actual spawn date in the
AI disclosure (previously hard-coded 2026-09-13).
Consequences: the CV axiom rows CV:ax:homfly / CV:ax:gausscode (F4 replacement) and mp:join / mp:lowest / mp:blocks
are unblocked; prop:C-silent's design may use SM.presentations.
CV:lem:uniformrot: prover delivered work/drafts/CV_uniformrot.lean (306 lines, standard axioms; bundle
CV.UniformRotData: pos_ge_one, pos_three, neg_le_neg_one, neg_three, one_dissent — (ii) admits zero turns among the
non-negative ones as printed d3:283-288, which SM.uniform_rotation does not cover, so the r ≥ 1 bound is re-proved by
the printed dual-vector argument via the NarrowSector lemmas). Ported as CV/UniformRot.lean, row mapped implemented
(CV.uniformrot); review next.

## thm:C-S3 ACCEPTED (third target row); CV axiom rows ported; mp:stack units complete — 2026-09-14 ~01:24Z (pod executor)

thm:C-S3: 3/3 lens reviews faithful, 2 refuters clean; notes non-blocking (side representatives below an existential δ
with the τ_j = ∓1 predicates over both Booleans, equivalent to the chamber values by def:germ + prop:C-chamber; labelled
deletion deleteVertex g.center j; hypotheses = WallGerm.FlatAt at N = n+1). Review work/reviews/thm-C-S3.json; hash from
the 01:22Z checker (105 mapped, 14828 audited, passed; receipt work/checks/dev-check-polyblock-accepted.json, which also
confirms the four polynomial-block hashes). Targets 3/8; claims verified 58/132 (43.9%), checklist 104/192.

CV:ax:homfly and CV:ax:gausscode (rows 160, 163) — DERIVED, not assumed (OPEN_WORK.md; cv-lane-plan F4). Prover draft
work/drafts/CV_axioms.lean ported as CV/Axioms.lean (267 lines; `lake build CV.Axioms CV.UniformRot` clean; axioms of
both rows: propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness). Rows mapped
`implemented`: CV:ax:homfly → CV.ax_homfly (bundle CV.AxHomflyData: descent on LinkEquiv, unknot, skein, reidemeister,
knot_parity (InSupportM 1), knot_product_z0 (new lemma CV.zRow_zero_mul_of_inSupportM_one), unique via
SM.coefficient_transport with the helper CV.rcompetitor_of_descent); CV:ax:gausscode → CV.gausscode_polynomial.
SCOPE/CHECKER CHANGE for CV:ax:gausscode, recorded as the plan requires: (a) printed (d10_axioms.tex:525-532): for two
oriented link diagrams whose underlying curves are connected generic immersed circles in the sphere with an
orientation-preserving record isomorphism, "D and D' present the same oriented link"; (b) replacement:
`CV.gausscode_polynomial (D D' : Diagram) (hD : D.componentCount = 1) (hD' : D'.componentCount = 1)
(i : RecordIso D.record D'.record) : homfly D = homfly D'` — proved from rp:record-polynomial (P_eq) and lp:core
(eq_homfly); the link-equivalence conclusion is outside the formal scope (design decision D2/11: LinkEquiv is the
equivalence generated by the moves, Reidemeister's theorem and Carter's classification are not formalized); (c) every
in-scope consumer reads only the polynomial: lem:pieceintrinsic (d6:56), prop:chamberinv(ii) (d1:1040-1060),
lem:silence (d1:1381-1396), cor:groupedknot (A)(B) (d6:263), lem:curl(i) via RI, and the RA files
R_GENERIC_COMMON_TRANSPORT §1-2, R_GENERIC_SELECTED_COUPLE §3, R_EXTREME_SINGLETON_TRANSPORT §1-2,
R_EXTREME_SELECTED_COUPLE §2, R_ATTACHMENT_WARRANTS §4 (list from cv-lane-plan F4); (d) the row id CV:ax:gausscode is
kept and points at the replacement; the independent review of both rows (launched next, brief
work/port/review_prompt_cv-axioms.md) is instructed to judge the replacement explicitly, and its verdict will be
appended here.
mp:stack: U2 (work/drafts/polyblock/U2.lean, +547 lines) proves beta_comp_eq_of_reconnect_sameCycle, restrictSmoothIso,
restrictSmoothDisjointIso (via primed clean forms over (ρ.restrict B).M); all five units done; assembler launched
(targets work/drafts/polyblock/Stack_Assembled_full.lean and Stack_Module.lean = §6 + StackData/stack on top of
SM.PolynomialBlock). CV:lem:uniformrot review launched 01:23Z.

## CV lane widened; CV-DOM decision panel opened — 2026-09-14 ~01:28Z (pod executor)

Launched: provers for CV:def:record + CV:def:homfly (rows 140-141; work/drafts/CV_record_homfly.lean, on the accepted
record layer and CV.ax_homfly / lp:core / lp:split-circle) and CV:lem:fulltwist (row 159; work/drafts/CV_fulltwist.lean,
from CV.ax_homfly's skein and RII clauses); review of CV:ax:homfly / CV:ax:gausscode (brief
work/port/review_prompt_cv-axioms.md, 3 lenses + 2 refuters per row, the gausscode refuters instructed to check that
the listed consumers need only polynomial equality).
CV-DOM: decision F2(A) of 2026-09-13 (no domain narrowing) left the carrier-dependent CV rows (135-139, 142-147, 151,
164) and through them the whole R lane and Bridge:B4 — the critical path to SM:corner_laws_and_soft — waiting for a
re-parametrisation of the Carrier lane whose cost was estimated at 2-3 prover-weeks. Because accepted declarations
must never be rewritten, the options are re-examined by a decision panel (2 analysts + judge; output
work/drafts/cvdom/DECISION_FINAL.md): (A) generalised lane alongside the accepted one, (B) documented narrowing with
the Bridge-B1 justification, (C) a CV-native carrier layer over CrossingGeometry, (D) a transfer principle. The judge's
recommendation becomes the recorded decision (with the review note every affected row must carry) once I have read it.

## mp:stack assembled and ported: SM/Stack.lean — 2026-09-14 ~01:32Z (pod executor)

The assembler merged U1-U5 into work/drafts/polyblock/Stack_Assembled_full.lean (2499 lines, 0 sorry, 17 disjoint hunks,
no de-duplication needed; 51 new helper names, none clashing with work/lean) and extracted Stack_Module.lean (= §6 with
proofs + StackData/stack on top of SM.PolynomialBlock; 1358 lines; `#print axioms SM.stack` = propext, Classical.choice,
Quot.sound, SM.lp_lm; STACK_ASSEMBLY_REPORT.md). Ported verbatim (header added) as SM/Stack.lean; `lake build SM.Stack`
clean; bundle StackData byte-identical to work/drafts/Stack_statement.lean; row mapped implemented (SM.stack). Reviewer
input work/reviews/mp-stack-reviewer-input-statement.lean.txt (proof withheld, notation map attached), excerpt
sm-3:1494-1536, brief work/port/review_prompt_mp-stack.md; review launched next. Proof route as planned (PLAN_FINAL
§6): record-level restriction/smoothing commutation (restrictSmoothIso / restrictSmoothDisjointIso on first-return
maps), diagram-level block bookkeeping, initialization from P_underFirst_init and the fibrewise component count,
step by solvedR_of_skein in the block containing the switched crossing. The whole polynomial block (5 rows) took ≈ 2 h
from the design panel's launch.

## CV:lem:uniformrot review clean; docstring citation fixed — 2026-09-14 ~01:36Z

3/3 faithful, 2 refuters clean; notes non-blocking (neg_three concludes rot = −1, equivalent to |rot| = 1 with
neg_le_neg_one; Π as the erase-sum equals the sum of the positive turns under the hypotheses; α ∈ (0, π) automatic;
[NeZero c] technical). A reviewer noticed the module and field docstrings cited the printed remark as d3:283–288; it is
at d3:288–291 — corrected in CV/UniformRot.lean before acceptance (docstring only; the statement hash is recomputed by
the checker run started now, which also audits the newly mapped mp:stack and CV axiom rows).

## CV axiom rows ACCEPTED; marked-product statements fixed; CV record/homfly rows ported — 2026-09-14 ~01:43Z (pod executor)

CV:ax:homfly (CV.ax_homfly) and CV:ax:gausscode (CV.gausscode_polynomial) accepted: 6/6 lens reviews faithful, 4/4
refuters clean (raw outputs /workspace/scratch/lean_results/cv-ax-{homfly,gausscode}-round1.output; review files
work/reviews/cv-ax-homfly.json, cv-ax-gausscode.json). Item (d) of the CV:ax:gausscode scope-change record (entry
~01:24Z): every reviewer states the conclusion is strictly WEAKER than printed by the recorded F4 replacement and that
the hypotheses are faithful; the refuters checked the consumers lem:pieceintrinsic (d6:56-73), prop:chamberinv(ii)
(d1:1062-1064) and lem:silence (d1:1411-1412) and confirm they pass only through polynomial equality. Verdict
recorded in the review file. Claims verified 61/132.

Marked-product block statements FIXED: work/drafts/MarkedProducts_statement.lean (= the judge's
work/drafts/markedproducts/Statements_FINAL.lean with my edit; NOTES_FINAL.md has the clause maps and the risks R1-R9).
Executor decisions: (R1) MarkedDiagram carries the printed interval I (Arc, IsMarkedInterval) together with the record
mark it determines (comp_eq, gap_iff via Diagram.IsGapOf), so the rows quantify over exactly the printed marked
diagrams; the rows read only the record mark (the printed "finite data"). (R2) IsCleanMarkedJoin A B J :=
Nonempty (RecordIso J.record (Record.joinRecord A.μ B.μ)) — design decision D9 ("Its finite data are precise";
realizations "are compared only by lc:presentations"). (R3) mp:blocks keeps the printed existential clause
`realizes` (a JoinForest of the supplied C_H with the full record) — its proof needs the geometric existence of clean
marked joins (sm-3:1380-1425), the tracked D9 sub-obligation; `product`, `sign_preserved`, `writhe_additive` are
provable at the record level; the row stays unaccepted until `realizes` is proved, but `product` is delivered as a
library lemma for cb:products. BlockSupply.actual (IsRealizable ρ) renders "actual ... record". (R7) [z^k] rows via
the accepted zRow; 2Λ = twoLambda (mixedSignSum), an integer. (R8) lem:homflyrows class-level via LinkEquiv
representatives. Names SM.join, SM.lowest, SM.blocks, SM.homflyrows. Proof-lane design panel launched next.

CV:def:record (CV.record_definition) and CV:def:homfly (CV.homfly_definition): prover draft
work/drafts/CV_record_homfly.lean ported as CV/RecordHomfly.lean and mapped implemented. Readings: CV's record = SM
Record with one circle (SingleCircle); clauses (a)-(d) of the record isomorphism rendered literally (PreservesCyclicOrder
one-directional on VisitBetween, CarriesDoublePoints, CarriesOverUnder, signs) with the theorem that on one-component
diagrams they characterise exactly the Φ of a RecordIso (gap G13 closed via the accepted
nextVisit_comm_iff_visitBetween_iff); "extends to an orientation-preserving homeomorphism" rendered by the accepted
ExtendsToCircleMaps; the isotopy-uniqueness sentence (any two extensions isotopic) is a justification, not rendered
(no homotopy theory in scope) — flagged in the docstring for the reviewers. CV def:homfly: the two normalising
identities + uniqueness (CV.ax_homfly.unique) and the split-unknot display P(L ⊔ ○) = ((a − a⁻¹)/z) P(L) from
lp:split-circle (no kink realisation needed, gap G12 closed); CV's skein has the same convention as SM's.

## mp:stack ACCEPTED — the polynomial block (5 rows) is closed — 2026-09-14 ~01:44Z (pod executor)

3/3 lens reviews faithful, 2 refuters clean, notes non-blocking (tags 0..q−1; restrict re-indexing; the disjoint-union
sentence as an instance; split_union as a two-block partition). Review work/reviews/mp-stack.json. With lp:core,
rp:record-polynomial, lc:presentations, lp:split-circle and mp:stack accepted, every row of sm-3's polynomial block is
closed; mp:join / mp:lowest / mp:blocks / lem:homflyrows (statements fixed, work/drafts/MarkedProducts_statement.lean)
are next. Checker re-run started to audit the newly mapped CV rows (def:record, def:homfly, lem:fulltwist).

## Front-block design panel stalled and resumed — 2026-09-14 ~01:48Z

The front-block design panel (rows 73-94; launched 2026-09-13 ~23:11Z) delivered design A
(work/reports/front-block-design-A-20260913.md: PL fronts on the accepted polygonal shadows, cusps = x-reversal
vertices, over = smaller slope, S(F) relational, Rutherford words as grid PL fronts) at 23:32Z, but designer B's agent
had been blocked on a tool call since 23:33Z with no further activity. Stopped at 01:48Z and resumed from the saved run
(designer A's result cached; designer B and the judge re-run). Checker receipt of 01:46Z saved as
work/checks/dev-check-cv-rows-implemented.json (111 mapped, 15099 audited, passed); checkpoint
/workspace/scratch/lean_results/RESULT_20260914_0146Z.tgz; Discord milestone sent 01:46Z.

## CV:lem:fulltwist ACCEPTED — 2026-09-14 ~01:53Z

3/3 faithful, 2 refuters clean (review work/reviews/cv-fulltwist.json). Readings recorded in the module docstring of
CV/FullTwist.lean: one-crossing identity (T1 oriented smoothing, T2 a ReflTransGen chain of accepted RII moves from the
switched diagram), d(D) = 1 − w(D) − |rot Γ_D| via CV.rotAbs of the unique component polygon, Ω(D) = [a^{d(D)} z^0] F_D,
both only for one-component diagrams. Claims verified 63/132.

## Plan note: the rounding/floor lane waits for the front-block representation — 2026-09-14 ~01:54Z

cf:lem-rounding (sm-3:3644-3869) needs a class of C^∞ regular closed curves carrying diagrams (over/under at double
points), the smooth transition profile φ = f(t)/(f(t)+f(1−t)) (Mathlib: Real.smoothTransition / expNegInvGlue), tangent
monotonicity and flatness clauses, and the disc package; cf:lem-curl and cf:thm-carrierfloor consume it, and the
front block's rounding S(F) (ng:front-domain) needs the same smooth-diagram class. To keep one coherent smooth model,
the rounding lane's design panel is launched only after the front-block panel's FINAL report (resumed 01:48Z) fixes
the representation of fronts and their rounding.

## CV:def:record and CV:def:homfly ACCEPTED; R-lane core statements delivered — 2026-09-14 ~02:04Z (pod executor)

CV:def:record (CV.record_definition) and CV:def:homfly (CV.homfly_definition), CV/RecordHomfly.lean: 6/6 lens reviews
faithful, 4/4 refuters clean (review files work/reviews/cv-def-record.json, cv-def-homfly.json). Non-blocking notes:
the abstract circle Γ carried only through the cyclic successor on V; (a)-(d) characterise the Φ of a RecordIso on
one-component diagrams (iso_iff); the extension sentence rendered forward via ExtendsToCircleMaps; the
isotopy-uniqueness sentence not rendered (justification); the third HOMFLY identity rendered as a claim, not via the
printed kink route. Checklist 111/192 (definition rows; claims verified unchanged at 63/132).

R-lane cores: the statement panel's judge delivered work/drafts/rlane/Statements_FINAL.lean (1085 lines; bundles
LocalizationData (12 fields), ParityData (5), FibrePartitionData (8), GenericTableData (19); rows stated on CV's locus
per F2(A) as `E.IsSimpleRIII e f g … → ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ <Row>Data E e f g δ`; abstract skeleton tables
proved by decide; isSimpleRIII_eventOfTriple proved from Bridge B2/B3 and localization_of_tripleAt proved from the row)
and NOTES_FINAL.md (clause maps, ten fidelity risks, unit split). Executor decisions: (1) the optional existence remark
both_orbits_occur (R-LOC-2 corollary sentence 2, consumed by nothing) is NOT a row clause and is removed from the fixed
statement file — recorded here as out of scope; (2) the presupposition/consequence fields (LocalizationData
.triangle_crossings/.order_same_side/.interlace_same_side/.gauss_words, ParityData.triangle_card,
FibrePartitionData.avail_card) stay, to be listed in the review note; (3) state_sum_partition is the X₁-free form over
every AddCommMonoid-valued summand, the specialisation to F_± added when CV:def:X1 lands; (4) the domain question
(CV.Generic sides versus the SM.Generic Triple* lane) is exactly CV-DOM — the proof lane for these rows is launched
after the CV-DOM decision. Fixed statement: work/drafts/RLaneCores_statement.lean.

## R-lane units G1 and F1 launched ahead of the CV-DOM decision — 2026-09-14 ~02:06Z

Two units that do not depend on the carrier-lane domain question were launched on copies of
work/drafts/RLaneCores_statement.lean: G1 (the sign classification of R:generic_table — Cramer identities and the
extreme/generic/selected classification of the three triangle crossings from the guards, as standalone lemmas
RProof.G1.*) and F1 (the abstract fibre-partition engine indep_partition and the FibrePartitionData fields it yields,
RProof.F1.*). Checkpoint /workspace/scratch/lean_results/RESULT_20260914_0207Z.tgz started.

## prop:C-silent design adopted (winner B, R2 hybrid); two units launched — 2026-09-14 ~02:14Z (pod executor)

Panel: work/drafts/csilent/PLAN_{A,B,FINAL}.md, Skeleton_{A,B,FINAL}.lean. Winner B: a Carrier.MarkTransport between the
two side polygons at one side parameter (below the silent_sides radius), closed by the accepted
MarkTransport.cornerStateSum_transport; uniformity via transported vertex/smoothing turns; equal rotations by
rotationNumber_family_constant along the corner family through the centre; equal HOMFLY of the positive lifts by
lit:homfly's planar clause along the same family (Link.homfly_positiveDiagram_single_of_family) — the SAME accepted
deviation from the printed route (lc:presentations + lp:core on the two generic sides, sm-4:137-141) as prop:C-chamber
and thm:C-S3; genericity of the family off the centre from single_geo_generic, at the centre from the new
single_generic_of_weak (the centre carrier polygon is a generic one-component shadow: tail-off, transversality, no
triple point, from the printed centre facts, sm-4:118-131 — no generic-parent lemma applied at the centre). Both fixed
side parameters reduced to one by prop:C-chamber along each side. Axioms of the assembled row: standard + SM.lit_homfly.
The judge closed 11 declarations; Skeleton_FINAL.lean (1491 lines) has 2 sorries: exists_geoBlock (U3a) and
geoCornerPolygon_meet_remote_edge (U3b); both units launched on copies of the skeleton. Plan A (record-first via
SM.presentations, 22 leaves, ~1160 lines, axioms + lp_lm) judged sound but longer; kept as a cross-check design.

## CV-DOM decided: F2 mechanism = (C) on the accepted geo layer — 2026-09-14 ~02:20Z (pod executor)

**Decision (CV-DOM panel: 2 analysts + judge; reports work/drafts/cvdom/ANALYSIS_A.md, ANALYSIS_B.md,
DECISION_FINAL.md).** Decision F2 of 2026-09-13 stands: no carrier-dependent CV row, and neither CV:ax:R nor
any `RProof.*` row, is stated on a domain smaller than printed. Its mechanism is changed. The Carrier lane
(`hP : SM.Generic P`) is NOT re-parametrised — rewriting the binder of `Carrier.Component`/`owner`/
`smoothingSuccessor` would change the statement hash (Supplemental/Audit.lean `semanticDependencies`) of
≥ 18 accepted rows. Instead the accepted geometric carrier layer `SM.GeoCarrier` (SM/FlatCarriersDefs.lean,
local definitions of def:flat-carriers: `geoMarkPosition`, `geoMarkSuccessor`, `geoSmoothingSuccessor`,
`GeoComponent`, `geoOwner`, `geoComponentMarkList`, `geoComponentCornerList`, `geoCornerCount`,
`geoCornerPolygon`, `geoCornerTurn`, `geoCarrierCrossings`, `GeoIndependent`, `geoCarrierSelector`, all on
`hP : CrossingGeometry P`) is completed into a full lane by porting the Carrier lane's THEOREMS as new
modules `SM/GeoCarrier*.lean` (namespace `SM.GeoCarrier`, prefix `geo`, never redefining an accepted name),
in three hypothesis tiers: tier 0 `CrossingGeometry P` (marks, successor, carriers, count, inherited order,
noncrossing, neighbour separation, pieces, trace); tier 1 `SM.CarrierGeometry P` := `CrossingGeometry P` ∧
(∀ k e, ¬ incident k e → P k ∉ edgeSegment P e), which is CV "diagrammatic" (`CV.diagrammatic_iff`, n ≥ 3)
(self-intersections of a carrier, regular corner polygon, positive lift); tier 2 the accepted `WeakGeneric P`
(nonzero turns of the corner polygon, def:wind, selector_A). `CV.Generic → WeakGeneric → CarrierGeometry →
CrossingGeometry` and `CV.Diagrammatic → CarrierGeometry` are one-line theorems (CV/Setup.lean:1135, 1154,
1566; `diagrammatic_iff` 1630).

**Measured basis.** `hP.2` (SM G2) is used 0 times in the 37 lane files; `hP.1` 313 times, all as the Prop
argument of `markPosition/visitPosition hn hP.1`; the lane's whole mathematical dependence on `Generic` is 28
lemma sites (CarrierSelfIntersections ×13, CarrierCornerPolygon ×4, GaussVisits ×7, SegmentGeometry ×2,
Marks ×1, SmoothingDefinition ×1), each with a `CrossingGeometry`/`WeakGeneric` counterpart in the library,
plus the SM positive lift (`SM.Link.positiveLift`, on `SM.Generic`), which is re-bound at tier 1. Two
prototypes compiled: a hand port of CarrierSelfIntersections §0-§5 onto the tiers (work/drafts/cvdom/
CarrierGeometry.lean, 367 lines, exit 0, no sorry) and a zero-hand-edit mechanical port of two combinatorial
files (GeoCombinatorialSample.lean, 169 lines, exit 0, no sorry; transformer port_lane.py). A third prototype
(CV_X1_prototype.lean) states CV:def:X1 on its printed binder `hG : CV.Generic P` over the accepted geo layer
with the DEFINE-row bundle proved (exit 0; `sorry` only in the six separately-rowed places).

**Fidelity.** Every carrier-dependent CV row is stated on its printed binder: `hD : CV.Diagrammatic P` for
CV:def:smoothing (d1:355), lem:carriers (d1:362-365 "genericity is not needed here"), lem:carrierword
(d1:450-456), def:pieces (d1:514), def:piecediagram (d1:565 "diagrammatic parent"), lem:piececurve (d1:592);
`hG : CV.Generic P` for def:wind (d1:487-489), def:X1 (d1:909), selector_A (d6:1017-1020), prop:chamberinv(ii)
(d1:932-940, CV chambers); `E : CV.Event n`, `E.Silent` for lem:silence (d1:1300); `E.IsSimpleRIII` for
CV:ax:R (d10:18-24) and the `RProof.*` rows. No scope change; ordinary "same domain" reviews. CV's carriers
are read as the accepted `SM.GeoCarrier` objects through `hD.crossingGeometry` / `hG.crossingGeometry`; on
SM-generic polygons these ARE def:smoothing's objects by the accepted `geoSmoothingSuccessor_eq_generic`,
`geoComponentEquivGeneric`, `geoComponentCornerList_eq_generic` (FlatCarriersDefs.lean:638-724). The ownership
convention at a selected crossing is SM conv:selected-visits (the same `selectedMarkPerm`), a disambiguation
CV leaves implicit (cited in each review). The final theorem is unaffected: `Bridge.sm_R` evaluates `CV.X1`
only at `(Bridge.eventOfTriple hn g h).curve t`, `t ≠ 0`, which are `SM.Generic` (`WallGerm.generic_punctured`;
`CV.eventOfTriple_sides_sm_generic` in the prototype), and there `Bridge.B4` identifies `CV.X1` with the
accepted `cornerStateSum` through the agreement lemmas and the accepted `SM.C_X1` (lem:C-X1) — B4 itself is
printed on SM-generic representatives (BRIDGE.md:639), so nothing in the target chain changes domain.

**Three documented readings (not scope changes; each review must cite them):** (i) lem:carrierword's
printed generality over "a closed curve C with finitely many transverse double points" is realised on the
carriers of a diagrammatic polygon P and its refinement clause (S ⊆ S′ both independent ⇒ every carrier of
S′ lies in one carrier of S with the induced order) — the only instances the CV text consumes (lem:piececurve
Step 5 applies it to daughter carriers); (ii) def:piecediagram's "parent curve with every double point outside
H erased" is the datum (restricted word + rotation system, d1:580-590) realised by the piece curve C_H of
lem:piececurve, so `CV.pieceDiagram H` is the positive lift (divide convention = `Diagram.IsPositive`) of the
carrier of S ∪ K_H that carries H; (iii) `hn : 3 ≤ n` is carried where the geo lemmas need it (CV fixes n ≥ 3
globally, d1:932). **One form decision:** `CV.hyp_R` is stated in the printed chamber-value form — for every
simple RIII event, `X1 (E.curve t₊) = X1 (E.curve t₋)` for ALL parameters t₊ > 0 > t₋ of the event (the two
sides ARE the two chambers of the event, def:event d1:1080-1083); `RProof.cv_R` proves it from the R lane's
punctured-δ form (`RProof.cv_R_near`) and CV:prop:chamberinv(ii) (constancy of X1 along each connected side).

**Cost (judge's estimate).** ≈ 7,000-7,500 new lane lines (≈ 2,450 pure renaming, the rest binder-and-lemma
swaps), ≈ 850 positive lift, ≈ 700 agreement + B4, plus the common work every option pays (CV row bodies incl.
Gaps G3/G4 ≈ 2,000; chamberinv(ii) on CV chambers ≈ 1,300; silence ≈ 800; Triple* lemmas on CV events ≈ 700):
≈ 12,000-13,500 lines, ≈ 95 prover agent-hours (range 75-125), of which ≈ 55-60 are (C)-specific. Critical
path U0 → U1 → U2 → U4 → U6 ≈ 30 serial hours; with 5-6 provers ≈ 2-3 days wall-clock, beside (not ahead of)
the phase-2 move / cb:products / G10-G11 work the R lane waits for under every option. No accepted file is
modified. Emergency fallback if the R-lane statements must be frozen before U1-U3 land: state them
parametric in `E : CV.Event n` as already drafted (they mention X1 only as a summand), never with `hSM`.

Execution: units U0-U9 of work/drafts/cvdom/DECISION_FINAL.md §5 (≈ 95 agent-hours; rulings R1-R7 of §3 bind the provers; review notes of §4 per row). U0 launched now; U8 (CV.Event forms of the six Triple* lemmas, feeding RProof.localization) and the mechanical ports U1a/U1b follow U0.

## R-lane unit F1 delivered — same time

work/drafts/rlane/U_F1.lean (+403 lines): RProof.indep_partition proved (standard axioms) and every field of
FibrePartitionData proved as RProof.F1.<field> — decompose/compose/bijection/state_sum_partition unconditionally,
graph_on_W_same/W_to_T_same/avail_same from LocalizationData.interlace_toggle, avail_card from ParityData.trichotomy —
so R:fibre_partition follows from R:localization and R:parity (F1.fibre_partition_of_rows). Row sorry left in place for
the assembler.

## prop:C-silent unit U3b delivered — 2026-09-14 ~02:24Z

work/drafts/csilent/U3b.lean (+162 lines): geoCornerPolygon_meet_remote_edge proved (standard axioms; the hypothesis
hnv turned out unused — kept for a byte-identical statement, lint only). U3a (exists_geoBlock) still running; then the
two hunks are merged into the skeleton and SM/CSilent.lean is ported under the fixed name SM.prop_C_silent.

## prop:C-silent assembled and ported: SM/CSilent.lean — 2026-09-14 ~02:28Z (pod executor)

U3a (work/drafts/csilent/U3a.lean, +210 lines: exists_geoBlock, standard axioms) and U3b (+162 lines) merged by the
executor into work/drafts/csilent/CSilent_Assembled.lean (1861 lines, 0 sorry; header status lines updated);
`#print axioms SM.prop_C_silent` = propext, Classical.choice, Quot.sound, SM.lit_homfly. Ported verbatim (header
added, the trailing #print stripped) as SM/CSilent.lean; `lake build SM.CSilent` clean; bundle CSilentData
byte-identical to work/drafts/CSilent_statement.lean; row mapped implemented under the fixed name SM.prop_C_silent.
Reviewer input work/reviews/prop-C-silent-reviewer-input-statement.lean.txt (proof withheld, notation map attached),
excerpt sm-4:101-105, brief work/port/review_prompt_prop-C-silent.md; review (3 lenses + 2 refuters) launched; checker
started. The whole row (statement → design panel → two units → assembly) took ≈ 1 h 25 min.

## R-lane unit G1 delivered; G2 launched — 2026-09-14 ~02:29Z

work/drafts/rlane/U_G1.lean (+807 lines, standard axioms): all eleven sign-classification fields of GenericTableData
proved as RProof.G1.* (radius structure G1.GoodRadius from the event's sign changes and guardconst; Cramer identities
from G4_factorization and the G4 = ±G3 identities; edges_iff directly from traversal keys, needing no radius or
adjacency; branch_count / selected_unique by decide). Remaining fields (local_word, canonical_words, local_supports,
local_undominated, mask_sharpening) → unit G2 (launched on a copy of U_G1.lean; may assume LocalizationData /
ParityData as hypotheses).

## CV-DOM unit U0 ported; U1a, U1b, U7a launched — 2026-09-14 ~02:34Z

work/drafts/cvdom/U0/ (report REPORT.md): SM/GeoCarrierGeometry.lean (277 lines; SM.CarrierGeometry = CrossingGeometry
+ vertex off non-incident closed edges — tier 1 = CV "diagrammatic"; ofWeak / ofGeneric / regular /
adjacent_edges_meet / edge_ne_zero / vertex_not_mem_edge / vertex_ne_edgePoint; cg_vertex_not_mem_edgeInterior,
cg_crossingPoint_ne_vertex) and CV/CarrierBridges.lean (CarrierGeometry.ofDiagrammatic / ofCV,
carrierGeometry_iff_diagrammatic, CV.mem_Ind_iff_geoIndependent, mem_N_iff, mem_U_iff) ported as library modules
(headers added; `lake build` clean; standard axioms). Finding: with adjacent_edges_meet and regular, the whole
"adjacent original edges" group of the lane is tier 1; only turn ≠ 0 at vertex corners stays tier 2 (ruling R4
confirmed). Launched: U1a (SM/GeoCarrierCount: the count |S|+1 and the combinatorial core), U1b (SM/GeoCarrierOrder:
inherited order, traced successor, segment geometry), U7a (CV/Carriers: rows CV:def:smoothing, def:wind, def:pieces on
their printed binders).

## Front block: representation adopted (FINAL = B + grafts); fidelity risks FR-1..FR-7 recorded; scope gaps — 2026-09-14 ~02:38Z (pod executor)

Panel (resumed after designer B stalled): work/reports/front-block-design-A-20260913.md, -B-, -FINAL-20260913.md
(+ sketch file). Adopted: row 73 (ng:front-domain) on the printed SMOOTH class `SmoothFront` (C^∞ 1-periodic loops;
cusps = zeros of γ' with det(γ'', γ''') ≠ 0 and x'' ≠ 0, down iff x''·det < 0; over = smaller dz/dx; D, w, s from the
finite sets); the rounding S(F) = clean-disc cusp replacement (`GeomRounding`) to a cusp-free smooth G read polygonally
through a named-record `Marking` on a `Diagram`; the certificate rows 77-82 and ng:finite-word on oriented Rutherford
words realized as grid PL fronts (design A's PL class, a Diagram); 83/93 via a Moves/Chain/Laws descent; the smooth
front → word representation (76b) is the single bridge, attempted last. Module plan: FINAL §11. Effort: plannable core
≈ 13k lines (95-110 agent-hours), 76b 7.5-11k, total ≈ 28k.

Fidelity risks recorded before row 73 is stated (verbatim from FINAL §9):

- **FR-1 (polygonal reading of S(F)).** Printed: "The resulting ordinary diagram is denoted S(F)" — a smooth
  cusp-free curve. Lean: `S` is a polygonal `Diagram` carrying the named record (`Marking`) of the cusp-free smooth
  front `G` produced by the literal clean-disc replacement (`GeomRounding`). This is the accepted layer's reading of
  every diagram (def:positive-lift row; sm-3:337-343 "a diagram here is a finite polygonal immersion, or a regular
  smooth immersion ..."; lem:gauss-pl-model "the crossing names, the four-ray orders, the traversal direction and
  the over/under designations are retained"). Consumers see only `P S`, which depends on the record alone
  (rp:record-polynomial, accepted). Must be cited in the row docstring and in each review of 73, 74, 83, 93.
- **FR-2 (cusp criterion in derivative form).** "Ordinary semicubical cusp ... in a semicubical parameter u ...
  x''(0) ≠ 0" is rendered as `deriv = 0 → det(γ'', γ''') ≠ 0 ∧ (γ'').1 ≠ 0` at the cusp parameter, and "traversed
  from its locally upper arm to its locally lower arm" as `x''·det(γ'', γ''') < 0`. Both are the standard unpacking
  (Bruce–Giblin) and are checked on the printed exact germ (`8A²`, `2A`, `16A³`, proved), but the equivalence with
  the (u², u³) normal form and the geometric upper/lower reading are not proved in Lean (an optional ~500-line Taylor
  lemma can supply the latter).
- **FR-3 (smoothness and parametrization).** "smooth" = `C^∞`; a parameter circle = a 1-periodic map of `ℝ`; "an
  actual map" is a parametrized map, and the record (occurrences, cyclic order) is read on the parameters.
- **FR-4 (parametrized rounding).** `GeomRounding` keeps the parameter circles of `F` and replaces `F` only on open
  intervals `I c` around the cusp parameters; "same oriented attachments" is thereby literal. A rounding in a
  different parametrization is covered because `Marking` is parametrization-free — the two readings agree on
  `P S`.
- **FR-5 (the PL/word layer is a proof device).** Rows 77-82 and ng:finite-word are stated on oriented Rutherford
  words and their grid PL realizations, as the printed certificate section is ("Use Rutherford's elementary front
  words"; "For an actual finite front word"). Rows 73, 74, 83, 93 are on the smooth class. The transfer is one named
  statement (`ng_commutation_word_statement`, the second sentence of ng:commutation). Rutherford's letters are
  unoriented; the direction bits quantify over *all* consistent orientations ("The permitted orientations need not
  produce a single component"), and the typing forces the printed orientation facts rather than assuming them.
- **FR-6 (ng:finite-word transcription).** Listed in risk 4. Plus: the axiom quantifies over closed oriented words
  only (no words with free ends), the base is `IsStandardCircles` of the realization (unions allowed, nesting
  allowed), and `Chain` encodes "stop at the first strict decrease of s or at the base" with `s` non-increasing
  before it as a *consequence* of the `Laws` (pres_s, skein_s), not as an axiom clause.
- **FR-7 (scope gaps, for rows 89-91, 94).** GAP-1 and GAP-2 of section 8, with the D2 citation
  (`LinkInterfaces.lean` header; `HomflyClauses.descent` over `LinkEquiv`).

Executor decisions (AUTONOMOUS_EXECUTION; nobody to ask): (D-F1) the FINAL representation is adopted; every review of
rows 73, 74, 83, 93 cites FR-1 (polygonal reading of S(F)) and FR-2. (D-F2) lanes: α = rows 73 + 74 (SM/FrontSmooth,
FrontRecordBridge); β = PL layer + oriented words + grid realization, then ng:front-III/II/I, then 80-82, 76a on words,
the ng:finite-word statement (independent review before any consumer), 83 on words, 93; 76b last. (D-F3) GAP-2:
cp:finite-contact-path (91) and hence fd:contact (94) derive polynomial equality from an AMBIENT ISOTOPY, while the
accepted lit:homfly descent clause is over LinkEquiv (design D2; Reidemeister's theorem outside scope); with the five
literature interfaces frozen, rows 89-91 and 94 will be STATED faithfully (after the smooth spatial vocabulary of 92
exists) and left unproved as a documented scope gap — no new interface, no narrowing. Consequence, recorded now: the
chain fd:contact → cf:thm-carrierfloor → thm:floor → cb:singleton → lem:corner-values → thm:C-soft / thm:C-S7 →
thm:comparison → cor:C-inherits → SM:corner_laws_and_soft cannot be closed under the frozen interfaces; the four
target rows thm:C-soft, thm:C-S7, thm:comparison, cor:C-inherits and the final obligation stay open unless Reidemeister's
theorem (ambient isotopy ⇒ LinkEquiv) is formalized or a policy change admits a spatial-isotopy descent clause. The
final report will list this stage as incomplete with this reason; Mark is informed at the next milestone. (D-F4) rows
84-88 (Moser neighbourhood, parameter avoidance, Hamiltonian flows, generic front, Gauss linking): statements when the
vocabulary exists; proofs (≥ 30k lines of analysis) are not planned within the horizon — recorded as open. (D-F5) the
reachable targets are prop:C-chamber ✓, thm:C-S3 ✓, thm:C-S5 ✓, prop:C-silent (under review); effort goes to the
ng rows, the marked products, the CV-DOM lane, the R lane, Bridge B4 and Bridge:theorem.

## prop:C-silent ACCEPTED — fourth target row — 2026-09-14 ~02:40Z (pod executor)

3/3 lens reviews faithful, 2 refuters clean, notes non-blocking (review work/reviews/prop-C-silent.json). Targets 4/8:
prop:C-chamber, thm:C-S3, thm:C-S5, prop:C-silent. The remaining four targets (thm:C-soft, thm:C-S7, thm:comparison,
cor:C-inherits) depend on the floor chain through fd:contact and the scope gap GAP-2 (entry ~02:40Z).

## R-lane unit P1 delivered — 2026-09-14 ~02:44Z

work/drafts/rlane/U_P1.lean (+673 lines, standard axioms): all five ParityData fields proved as RProof.P1.* from
LocalizationData (triangle_crossings, adjacent, interlace_toggle) via a polygon-level core on CrossingGeometry (the
two-colouring argument of R-PAR-v6: Col / col_of_adjacent / interlaces_iff_col / three_xor_cases; avail commutes with
crossingTransport given the toggle). With F1 (fibre partition from localization + parity) and G1 (sign classification),
the R-lane cores now reduce to R:localization (units L1-L3, after CV-DOM U8 supplies the triple lemmas on CV events)
and the remaining word fields of R:generic_table (G2 running).

## R-lane unit G2 delivered — the four cores reduce to R:localization — 2026-09-14 ~02:50Z

work/drafts/rlane/U_G2.lean (+739 lines on top of U_G1, standard axioms): local_word (from the sortedness of
geometricGaussList and the key order of the six triangle visits; the cyclic case as a rotation), canonical_words,
local_supports, local_undominated (from G1.GoodRadius) and mask_sharpening (from ParityData alone) proved; the test
assembly G2.genericTableData discharges all 19 fields, and G2.generic_table_of_parity closes the row from R:parity.
Chain of the R-lane cores: R:localization (units L1-L3 after CV-DOM U8) → R:parity (P1.parityData) → R:fibre_partition
(F1.fibre_partition_of_rows) and R:generic_table (G2.generic_table_of_parity). Assembly: merge the F1, P1, G2
insertions and the localization proof into one RProof module.

## CV-DOM unit U1a ported: SM/GeoCarrierCount.lean — 2026-09-14 ~02:51Z

work/drafts/cvdom/U1a/GeoCarrierCount.lean (1,792 lines; 95 declarations ported mechanically with proofs verbatim, 43
dropped because the accepted geo* counterpart exists, tier 0 throughout; REPORT.md) ported as a library module and
built. Targets: geoComponent_card (count |S| + 1 on CrossingGeometry), geo_selected_visits_separated,
geoOwner_refines (new proof), GeoInheritsMarkOrder / geoInheritsMarkOrder_of_independent, geoComponentCycle. Because
the count needs the inherited-order invariant, U1a also ported the CarrierInheritedOrder / InheritedInsert /
IndependentOrder / SameArc / MarkedArcLists files assigned to U1b; U1b was told to import SM.GeoCarrierCount and drop
its duplicates. Six CV-free copies of CV/Events' geometric-interlacement lemmas were made (swappable for an import).

## CV-DOM unit U8 ported: CV/TripleEvents.lean — 2026-09-14 ~02:57Z

work/drafts/cvdom/U8/CVTripleEvents.lean (1,052 lines, 0 sorry, standard axioms; REPORT.md) ported as a library module
and built: on a CV simple RIII event the crossing set is constant on the WHOLE interval (centre included; the four
unconditional G2 members are off Z, so every Crosses activation is constant by guardconst), the three bundle pairs are
crossings, their parameter orders reverse across the wall (TriangleCrossParamExchanges ↔ SM.TriangleOrderExchanges),
other orders persist, the Gauss-word form ExactTriangleVisitOrders, the empty-arc adjacency (CV.EmptyArcAdjacent =
RProof.AdjacentVisits' body) with the one-directional bridge from SM.VisitsAdjacent (the converse fails at the cut),
interlace_same_side, and the bundle CV.Event.TripleEventData — no δ needed anywhere; no tier-1 hypothesis needed; no
restated lemma is false on CV events (geometric_edgeParameters_ne replaces generic_edgeParameters_ne). A consumer check
shows 8 of the 10 LocalizationData fields discharge with δ := E.radius; interlace_toggle and complement_on_triangle
remain (unit L, launched next).

## CV-DOM unit U1b ported: SM/GeoCarrierOrder.lean — 2026-09-14 ~02:58Z

work/drafts/cvdom/U1b/GeoCarrierOrder.lean (231 lines on top of GeoCarrierCount after de-duplication; standard axioms;
REPORT.md): geoTracedSuccessor_of_independent, geoCarrierSpec_of_independent (via the accepted GeoCarrierSpec.of_core),
geoComponentCycle_eq_filter, geo_closed_trace, the smoothing-segment residue (zero/one/glue/continuity/length_pos/
injective). Shape deviations recorded: geoInheritsMarkOrder_of_independent takes no hn;
geoSmoothingSegment_mem_edgeSegment is the accepted FlatCarriers.lean:1466 form. Launched: U2a (GeoCarrierCrossings +
Noncrossing), U2b (GeoCornerPolygon), and the R-lane localization unit L on CV/TripleEvents.

## ng:front-domain (row 73) ported and under review; α2 and the rounding lane launched — 2026-09-14 ~03:05Z (pod executor)

Unit α1 delivered work/drafts/front/FrontSmooth.lean (1,338 lines, sorry-free; ALPHA1_REPORT.md): the smooth front
class SmoothFront (C^∞ 1-periodic loops; cusps in derivative form per FR-2; over = smaller dz/dx; D, w, s; Marking =
a polygonal Diagram carrying the named record; GeomRounding = the clean-disc cusp replacement; IsRounding), the exact
germ lemmas and the defect. Ported as SM/FrontSmooth.lean. EXECUTOR EDIT before review: the DEFINE-row bundle
FrontDomainDefinitionData had three fields with no counterpart in the printed definition sm-3:1825-1841 —
over_first_sign (a sign-rule sanity fact), germ (the exact germ of cp:finite-contact-path, sm-3:3218) and defect (the
defect belongs to ng:local-front-bound) — removed from the bundle (the lemmas stay in the module as library material
for later rows); 18 fields remain, one per printed clause. Rebuilt, row mapped implemented (SM.front_domain_definition),
reviewer input work/reviews/ng-front-domain-reviewer-input-statement.lean.txt, excerpt sm-3:1825-1841, brief
work/port/review_prompt_ng-front-domain.md (cites FR-1..FR-4); review launched. Launched: α2 (row 74
ng:smoothing-record on SM.FrontSmooth) and the rounding-lane design panel for cf:lem-rounding (row 97; output
work/drafts/rounding/: statement candidates + PLAN_FINAL + Skeleton_FINAL on the shared smooth model).

## CV-DOM unit U7a ported: CV/Carriers.lean (rows CV:def:smoothing, def:wind, def:pieces) — 2026-09-14 ~03:09Z (pod executor)

work/drafts/cvdom/U7a/CVCarriers.lean (831 lines, sorry-free, standard axioms; REPORT.md) ported as CV/Carriers.lean
and built; rows mapped implemented: CV:def:smoothing → CV.smoothing_definition (binder hD : Diagrammatic P, S ∈ Ind),
CV:def:wind → CV.wind_definition (binder hG : Generic P), CV:def:pieces → CV.pieces_definition (hD) — the PRINTED
binders, no domain change (CV-DOM decision). Finding: no tier-2 field waits for U2b — the accepted tier-0
geoCornerPolygon_turn_eq_sign plus CV's (G1)/(G5) give the turn facts once TracedSuccessor (U1b) is known. The printed
def:wind counterexample ((0,0),(1,0),(2,0),(0,1)) is formalised (flatExample: Diagrammatic, turn at p₂ = 0, not
Generic). Reviewer input work/reviews/cv-carriers-reviewer-input-statement.lean.txt (the three row proofs withheld),
excerpts d1:355-361 / 487-513 / 514-521, brief work/port/review_prompt_cv-carriers.md; review launched.

## Marked-product proof lane adopted (winner B + grafts); six units launched — same time

Panel: work/drafts/markedproducts/PLAN_{A,B,FINAL}.md, Skeleton_{A,B,FINAL}.lean (FINAL: 1616 lines, 13 sorries; the
four row theorems proved from the chain; bundles byte-identical to MarkedProducts_statement.lean; the judge closed 9
lemmas). Routes: mp:join by two nested record-level (N, b) inductions (skein_induction_based) with the join quantified
in the predicate, base = the join of two marked-first UNDER-first based orders is UNDER-first, step = joinRecord_switch_inl
/ exists_joinRecord_smooth_inl at the record level; mp:lowest = the weight a^{2Λ}[z^{1−c}]P is invariant under mixed
switches (P_support of the (c−1)-component smoothing), induction on the wrong mixed crossings down to BlockOrdered D id,
then SM.stack with singleton blocks and zero_link.over_constant (Λ = 0) and the row extraction; lem:homflyrows from
join_value / SM.stack.split_union / two_component_row + P_eq_homfly + homfly_descent + CV.ax_homfly.knot_parity.
DECISIVE FINDING on mp:blocks.realizes (the D9 obligation): since IsCleanMarkedJoin is record-level and JoinForest
allows any marks, the ROOT node is the supplied actual diagram itself (BlockSupply.actual) and every internal node is a
realization of restrictCrossings obtained by SMOOTHING AWAY the other blocks' crossings inside an actual realization
(accepted geometry only) — the printed planar construction sm-3:1387-1425 and Architect A's ≥ 1500-line
exists_cleanMarkedJoin are NOT needed; the block's only geometry is exists_markedInterval_of_mark (a clean disc around an
interior edge point). realizes lane R1-R4 ≈ 1.9-2.5k lines; product follows realizes (as printed). Units launched: U-L
(row algebra), U-J5 (first-return perm lemmas), U-J3 (join init), U-J4a (RecordIso.ofOcc), U-B2 (sign bijection), U-R1
(the geometric marked interval); then U-J4b, U-R2, U-R3a/b, U-R4.

## Marked products: U-J4a delivered; U-J4b launched — 2026-09-14 ~03:15Z

work/drafts/markedproducts/U_J4a.lean (+151 lines, standard axioms): RecordIso.ofOcc (a RecordIso from an occurrence
bijection commuting with succ/pair/isOver/sgn plus a bijection of the crossing-free circles), the counting variant
ofOccOfCard / nonempty_of_occ (equal component counts suffice), spec lemmas. U-J4b (exists_joinRecord_smooth_inl, the
critical path of mp:join) launched on a copy of U_J4a.lean; U-R3b and U-R2 follow U-R3a / U-J5. Checker of 03:10Z
passed (116 mapped, 15874 audited; receipt work/checks/dev-check-front73-cvcarriers-implemented.json).

## CV-DOM unit U2b ported: SM/GeoCornerPolygon.lean — 2026-09-14 ~03:16Z

work/drafts/cvdom/U2b/GeoCornerPolygon.lean (828 lines, 39 theorems, standard axioms; REPORT.md) ported and built:
geoCornerPolygon_edge_smul / _trace / _turn_vertex / _turn_visit(_twin) at tier 0; geoCornerPolygon_regular and
three_le_geoCornerCount at TIER 1 (CarrierGeometry — better than §5's tier-2 shape, provided as a corollary);
geoCornerPolygon_turn_ne_zero / geoCornerTurn_ne_zero at tier 2 (WeakGeneric); the actual corner block port and
geoCornerPolygon_block (8 clauses). Ruling R4 confirmed by compiled proof; U4's positive lift can be stated on
CarrierGeometry. Next: U2c (self-intersections) after U2a; U3 (GeoCarriersLemma bundle mirror) and U4 (geo positive
lift) after U2c.

## CV-DOM unit U2a ported: SM/GeoCarrierCrossings.lean, SM/GeoCarrierNoncrossing.lean — 2026-09-14 ~03:17Z

work/drafts/cvdom/U2a/ (686 + 410 lines, 62 declarations, all tier 0, standard axioms; REPORT.md) ported and built:
geo_noncrossing, geo_neighbor_visits_separated, geo_nonneighbor_visits_together (textually the accepted
CarriersLemmaData fields under owner ↦ geoOwner, visitPosition ↦ geometricVisitPosition), the retained-crossing
counting lemmas (∑ m_Q = |U(S)|), and the SM-side geoSupportNeighbors / geoSupportUnselected (= CV.N / CV.U by rfl,
so U7b can state lem:carriers on CV.N / CV.U directly). Launched: U2c (self-intersections at tier 1) and U7b
(CV:lem:carriers on its printed Diagrammatic binder).

## R:localization PROVED (unit L); R-lane cores assembler launched; marked-products U-R4 delivered — 2026-09-14 ~03:18Z

work/drafts/rlane/U_L.lean (+349 lines, standard axioms): RProof.localization proved with δ = E.radius — eight fields
from CV/TripleEvents (IsSimpleRIII.tripleEventData), interlace_toggle and complement_on_triangle from
ExactTriangleVisitOrders via the interlacement-as-Xor-of-cyclic-orders characterisation (only the bundle pair's key
comparison reverses; a pure-real toggle lemma). All four R-lane cores now close: the assembler merges U_L + U_P1 + U_F1
+ U_G2 and closes parity / fibre_partition / generic_table by the delivered compositions → RProof/Cores.lean.
Marked products: U-R4 (work/drafts/markedproducts/U_R4.lean, +132 lines) proves exists_joinForest_of_realizable from
the R1-R3 statements as they stand (strong induction on the number of blocks inside S; the node is the given
realization; sorryAx only via R1-R3).

## Marked products: U-L delivered — mp:lowest closed inside the skeleton — 2026-09-14 ~03:20Z

work/drafts/markedproducts/U_L.lean (+151 lines, standard axioms): mixedSignSum_switch_of_not_mem / _of_mem and
twoLambda_switch proved (termwise sums, modeled on Record.sum_sgn_switch; helper eq_over_under_of_crossing_eq). With
them SM.lowest is sorry-free within the skeleton (axioms standard + lp_lm); SM.homflyrows waits only on mp:join's
connected_sum. Remaining marked-product units in flight: U-J5, U-J3, U-J4b, U-B2, U-R1, U-R3a; then U-R2, U-R3b.
Review brief for the R-lane cores written ahead of assembly: work/port/review_prompt_rlane-cores.md (sources: the RA
statements and R_ASSEMBLY_SPEC.md, excerpted into work/reviews/rlane-*).

## Marked products: U-B2 delivered — sign_preserved closed — 2026-09-14 ~03:20Z

work/drafts/markedproducts/U_B2.lean (+159 lines, standard axioms): IsCleanMarkedJoin.crossingEquiv (a sign-preserving
crossing bijection from the RecordIso with joinRecord, bypassing Record.Crossing) and joinForest_sign (JoinForest
induction with Σ-set equivalences) proved; BlocksData.sign_preserved is sorry-free. In flight: U-J5, U-J3, U-J4b, U-R1,
U-R3a; then U-R2, U-R3b.

## Marked products: U-J5 delivered; U-R2 launched — 2026-09-14 ~03:23Z

work/drafts/markedproducts/U_J5.lean (+225 lines, standard axioms): firstReturn_mul_swap_of_lastKeep_some / _none proved
(helpers lastKeep_some_spec, firstReturn_mul_swap_apply_of_avoid — generic Equiv.Perm lemmas, candidates for the
accepted layer next to firstReturn_mul_swap). U-R2 (isRealizable_restrictCrossings_of_gapContiguous — the smoothing-away
invariant inside an actual realization) launched on a copy of U_J5.lean. In flight: U-J3, U-J4b, U-R1, U-R2, U-R3a;
then U-R3b.

## ng:front-domain review round 1: NOT FAITHFUL (rounding clause empty) — fix unit launched — 2026-09-14 ~03:27Z (pod executor)

Review (raw /workspace/scratch/lean_results/ng-front-domain-round1.output): the front class clauses (a)-(j) judged
faithful by all three lenses (C^∞ reading FR-3, derivative-form cusp criterion FR-2 verified reparametrization-invariant,
sign rule for downward cusps checked independently), but clause (k) — the rounding S(F) — is NOT: two kernel-checked
defects (reviewers' scratch proofs under /workspace/scratch/review_ng_front_domain/ and
/workspace/scratch/refuter_ng_front_domain/): (A) Rounding.G was typed SmoothFront with CuspFree, unsatisfiable by Rolle
(no_vertical on a 1-periodic loop forces a cusp), whereas the printed S(F) is an ordinary diagram with no nonverticality
clause; (B) GeomRounding.clean used the open interval I c, so F(a c) ∈ U c had no admissible preimage — GeomRounding
empty for every cusped front. Also weaker than printed: clean did not require F's arc inside the disc nor F ∩ U c to be a
single arc. Decision: the rounding notions are repaired (GeomRounding with stored endpoints, CLOSED-interval clean,
arc_in, arc_simple, target G : Fin c → SmoothLoop; Rounding = ⟨G, geom, marking : F.Marking S⟩ — the record of S(F) is
F's own named record since the rounded curve agrees with F at every double point and creates none), the bundle's
rounding fields restated, the row re-reviewed (round 2). The row stays implemented (unaccepted). Unit α2 (row 74) was
told to rebase on the repaired module. Lesson recorded: definitions introduced by a DEFINE row must come with a
non-vacuity check when their existence is asserted elsewhere; the front lane will add an explicit rounding existence
lemma when 76b lands.

## R-lane cores ASSEMBLED and ported (RProof/Cores.lean); front β1 ported; marked-products U-R1, U-J3 delivered — 2026-09-14 ~03:30Z (pod executor)

R lane: the assembler merged U_L + U_P1 + U_F1 + U_G2 into work/drafts/rlane/RLaneCores_Assembled.lean (4051 lines, 0 sorry,
no warnings; ASSEMBLY_REPORT.md; the four bundles and row signatures md5-identical to RLaneCores_statement.lean; the
rows parity / fibre_partition / generic_table closed by P1.parityData, F1.fibre_partition_of_rows,
G2.generic_table_of_parity from RProof.localization; axioms of all four: propext, Classical.choice, Quot.sound — no
literature axiom). Ported as RProof/Cores.lean (module RProof.Cores; the lakefile glob RProof.+ covers it; imports
CV.TripleEvents), built; rows mapped implemented under the FIXED names RProof.localization / parity / fibre_partition /
generic_table; reviewer input work/reviews/rlane-cores-reviewer-input-statement.lean.txt (the four row proofs withheld),
sources excerpted (RA statements + R_ASSEMBLY_SPEC), brief work/port/review_prompt_rlane-cores.md; review launched
(3 lenses + 2 refuters per row, the refuters told to check non-vacuity of the event hypotheses); checker started for
the hashes. This is the first delivery of the R lane (4 of 13 obligation rows); the other nine need CV:def:X1 (CV-DOM
U7c) and the carrier layer.
Front lane β1: work/drafts/front/FrontPL.lean (560) and FrontWords.lean (1238) ported as SM/FrontPL.lean and
SM/FrontWords.lean (library modules; no axiom declared; BETA1_REPORT.md). Findings recorded: design A's IsDownCusp was
wrong at right cusps (fixed with the x-side factor, literal arm-height reading proved); IsComm via strand footprints with
the two-strand shift; the cusp-skein bits derived from the printed (t,u) definitions and the printed table reproduced by
decide; right-cusp skein templates excluded (the axiom cites ng:cusp-words + reflection only) — open item for the
ng:finite-word statement; FINAL's example word l₁l₂r₁r₂ is not typed (the intended zigzag is l₁l₂r₁r₁). β2 (grid
realization + shared grid geometry) launched.
Marked products: U-R1 (work/drafts/markedproducts/U_R1.lean, +491 lines) proves exists_markedInterval_of_mark — the
block's only geometric lemma — via a clean disc around a nonsingular interior edge point (EdgeDisc: clearance radius as
in Smoothing.lean §1); U-J3 (+347 lines) proves exists_rUnderFirst_joinRecord with Architect B's RBasing.join witness. In
flight: U-J4b, U-R2, U-R3a; then U-R3b; then assembly.

## CV-DOM unit U7b ported: CV/CarriersLemma.lean (CV:lem:carriers) — 2026-09-14 ~03:33Z

work/drafts/cvdom/U7b/CVCarriersLemma.lean (451 lines, standard axioms; REPORT.md) ported and built; row CV:lem:carriers
mapped implemented (CV.carriers; binder hD : Diagrammatic P as printed, d1:363-365). Clause (iv) (every piece on one
carrier — gap G3 of the cv-lane plan) proved by a walk induction in the residual graph. Reviewer input, excerpt
d1:362-383, brief work/port/review_prompt_cv-lem-carriers.md; review launched next. Unit U7b2 launched for
CV:lem:carrierword (137) and CV:selector_A (164). Checker receipt work/checks/dev-check-rlane-cores-implemented.json
(120 mapped, 16511 audited, passed).

## CV:def:smoothing, def:wind, def:pieces ACCEPTED; U2c ported; U3, U4 launched — 2026-09-14 ~03:36Z (pod executor)

The three CV carrier definition rows (CV/Carriers.lean, CV-DOM U7a): 9/9 lens reviews faithful, 6/6 refuters clean
(review files work/reviews/cv-def-{smoothing,wind,pieces}.json; raw outputs /workspace/scratch/lean_results/cv-def-*-round1.output).
Notes non-blocking: noncrossing_arcs renders "do not cross" by the opposite nonzero turning signs at the site (the
pairing is fixed by reconnect_selected + oriented_arcs) — to be redocumented at the next layer rebuild; local ∀ hn
quantifications; the printed def:wind counterexample formalised as a field; excerpt range 514-521 vs definition
514-520. First CV rows stated on their printed binders through the geo layer — the CV-DOM mechanism works end to end.
Checklist 115/192.
CV-DOM: U2c (work/drafts/cvdom/U2c/GeoCarrierSelfIntersections.lean, 869 lines, 40 declarations, standard axioms)
ported as SM/GeoCarrierSelfIntersections.lean: geo_self_intersections at TIER 1 (character-for-character the accepted
self_intersections field under the geo renaming), plus the agreement lemmas with the accepted lane; ruling R4 held
(no tier-2 site remained). Launched: U3 (GeoCarriersLemma / GeoSmoothingData / geoWind mirrors) and U4
(geoPositiveLift at tier 1 with the agreement with positiveLift on SM-generic polygons).

## Front α2 (ng:smoothing-record) delivered modulo the row-73 repair — 2026-09-14 ~03:41Z

work/drafts/front/FrontRecordBridge.lean (581 lines, clean against the current library; ALPHA2_REPORT.md): the
justification lemmas for the corrected clean-disc replacement (CleanReplacement mirror: creates no crossing, changes
no successor, germs / slopes / crossing signs unchanged via Filter.EventuallyEq.deriv_eq), Marking.recordIso (two
markings of F compose to a RecordIso), P_eq_of_markings / defect_eq_of_markings; the row bundle SmoothingRecordData
(14 fields) and theorem ng_smoothing_record in FrontRecordBridge_row_v2.lean, to be appended once the repaired
FrontSmooth (v2) is ported (a mock test compiles with axioms standard + lp_lm). The unit independently found the same
GeomRounding emptiness (GeomRounding.false_of_cusp, kernel-checked) as the row-73 review. Rebase on my signal after the
v2 port.

## Marked products: U-J4b delivered — mp:join closes — 2026-09-14 ~03:42Z

work/drafts/markedproducts/U_J4b.lean (+241 lines): exists_joinRecord_smooth_inl proved (witness μ₁.smoothMark a; all
rewriting at the level of permutations of α ⊕ β; the conjugation gapSwap ∘ swap = swap ∘ gapSwap(mapped gap); the heart
firstReturn_sumCongr_gapSwap_swap_val via the U-J5 lemmas; RecordIso.nonempty_of_occ with the component count) —
sorryAx only through the U-J5 statements, which are proved in U_J5.lean. With U-J3, U-J5, U-J4a, U-J4b, U-L, U-B2, U-R1,
U-R4 delivered, mp:join, mp:lowest, lem:homflyrows and the sign/writhe clauses of mp:blocks are closed inside the
skeleton; realizes/product wait for U-R2 and U-R3b (running). Assembly follows.

## Marked products: U-R2 delivered — 2026-09-14 ~03:45Z

work/drafts/markedproducts/U_R2.lean (+295 lines, standard axioms): isRealizable_restrictCrossings_of_gapContiguous proved
by a simpler invariant than the judge's (every retained point other than the base has a retained successor; smoothing
any unretained crossing preserves it; two permutations agreeing off one point are equal, so the first returns coincide
without orbit computations; realizability through the accepted smoothing gate transported by RecordIso.smooth; base
case by Diagram.isRealizable_restrict). One new helper definition Record.onePred (invariant carrier), flagged for the
assembler. Only U-R3b (join decomposition) remains before the marked-product assembly.

## ng:front-domain repaired and re-ported; round-2 review launched — 2026-09-14 ~03:48Z (pod executor)

work/drafts/front/FrontSmooth_v2.lean (1711 lines, 0 sorry, standard axioms) ported over SM/FrontSmooth.lean and built.
Repair: GeomRounding stores the endpoints a c < cusp < b c (b − a < 1), clean on the CLOSED interval, arc_in (F's closed
arc in the disc), arc_simple (F meets the disc in that single embedded arc — on the CLOSED arc, the prover's deliberate
choice, accepted by the executor: with the open arc a double point at the arc's end points would be allowed and "clean
cusp disc" would be under-specified), inside / regular / simple / no_crossing / agree on the open arc, target loops
G : Fin c → SmoothLoop; Rounding S = ⟨G, geom, marking : F.Marking S⟩ (the record of S(F) is F's own named record —
justified in the module: the rounded curves agree with F, with velocities, at every double point and create none:
isDouble_iff, deriv_eq_of_isDouble, regular_everywhere, transverse, no_triple; SmoothFront.not_cuspFree documents the
Rolle obstruction to the old typing). Bundle now 20 fields (new: rounding_no_crossing, rounding_ordinary for "no
crossing" / "the resulting ordinary diagram"). Reviewer input regenerated; brief updated with the round-2 specifics;
round-2 review launched. Unit α2 (row 74) told to rebase its draft (removed names listed in the fix report).

## CV:lem:carriers review round 1: NOT FAITHFUL on clause (ii) — repaired; U7b2 ported — 2026-09-14 ~03:53Z (pod executor)

Review (raw /workspace/scratch/lean_results/cv-lem-carriers-round1.output): setup, (i), (iii), (iv) and the binder
exact; clause (ii) BLOCKING — the noncrossing field quantified over crossing visits only, while the printed clause
ranges over four points of Γ (at least all marks of the accepted finite model, vertex marks included; the module
already proved the mark-level form carriers_noncrossing_marks). Repair: the field now quantifies over Mark P with
geoMarkPosition, "preimage of an element of S" = a visit of a selected crossing (four conjuncts), proof from
carriers_noncrossing_marks (which needs no exclusion at all); docstring citation 362-378 → 362-383. Rebuilt; reviewer
input regenerated; brief updated (round 2: the residual gap for unmarked interior edge points is inherent in the
accepted finite model of def:smoothing and judged non-blocking by all round-1 reviewers). Round-2 review next.
CV-DOM U7b2 delivered and ported: CV/CarrierWord.lean (row 137 CV:lem:carrierword, 349 lines: smoothing preserves the
inherited order, the carrier's Gauss word = P's Gauss word restricted (carrierGaussList_eq_filter), the refinement
clause from geoOwner_refines; reading (i) quoted) and CV/SelectorA.lean (row 164 CV:selector_A, 182 lines: clause (A)
rendered exactly as printed — every carrier has ≥ 3 corners, from three_le_geoCornerCount at tier 1; the executor's
brief had paraphrased clause (A) as the selector identity, which is SM lem:C-X1 / CV clause (B) material — the unit
correctly rendered the printed sentence instead); rows mapped implemented (CV.carrierword, CV.selector_A); standard
axioms. Reviews of the three rows next (checker first for the two new hashes and the changed lem:carriers hash).

## ng:smoothing-record (row 74) ported and under review; three more reviews launched — 2026-09-14 ~03:56Z (pod executor)

Unit α2 rebased on the repaired SM/FrontSmooth.lean: work/drafts/front/FrontRecordBridge.lean (479 lines, sorry-free;
ALPHA2_REPORT.md) — Marking.recordIso (two markings of F compose to a RecordIso), the rounding justification lemmas
(no new crossing, successors / germs / slopes / signs unchanged), IsRounding.P_eq. EXECUTOR EDIT before review: the
bundle SmoothingRecordData had 14 fields, seven of them rendering sentences of the printed PROOF (no_new_crossing,
successor_unchanged, same_attachments, germs_unchanged, component_identity, front_record, record_polynomial); trimmed
to the seven clauses of the printed STATEMENT (full_named_record, component_circles, crossing_occurrences,
cyclic_orders, over_under_bits, signs, polynomial); the proof-sentence renderings remain as lemmas in the module.
Ported as SM/FrontRecordBridge.lean; row mapped implemented (SM.ng_smoothing_record; axioms standard + lp_lm); excerpt
sm-3:1843-1849; brief work/port/review_prompt_ng-smoothing-record.md; review launched. Also launched: CV:lem:carriers
round 2 (restated clause (ii)), CV:lem:carrierword + CV:selector_A (brief work/port/review_prompt_cv-carrierword-selectorA.md).
Checker started 03:54Z for the changed/new hashes (lem:carriers, carrierword, selector_A, ng:smoothing-record,
ng:front-domain v2).

## CV-DOM unit U3 ported: SM/GeoCarriersLemma.lean — 2026-09-14 ~03:58Z

work/drafts/cvdom/U3/GeoCarriersLemma.lean (791 lines, 48 declarations, standard axioms; REPORT.md) ported and built:
GeoCarriersLemmaData (tier 1; mechanically verified as the accepted CarriersLemmaData body under the geo renaming minus
the single turn ≠ 0 clause, which sits in GeoCornerTurnsData at tier 2 — ruling R4), GeoSmoothingData (identical mirror
of SmoothingData), def:uniform mirrors (geoCarrierUniform, geoUniformSupport, geoCarrierRotation(Int)), def:wind
weights (geoCarrierWeight = geoCarrierSelector, geoWind, geoWind_ne_zero_iff), and nine agreement lemmas on SM-generic
polygons. Finding for U6: the accepted SM/CS3.lean §B already proves geoCornerCount_eq_generic,
geoCornerPolygon_eq_generic, cornerSelector_recastTuple, carrierWeight_eq_geoCarrierSelector,
wind_eq_prod_geoCarrierSelector, carrierCrossings_eq_geo, positiveLift_eq_geo — U6 consumes them instead of redoing
them (a library module may import the accepted row module CS3 for these, or the assembler copies the proofs).

## CV-DOM unit U4 ported: SM/GeoPositiveLift.lean; U7c and U5a launched — 2026-09-14 ~04:00Z

work/drafts/cvdom/U4/GeoPositiveLift.lean (859 lines, 64 declarations, standard axioms; REPORT.md) ported and built:
geoCarrierPolyComp / geoCarrierShadow (generic: tail-off, transverse, no triple at TIER 1 via U0's fold-back exclusion
applied to the corner polygon itself), geoPositiveLift (positive, one component, crossing equivalence with the retained
crossings, writhe = |retained|), and the STRONGEST agreement: geoPositiveLift_eq_generic — literal equality of diagrams
with the accepted positiveLift on SM-generic polygons (recast-free via polyOfList + subst), with the RecordIso
corollary that SM.presentations consumes. Launched: U7c (rows CV:def:piecediagram 142, CV:lem:piececurve 143,
CV:def:X1 146 on their printed binders) and U5a (GeoMarkTransport / path transport along CrossingGeometry families →
CV:prop:chamberinv(ii) and the record-persistence machinery for lem:silence and the R-lane's G8).

## R-lane cores ACCEPTED (4 obligation rows) — claims verified 68/132, past the half mark — 2026-09-14 ~04:03Z (pod executor)

R:localization, R:parity, R:fibre_partition, R:generic_table (RProof/Cores.lean, fixed names RProof.*): 12/12 lens reviews
faithful, 8/8 refuters clean (review files work/reviews/r-*.json; raw outputs /workspace/scratch/lean_results/r-*-round1.output);
all notes non-blocking / harmless (presupposition fields, the excluded optional orbit remark, the X₁-free partition,
the abstract skeleton). Axioms of all four: propext, Classical.choice, Quot.sound only. Claims verified 68/132 (51.5%),
checklist 119/192. The remaining nine R rows (exterior, availability_0_1, generic_selector/transport/selected,
extreme_pair_zero/transport/selected, cv_theorem) need CV:def:X1 (U7c, running) and the carrier transport (U5a).
Marked products: U-R3b (work/drafts/markedproducts/U_R3b.lean, +441 lines) proves restrictCrossings_join_decomp — (d) the
consecutive block by a maximal-gap argument over (block, occurrence) pairs, (e) the join identity for ANY gap-contiguous
split (gapMark, splitOcc, first-return commutation, RecordIso.nonempty_of_occ). All 11 units delivered; the assembler
launched (target MarkedProducts_Assembled.lean → SM/MarkedProducts.lean; expected axioms: standard + lp_lm, homflyrows +
lit_homfly, lp_lm_uniqueness).

## Front lane: ng:finite-word interface statement unit launched — 2026-09-14 ~04:04Z

The fifth-but-one literature interface (fixed name SM.ng_finite_word, axiom-policy.json "literature") is to be transcribed
verbatim from blueprint/AXIOM_REGISTRY.md onto the word layer (SM/FrontWords.lean); a statement unit drafts
work/drafts/front/FrontInterfaces_statement.lean in the ∃-over-Prop-structure form of SM/LinkInterfaces.lean; it will be
independently reviewed BEFORE any consumer (rows 83, 93) may cite it, per FR-6.

## ng:front-domain ACCEPTED (round 2) — the first front-block row — 2026-09-14 ~04:10Z (pod executor)

Round 2 after the rounding repair: 3/3 lens reviews faithful, 2 refuters clean (raw
/workspace/scratch/lean_results/ng-front-domain-round2.output; review file work/reviews/ng-front-domain.json records
both rounds' outcome). Notes non-blocking: left_right_cusp is vocabulary from sm-3:1906-1907 (kept, no constraint);
FR-1/FR-2/FR-3 readings; rounding existence deferred to 76b. Checklist 120/192 (definition row).

## Four accepts, one split verdict, one library decision — 2026-09-14 ~04:22Z (pod executor)

- CV:lem:carriers ACCEPTED (round 2: clause (ii) restated over all marks of Γ; 3/3 faithful, 2 refuters clean). Non-blocking:
  (ii) ranges over the marked points of Γ (unmarked interior edge points have no owner in the accepted finite carrier model);
  double points read as Crossing P through the accepted def:interlace identification; binder only [NeZero n].
- ng:smoothing-record ACCEPTED (3/3 faithful, 2 refuters clean) with a MATERIAL DISCLOSED READING raised by all three
  reviewers (inherited from FR-1 / the accepted row ng:front-domain): `SmoothFront.Rounding S = ⟨G, geom, marking⟩` has no
  field tying the polygonal S to the rounded curves G, so `IsRounding S ↔ (∃ G, GeomRounding G) ∧ Nonempty (Marking S)`; the
  hypothesis "S is an S(F)" already contains "S carries F's named record", and the row's fields follow from the composite
  marking isomorphism without the geometry. The printed proof's content (the cusp replacement creates no crossing, changes no
  successor, germs and signs unchanged; sm-3:1851-1862) is kernel-checked only as library lemmas about G versus F
  (isDoubleOf_iff, occSetOf_eq, slopeOf_eq, crossSignOf_eq in SM/FrontRecordBridge), not asserted by an accepted row.
  DECISION D-F6: the accepted definitions are NOT rewritten (rule 2: never rewrite an accepted declaration). The library is
  extended by a theorem `isRounding_of_geomModel`: a polygonal diagram carrying the named record of the rounded curves G
  (a `GeomMarking G S`, defined on the SmoothLoop family exactly as `Marking` is on the front: circles, occurrences = double
  points of G, successor = cyclic order, pairing, over = smaller slope of G, sign = det of G's tangents) is an F-marking, hence
  `IsRounding S`. That makes the printed content a kernel-checked theorem; FINAL_REVIEW will report the reading and cite it.
  Unit "front lane γ" (new module SM/FrontGeomModel.lean) is launched for it; not a row.
- CV:selector_A ACCEPTED (3/3 faithful, 2 refuters clean; clause (A) of lem:selectorid on the printed Generic binder).
- CV:lem:carrierword: SPLIT VERDICT (2/3 faithful; the definitions lens NOT FAITHFUL on one item; 2 refuters not refuted,
  both judging that item non-blocking). The item: the printed first sentence quantifies over "a closed curve C with a
  traversal circle Γ_C and finitely many transverse double points" (d1:450-453; the generality serves the induction on
  smoothed curves, d1:481-484), the Lean binder is `hD : Diagrammatic P` with the smoothed curves reached as iterated
  carriers (field `refinement`). The dissenter's own words: "a documented, content-preserving narrowing to every instance
  the text and its own proof use", refusing only my brief's wording "no domain change". RULING: reading (i) is restated as
  a NARROWING of the printed binder to diagrammatic polygons and their iterated carriers; it is content-preserving on every
  instance the frozen source defines or uses (smoothing is defined only for polygons, def:smoothing d1:355-360; the
  consumers lem:piececurve Steps 1/5 and lem:carriers are polygon-derived) and the library has no class of general closed
  curves. The accept script (my own safeguard) requires unanimity, so the row stays `implemented` and goes to a ROUND 2
  review with the corrected, neutral disclosure (statement unchanged). If round 2 is split again the row stays
  unaccepted and is reported as such.
- Marked-product block: assembler delivered work/drafts/markedproducts/MarkedProducts_Assembled.lean (4966 lines, 0 sorry,
  axioms propext/Classical.choice/Quot.sound/SM.lp_lm (+ lit_homfly, lp_lm_uniqueness for homflyrows)); ported verbatim to
  work/lean/SM/MarkedProducts.lean (header added; three stale "ANALYSED ONLY" docstring words → "PROVED"); build running.

## Rounding lane (cf:lem-rounding, row 97): design panel decided; fidelity risks recorded BEFORE the row is stated — 2026-09-14 ~04:27Z

Panel: two architects (A model-first/existential clearance, B proof-first/named witnesses) + judge; winner A with five grafts
from B (work/drafts/rounding/PLAN_FINAL.md, Rounding_statement_FINAL.lean (compiles, 1 sorry = the row), Skeleton_FINAL.lean
(compiles, 52 leaf sorries in units P, G1, E, A, G2, G3, X)). Model: input `PolygonDiagram C` (= the accepted one-component
`Diagram` on `Shadow.single C`, plus `∀ i, principalTurn ≠ 0`); output curve = accepted `SmoothLoop` + regularity (bridged to
`ClosedC1Curve.rot`); output diagram D_ε = D read through the new record `Carried γ X` (occurrence parameters, twin pairing,
transversality, cyclic order via cycBetween/visitCoord, over/under = X's with sign consistency); junctions on parameter
intervals with explicit lifts; discs = closed Euclidean ε-discs; clearance existential in the bundle, the explicit
⅓·min{η_v,η_e,η_ℓ,η_X} in the proof module. Fidelity risks, to be cited by the reviewers of this row and its consumers:
FR-R1 D_ε is the polygonal D carried by the smooth curve (FR-1 for the rounding lane; `Carried` is the smooth-diagram record
offered to cf:lem-curl and cf:thm-carrierfloor). FR-R2 the row is the printed ∃-form; the named construction lives in the
proof module, so cf:thm-carrierfloor (A) must import it. FR-R3 `no_triple` enters through the accepted class
`PolygonDiagram.generic` (not printed in the lemma); the witness exports strictly more than printed (constant speed, open
straight interval, flatness of order ≥ 2, "junction = all of the curve in the disc", embeddedness). FR-R4 arclength/Λ
parameter (period 1) instead of arclength σ ∈ [0,ℓ]; "angular derivative nonzero" as deriv θ ≠ 0 on the open arc. FR-R5
bundle fields 2-7 are projections of `RoundingWitness`; the theorem content is field 1. FR-R6 chain audit: A's
`tangentField_periodic` needed `Regular` (false without it; fixed and proved in the skeleton); B's `roundDisc_inter_edge_in`
false at k = 0 (not adopted). FR-R7 Mathlib pin lacks smoothTransition monotonicity/derivative/flatness lemmas (Unit P
supplies them). Units launched in parallel on byte-identical copies of the skeleton; statements never change.

## ng:finite-word interface stated and ported for review — 2026-09-14 ~04:29Z (pod executor)

Statement unit delivered work/drafts/front/FrontInterfaces_statement.lean (report FINITEWORD_REPORT.md): one Prop structure
`NgFiniteWordClauses` with the single field `finite_principal_chain : ∀ W : OWord, PrincipalChain OWord.sCountSyn
OWord.IsStandardCircleBase W` (no ∃: the registry block supplies no map), `axiom ng_finite_word : NgFiniteWordClauses`
(fixed literature name), `Move := Pres ∨ Del ∨ ∃ C, Skein` (items 1-3 as the FrontWords rewrite relations), inductive
`PrincipalChain` (base / stop at the first strict decrease of s / step otherwise), the base predicate defined on words
(no crossing letter, every right cusp closes one left cusp). Readings R1-R10 and mismatches M1-M3 (M1: FrontWords' Chain
stop rule differs, bridged by principalChain_iff_chain; M2: base on words instead of via the realization, obligation
for β2; M3: Chain independent of s, B) are in the report. Ported verbatim to work/lean/SM/FrontInterfaces.lean (header
only), built 04:31Z, mapped implemented; independent interface review launched (brief work/port/review_prompt_ng-finite-word.md,
registry excerpt work/reviews/ng-finite-word-registry-excerpt.md.txt). No consumer may cite the axiom before acceptance.
Marked-product rows mapped implemented (SM.join, SM.lowest, SM.blocks, SM.homflyrows); checker passed 04:28Z (128 mapped,
17493 audited; receipt work/checks/dev-check-markedproducts-implemented.json); 4-row review running.

## D-F6 closed: SM/FrontGeomModel.lean ported — 2026-09-14 ~04:34Z (pod executor)

Front lane γ delivered the library module (358 lines, 33 declarations, imports SM.FrontRecordBridge; axioms of the main theorems
propext/Classical.choice/Quot.sound; P_eq_of_geomModels additionally SM.lp_lm through P). `GeomMarking G S` is `Marking` verbatim
with F.Occ → OccOf G (the subtype of occSetOf G), F.eval → the loops' meeting relation, F.slope → slopeOf G, F.crossSign → crossSignOf G;
F does not occur. `Marking.ofGeom (r : F.GeomRounding G) (m : GeomMarking G S) : F.Marking S` and its inverse are defs (Type-valued
markings); the Prop content is `isRounding_of_geomModel` and `isRounding_iff_geomModel : F.IsRounding S ↔ ∃ G, Nonempty
(F.GeomRounding G) ∧ Nonempty (GeomMarking G S)`. The transport of comp_eq/between_iff is by application (Equiv.setCongr is the
identity on parameters: "changes no successor"); over_iff/sgn_eq rewrite with slopeOf_eq/crossSignOf_eq ("germs and signs
unchanged"). Ported verbatim to work/lean/SM/FrontGeomModel.lean (header only). FINAL_REVIEW must cite it next to ng:smoothing-record.

## CV-DOM U7c ported (rows 142, 143, 146 implemented); new lanes; deferrals — 2026-09-14 ~04:38Z (pod executor)

- U7c delivered CV/PieceCurve.lean (CV:def:piecediagram → `CV.piecediagram_definition`, CV:lem:piececurve → `CV.piececurve`) and
  CV/X1.lean (CV:def:X1 → `CV.X1_definition`), 0 sorry, tier 0 only (no WeakGeneric fact used; rows 142/143 on the printed
  Diagrammatic binder). Ported verbatim (headers only), built, mapped implemented; checker running; 3-row review launched
  (brief work/port/review_prompt_cv-piece-x1.md) with the unit's readings disclosed as R-a..R-e: hn : 3 ≤ n a bundle
  parameter; the recursion of lem:piececurve rendered by StepInvariant with the measure "number of unselected crossings" and
  K_H fixed by Classical.choose; "Gauss word" = double-point subword of the carrier's inherited word; X₁ sums over
  (Ind hP).attach like the accepted cornerStateSum; the piece diagram is geoPositiveLift of the piece carrier. Axioms:
  CV.X1_definition additionally SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness through the field homfly_exists := ax_homfly.
- New lanes launched: (a) design panel for cb:blocks (101) + cb:products (102) on the SM carrier layer + SM.blocks
  (work/drafts/cb/); (b) statement unit for def:transverse-front (92) on the smooth class (work/drafts/front/TransverseFront.lean);
  (c) CV:lem:homflyrows (157) from the marked-product block (work/drafts/cvdom/CVHomflyRows.lean).
- DEFERRED with reasons (to be reported in FINAL_REVIEW if still open): lem:gauss-two-discs (57) is the PL Jordan–Schoenflies
  theorem for polygonal circles in S² (two complementary regions, both PL discs, positive PL/topological boundary-map
  extension) — Mathlib has no Jordan curve theorem; a self-contained formalization is a multi-thousand-line project whose only
  consumers are cb:embedded-rotation (104) and lem:corner-values (105, blocked by GAP-2 through cb:singleton ← thm:floor).
  The fd block 84-88 (transverse neighbourhood via H*α = hα₀, compact parameter avoidance, global flows of contact
  Hamiltonian fields with C^k-closeness, generic fronts, the Gauss linking integral) is heavy differential geometry with
  thin Mathlib support (no global flows, no Sard, no degree theory) and feeds only fd:contact (GAP-2); it is scheduled
  after the front certificate rows, fd:parameter-avoidance (85) first as the most tractable. CV:ax:etnyre (161): sl is
  never defined in the document ("reads the identity only as a bridge from the diagram's writhe to the transverse
  HOMFLY-PT bound"), CV:ax:slbound depends on fd:contact (GAP-2); the rendering question (definitional sl := writhe versus
  a stated bridge) is left for the GAP-2 statement-only rows.
- Checker passed 04:40Z after the ports (132 mapped, 18182 audited; receipt work/checks/dev-check-piece-x1-finiteword-implemented.json);
  the hashes of ng:finite-word, CV:def:piecediagram, CV:lem:piececurve, CV:def:X1 are audited, so their accepts can follow their reviews.

## CV:lem:carrierword round 2: 3/3 faithful, 2 refuters clean — 2026-09-14 ~04:44Z (pod executor)

With the binder narrowing disclosed as such, all three lenses returned faithful and both refuters found nothing (refuter 0 grepped
every citation of lem:carrierword in the frozen CV text — d1:630, 649, d6:94, 1416, 2309 … — and found every instance inside the Lean
class {diagrammatic polygons} ∪ {their iterated carriers}). Non-blocking notes: the module docstring still said "no domain change"
and cited the statement as d1:450–456 — corrected to the ruling's wording and to 450–459 (docstring only; module rebuilt, reviewer
input refreshed, checker re-run before the accept); Diagrammatic's two extra clauses are the subsection's standing hypothesis;
marks include vertices and selected visits (stronger); S2 stated on Diagrammatic (the generic instance is carrierword_generic);
refinement's hypothesis S' ∈ Ind(G_P) leaves the equivalence with "non-interlacing on Γ_q" to the consumer (visits_separated_iff).
Accepting after the checker passes.

## CV:lem:homflyrows (157) stated and proved from the marked-product block — 2026-09-14 ~04:53Z (pod executor)

Unit delivered work/drafts/cvdom/CVHomflyRows.lean (325 lines; report CVHOMFLYROWS_REPORT.md): bundle `CVHomflyRowsData` with one
field per printed display — connected_sum (= SM.homflyrows.connected_sum), knot_split_link (from the general SM.Link.P_splitUnion;
SM.homflyrows.split_union needs J one-component and was not usable), two_component_row (SM's two_component_row after
twoLinking = 2ℓ; `IsLinkingNumber D i j ℓ := 2ℓ = mixedSignSum D i j`), split_union_family (printed clause (iii), rendered as an
n-block split diagram `IsSplitUnionFamily`; the binary parenthesization `IsSplitChain` is supplementary, equivalence proved at
n = 2 only). Axioms: propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness. Readings reused from
the SM block (D2 LinkEquiv, D9 clean marked joins, polygonal split reading, factor-2 linking bookkeeping); risks in the report.
Ported verbatim to work/lean/CV/HomflyRows.lean (header only), built, mapped implemented; review launched (brief
work/port/review_prompt_cv-lem-homflyrows.md); checker running.

## Marked-product block ACCEPTED (mp:join, mp:lowest, mp:blocks, lem:homflyrows); U5a ported — 2026-09-14 ~04:54Z (pod executor)

All four rows: 3/3 faithful, 2 refuters clean (20 agents). Reviewers confirmed D9 (record-level clean marked join; the printed text
compares realizations only by lc:presentations, sm-3:1419-1421) and the determination of the record mark μ by the printed interval I.
Only non-blocking notes (BlockSupply.actual keeps the printed adjective 'actual' as a hypothesis; the inclusion fields of mp:join are
specializations of join_value; knots as LinkEquiv classes, D2). claims verified 76/132, checklist 128/192.
CV-DOM U5a delivered and ported (library, not rows): SM/GeoMarkTransport.lean (668 lines), SM/GeoPathTransport.lean (865),
CV/ChamberInvII.lean (501; `X1_eq_of_mem_chamber_of_pieceHomfly : PieceHomflyTransported hn hP hQ h → X1 hn Q hQ = X1 hn P hP`).
Left for CV:prop:chamberinv (ii): the lemma PieceHomflyTransported — choice-independence of the piece polynomial P_H (pieceSupport is
Classical.choose); route recommended in U5a REPORT §6: CV.gausscode_polynomial + a RecordIso from pieceCarrier_gaussWord (≈250-400 lines).

## ng:finite-word ACCEPTED (literature interface; 4 of 5 admitted, src:contact pending) — 2026-09-14 ~04:56Z (pod executor)

3/3 faithful, 2 refuters clean; the axiom may now be cited by consumers (row 83 on words, row 93). Readings recorded in the review
file (s syntactic, base on words, deletion directions only for I/II, right-cusp skein templates excluded). OBLIGATIONS left to the
front lane: (1) `hinv`: a disjoint-gadget commutation preserves OWord.IsStandardCircleBase (true: it relabels the two exchanged
letters' indices bijectively; labelRun tests labels for equality only) — needed to turn Descends.of_principalChain into an
unconditional projection; (2) β2: (realize W).IsStandardCircles ↔ W.IsStandardCircleBase and (realize W).sCount = W.sCountSyn.

## def:transverse-front (92) stated and ported; checker note — 2026-09-14 ~04:59Z (pod executor)

Statement unit delivered work/drafts/front/TransverseFront.lean (914 lines, 135 declarations; report TRANSVERSE_REPORT.md):
`TransverseKnot` (C^∞ 1-periodic embedded T : ℝ → ℝ³ with z′ − y x′ > 0 and the printed projection clauses), the smooth diagram
class `SmoothKnotDiagram` with over = smaller y, `IsGenericPositiveTransverseFront D := ∃ K, K.front = D`; bundle
`TransverseFrontDefinitionData` (13 fields: one per printed clause, the two printed consequences no_cusp / vertical_up proved,
writhe = Σ sgn det(u_O, u_U) over the double points, over/under counts read as the traversal tallies (T-4), determination as
functions of the diagram + front_ext (T-5)). Risks R-1..R-6 in the report; R-3: the polygonal (FR-1) reading for transverse fronts
is not built (GAP-1, belongs to fd:contact). Ported verbatim to work/lean/SM/TransverseFront.lean (header only), built, mapped
implemented; review launched (brief work/port/review_prompt_def-transverse-front.md).
Process note: I started a second tools/check_lean.py while one was still running (two concurrent lake builds); killed the
second within seconds, then restarted the checker cleanly once the first had finished. Rule kept: one checker/build at a time.

## Rounding lane complete: cf:lem-rounding assembled, statement strengthened (R-f), ported — 2026-09-14 ~05:04Z (pod executor)

Seven units proved all 52 leaves (P 4, G1 3, E 9, A 7, G2 10, G3 4, X 15; 139 helper lemmas), assembler merged them into
work/drafts/rounding/Rounding_Assembled.lean (3147 lines, 0 sorry in declarations, axioms propext/Classical.choice/Quot.sound,
every skeleton declaration verbatim). Statement pre-review (PREREVIEW.md): jointly satisfiable, no blocking issue; notes R-a..R-h.
DECISION on R-f: the printed clearance is ε₀(L), a function of the polygon alone, while the fixed statement had ∀ C D, ∃ ε₀
(ε₀ allowed to depend on the over/under assignment D) — weaker than printed and unusable by cf:thm-carrierfloor (B) ("Take
ε₁ = ε₀(L)"). Restated before review: `exists_clearance : ∀ C, (∀ i, principalTurn ≠ 0) → (Shadow.single C).Generic → ∃ ε₀ > 0,
∀ (D : PolygonDiagram C) ε, 0 < ε → ε < ε₀ → Nonempty (RoundingWitness C D ε)` (the construction's clearance C depends on C only;
proof unchanged up to argument order; RoundingData.of_diagram adapted). Both files recompiled (0 errors). Two prose mentions of
the placeholder word reworded. Ported verbatim to work/lean/SM/Rounding.lean (header only); build/map/checker queued behind the
running checker; review brief work/port/review_prompt_cf-lem-rounding.md updated with the pre-review notes.

## U7c rows reviewed: CV:def:X1 ACCEPTED, CV:def:piecediagram faithful (accept deferred to the module repair), CV:lem:piececurve NOT FAITHFUL — 2026-09-14 ~05:11Z (pod executor)

CV:def:X1 (146): 3/3 faithful, refuters clean → accepted. CV:def:piecediagram (142): 3/3 faithful, refuters clean; weaker-side notes
(erased's crossing clause is a cardinality bijection; the datum field renders the word half of the printed datum, not the
rotation-system half; record_shadow only SingleCircle) — accept deferred until the shared module CV/PieceCurve.lean is repaired for
row 143, so that the review binds the final file. CV:lem:piececurve (143): 1/3 NOT FAITHFUL and BOTH refuters REFUTED (weaker than
printed): the lemma's last conclusion "the datum of Definition def:piecediagram is the datum of C_H" has a rotation-system half — at
each surviving crossing c ∈ H the two strands of C_H through crossingPoint c carry the parent's counter-clockwise half-edge order
(they run along P's two edges at c with P's directions; printed proof d1:664-666 "that is the second half of the datum") — with no
field in PieceCurveData; reading (ii) cannot make it definitional since it presupposes that clause. REPAIR: add a field
`rotation_system` (the piece curve's strands through crossingPoint c are positively directed along P's two edges at c, for every
c ∈ H) and strengthen `realizable` to a crossing-point-preserving bijection; prove from the accepted geo self-intersection lemmas
(GeoIsSelfIntersection clause 2 / geoCornerPolygon edges are sub-segments of P's edges); statements of rows 142/146 unchanged;
round-2 review of 143.

## def:transverse-front ACCEPTED — 2026-09-14 ~05:15Z (pod executor)

3/3 faithful, 2 refuters clean (explicit transverse unknots exhibited). Notes recorded in the review file (T-1..T-5, R-1, R-3, R-5;
docstring line citations off by 1-2 lines, cosmetic, left as is). Checker passed ~05:20Z with 135 mapped (cf:lem-rounding,
CV:lem:homflyrows, def:transverse-front audited; receipt work/checks/dev-check-rounding-implemented.json).
Process note: a background waiter of mine matched its own command line (pgrep -f on a literal that the same command contained) and
never returned; killing it by the same pattern killed my own shell. Rule: patterns for pgrep/pkill must not occur in the invoking
command line (use character-class tricks on the pattern itself, e.g. 'check_lea[n]').

## CV:lem:homflyrows ACCEPTED — 2026-09-14 ~05:19Z (pod executor)

3/3 faithful, 2 refuters clean; readings reused from the SM marked-product block (D2, D9, factor-2 linking bookkeeping) and
CV:ax:homfly. Unblocks the R-lane rows R:generic_selected / R:extreme_selected (with CV:thm:carrierfloor still pending) and
CV:cor:groupedknot / CV:singleton_D_i on the CV side.

## Lanes launched after CV:lem:homflyrows — 2026-09-14 ~05:21Z (pod executor)

- CV:lem:pieceintrinsic (156) unit (work/drafts/cvdom/CVPieceIntrinsic.lean) on the implemented piece layer; next CV:cor:groupedknot (158).
- R-lane statement panel (work/drafts/rlane2/) for the nine remaining obligations (R:exterior, availability_0_1, generic_selector,
  generic_transport, generic_selected, extreme_pair_zero, extreme_transport, extreme_selected, cv_theorem) now that CV:def:X1 is
  accepted; rows depending on CV:thm:carrierfloor (blocked by CV:ax:slbound ← fd:contact, GAP-2) will be stated and reported as
  unprovable under the frozen interfaces unless the panel finds otherwise.

## hinv obligation closed: SM/FrontWordsBase.lean ported — 2026-09-14 ~05:23Z (pod executor)

`isStandardCircleBase_comm_invariant : ∀ W W' : OWord, IsComm W.letters W'.letters → (W.IsStandardCircleBase ↔ W'.IsStandardCircleBase)`
(standard axioms) and the unconditional `SM.ng_finite_word_nonbase_descends'` (standard + SM.ng_finite_word). Finding: labelRun
allocates fresh labels by the letter's POSITION, so the two runs of a commutation differ by the transposition |X| ↔ |X|+1; the lemma
is stated up to injective relabelling (kernel-checked counterexample to the naive equality recorded in HINV_REPORT.md). The β2
obligation (realize W).IsStandardCircles ↔ W.IsStandardCircleBase remains open.

## cf:lem-rounding ACCEPTED (row 97) — 2026-09-14 ~05:25Z (pod executor)

3/3 faithful, 2 refuters clean. First row of the carrier-floor chain (97 → 98 cf:lem-curl (design panel running) → 99
cf:thm-carrierfloor (depends on fd:contact, GAP-2) → 100 thm:floor). Notes in the review file; the named construction
SM.CornerRounding.roundedWitness / clearance is available to cf:lem-curl and cf:thm-carrierfloor (A) as FR-R2 requires.

## CV:lem:piececurve repaired and re-stated; module CV/PieceCurve.lean replaced — 2026-09-14 ~05:27Z (pod executor)

Repair unit (work/drafts/cvdom/U7c-fix/, REPORT.md, PieceCurve.diff): new field `rotation_system` — at every surviving crossing
c ∈ H the two strands of the piece shadow through crossingPoint c are in bijection with the two parent edges of c with positively
proportional directions (the parent's counter-clockwise half-edge order, "the second half of the datum", d1:664-666) — and
`realizable` strengthened to a crossing-point-preserving bijection; four new lemmas (the missing geometric fact
`cornerPolygon_edge_of_crossingPoint_mem`: an edge of a corner polygon through crossingPoint c is a positive multiple of a parent
edge of c). Rows 142/146 declarations byte-identical; CV.X1_definition axioms unchanged. Module rebuilt (CV.PieceCurve, CV.X1,
CV.ChamberInvII), row 143 remapped, reviewer input refreshed, brief extended with a ROUND 2 paragraph; checker running; round-2
review launched. CV:def:piecediagram will be accepted on the same checker pass (its hash is unchanged).

## CV:def:piecediagram ACCEPTED — 2026-09-14 ~05:28Z (pod executor)

Accepted on the checker pass after the row-143 repair (row-142 text unchanged, hash c45c162d…; receipt
work/checks/dev-check-piecefix-implemented.json, 135 mapped, 19024 audited). Checklist 134/192. CV:lem:piececurve round 2 running.

## CV:lem:rounding (152) stated and proved from SM.cf_lem_rounding; ported — 2026-09-14 ~05:38Z (pod executor)

Unit delivered work/drafts/cvdom/CVRounding.lean (439 lines; report CVROUNDING_REPORT.md): CV's lemma (d3_floor.tex:31-93) is SM's
cf:lem-rounding word for word (τ_i for ϑ_i) except the scoping sentence (CV's single def:rot; (d) stated with CV.rot and proved via
the accepted rot_eq_rotationNumber), two commentary paragraphs (readings), and the polygon domain (LabelledTuple n + Diagrammatic +
Regular + nonzero turns, bridged to PolyComp by polyComp L hreg with n ≥ 3 from Regular.three_le; single_generic_of_diagrammatic).
The SM witness is transported unchanged; axioms propext/Classical.choice/Quot.sound. Risks FR-CV1..FR-CV7 in the report (OverUnder
structure; [NeZero n]; hreg redundant but printed; no-triple from Diagrammatic as CV's (C) states). Ported verbatim to
work/lean/CV/Rounding.lean (header only), built, mapped implemented; review launched (brief work/port/review_prompt_cv-lem-rounding.md);
checker running.

## cb lane (cb:blocks 101, cb:products 102): design panel decided; fidelity risks recorded BEFORE the rows are stated — 2026-09-14 ~05:40Z

Panel (work/drafts/cb/PLAN_FINAL.md, Statements_FINAL.lean, Skeleton_FINAL.lean): winner A (accepted CV block objects + the SM.blocks
route) with three grafts from B (literal SM owner definition; D_A = accepted positiveLift on SM carriers; P_H = recordPolynomial of the
restricted record with existential D_H). Binder: hn : 3 ≤ n, hP : SM.Generic P, hS : IsDecomposition hn hP S. Risks to be cited by
the reviewers: R-1 SM "block" = accepted CV.Piece (generic_crossingGeometry hn hP) S, bridging conjuncts (CV.U = supportUnselected,
CV.N = supportNeighbors, geometricInterlacementGraph = interlacementGraph) inside the clauses they serve; R-2 owner of a crossing
DEFINED through a fixed visit (someVisit) and pinned by crossing_owner; block owner = CV.pieceOwner transported by
geoComponentEquivGeneric, pinned by one_owner — no clause depends on the choices; R-3 two lanes joined by the accepted equivalence
geoComponentEquivGeneric (identity on owners); R-4 "actual positive carrier diagram D_H" = positiveLift of a carrier q of an
independent refinement T ⊇ S with carrierCrossings T q = pieceLabels H (IsBlockCarrierDiagram; the printed U(S_H) = H is not needed by
any clause); R-5 "its restricted named cyclic record" = Record.restrictCrossings of the record of the owner's actual diagram D_{A_H}
to H's chords (blockRecord), RecordIso to "the original record restricted to H"; R-6 P_H := recordPolynomial (blockRecord H) pinned by
polynomial_independent and block_diagram; R-7 stronger conjuncts (polynomial_independent for EVERY block carrier diagram; one_owner
∃!); R-8 hn, [NeZero n] bundle parameters; R-9 proof sentences (eq. cb:greedy-step, greedy independence, self-crossings = owned labels)
are companion lemmas, not fields; R-10 a proof-irrelevant identification of CrossingGeometry proofs inside the PROOF of the PC leaf;
R-11 row 102's proof uses CV:lem:piececurve / def:piecediagram (rows 143/142; 142 accepted, 143 in round 2; fallback PLAN_B L3 greedy
support); axioms: 101 standard + lit_homfly/lp_lm/lp_lm_uniqueness through homfly (as def:C), 102 adds SM.blocks' (SM.lp_lm); R-12 D8
guard: RecordIso enters only through SM.P / presentations. Units KL0, KL1 (carrier record bridge, critical path), KL2, KL3, T1, GL, AS
launched in parallel on byte-identical skeleton copies; statements never change.

## cb:blocks (101) ported and under review; cb:products (102) provers launched — 2026-09-14 ~05:43Z (pod executor)

work/lean/SM/CBBlocks.lean = the panel's Statements_FINAL.lean with the row-101 theorem proved by the panel's own sorry-free
`cb_blocks_definition_check` body (kept as an alias), the row-102 theorem removed (its bundle CbProductsData stays fixed here; the
theorem will live in SM/CBProducts.lean). Built, mapped implemented; review launched (brief work/port/review_prompt_cb-blocks.md,
readings R-1..R-12 disclosed); checker running. Seven prover units (KL0, KL1 critical path, KL2, KL3, T1, GL, AS) launched on
byte-identical copies of Skeleton_FINAL.lean; the assembler will produce CBProducts importing SM.CBBlocks.

## CV:lem:piececurve ACCEPTED (round 2); β2 ported — 2026-09-14 ~05:51Z (pod executor)

Round 2 after the rotation-system repair: 3/3 faithful, 2 refuters clean; readings R-a/R-b/R-c recorded in the review file. The
whole U7c triple (142, 143, 146) is now accepted. Front lane β2 delivered seven library modules (grid realization
`SM.realize : OWord → PLFront`, slots/cycles, correspondence xdir/cusps/crossings/sCount/downCount/writhe with the word layer,
standard circles + the planarity fact downCount = c, the base bridge forward direction (realize W).IsStandardCircles ← W.IsStandardCircleBase,
placement-independence of P and defect via Deform, rectangle geometry / OutsideMatch for the moves); ported verbatim as
work/lean/SM/FrontRealize{Slots,,Correspondence,Standard,Base,Deform,Geometry}.lean (headers only, one prose word reworded); building.
Open β2 items: converse of the base bridge, MoveMatch component bijection / arc tools, deletions with an empty factor.

## CV:lem:pieceintrinsic (156) stated and proved; ported — 2026-09-14 ~05:58Z (pod executor)

Unit delivered work/drafts/cvdom/CVPieceIntrinsic.lean (1058 lines; report CVPIECEINTRINSIC_REPORT.md): bundle PieceIntrinsicData
(carried, restriction, intrinsic, record_iso, same_link, polynomial, writhe), theorem CV.pieceintrinsic on the printed Generic binder.
Substantive reading R1: D_L(H) rendered as the family of positive lifts of carriers q of S ∪ K (K an admissible erased set) retaining
exactly H — every field for every member (fixing a single D_L(H) would make the row a tautology). R3 identity on visits = pieceVisit ∘ Φ =
restrictionVisit; R4 "same oriented link" in the F4 polynomial form. General theorem exists_recordIso_of_geoCarrierCrossings_eq (two
carriers of independent sets with the same retained crossings have record-isomorphic positive lifts) — also what cb:products needs
(KL1). Axioms standard + lit_homfly/lp_lm/lp_lm_uniqueness through homfly. Ported verbatim to work/lean/CV/PieceIntrinsic.lean (header
only), built, mapped implemented; review launched (brief work/port/review_prompt_cv-lem-pieceintrinsic.md); checker running.

## CV:lem:rounding ACCEPTED (row 152) — 2026-09-14 ~05:59Z (pod executor)

3/3 faithful, 2 refuters clean; the CV analogue of cf:lem-rounding proved through the polygon bridge. Next in the CV floor chain:
CV:lem:curl (154; the SM cf:lem-curl panel is running — the CV row will be bridged the same way), CV:thm:carrierfloor (155; blocked
by CV:ax:slbound ← fd:contact, GAP-2, and by CV:ax:etnyre's rendering).

## cb:blocks ACCEPTED (row 101) — 2026-09-14 ~06:01Z (pod executor)

3/3 faithful, 2 refuters clean; readings R-1..R-12 confirmed. The provers of cb:products (102) are running on the panel's skeleton.
Checker ~06:05Z passed with 138 mapped (CV:lem:pieceintrinsic audited; receipt work/checks/dev-check-pieceintrinsic-implemented.json).

## Curl lane (cf:lem-curl, row 98): design panel decided; fidelity risks recorded BEFORE the row is stated — 2026-09-14 ~06:19Z

Panel (work/drafts/curl/PLAN_FINAL.md, Statements_FINAL.lean (1 sorry = the row), Skeleton_FINAL.lean (54 leaf sorries; assembly and
row proved)): winner A (printed hypotheses only; record-level carrying; existential disc inside any preassigned neighbourhood; local
polygonal kink) with grafts from B (unchanged_deriv export; the Cuts/InsertedArc/GluedLoop decomposition in the replacement unit).
Risks to be cited by the reviewers: FR-C1 (the one class deviation) input and output diagrams are `RecordCarried F D` = the accepted
`Carried` minus the point-coincidence clause τ_eval plus twin_eval — forced because a polygonal RI kink of D cannot sit at the smooth
double point; coherent with SmoothFront.Marking (record level) and the printed proof's record-isomorphism step; P is well defined at
record level (rp:record-polynomial); Carried.toRecordCarried proved. FR-C2 exists_curl strengthens the printed ∃Δ to "inside any
preassigned neighbourhood Δ₀ of p" (proof sm-3:4038-4041, consumer 4442); the bare form is exists_curl'. FR-C3 "modified inside Δ" =
equality of the parametrised curves with velocity off the window (s₁,s₂) mod 1. FR-C4 P_{F'} = P_F via the polygonal RI and the
accepted P_reidemeister_I, not the printed F°/record route. FR-C5 "isolated" = uniqueness of the u-tangency on the arc; "turns strictly
positively" = StrictMonoOn of a lift; β − α < 1. FR-C6 exports beyond print (window, unchanged_deriv, crossing correspondences, ri : RI
D D', sign/writhe corollaries). FR-C7 effort ≈ 8500 lines / 54 leaves / 7 units, 2 waves. FR-C8 chain repairs: A's inserted_arc_props
was false in two clauses (missing ℓ > 0; a non-uniform diameter bound) — repaired; B's exists_insertedArc / exists_gluedLoop false for
arbitrary cuts — not adopted. FR-C9 the polygonal kink is inserted at a free interior edge point in the cyclic gap of t₀; the smooth
double point and the polygonal kink point are unrelated (FR-C1); sign conventions fixed in KinkInsertion.kink_neg / order_pair.
FR-C10 compiled against the built SM.Rounding; port as SM/Curl.lean after the units close. A statement pre-review (satisfiability,
numeric probe of the model identities) runs alongside the provers, as for the rounding lane.
- 06:20Z: curl-lane provers launched (units MF, G, HT, R, K1, K2 (critical path), CA on byte-identical copies U_*.lean of
  Skeleton_FINAL.lean; a statement pre-review with numeric probes runs alongside; assembler afterwards → SM/Curl.lean).

## R lane, nine X₁-dependent obligations: statement panel decided; readings recorded BEFORE the rows are stated — 2026-09-14 ~06:35Z

Panel (work/drafts/rlane2/Statements_FINAL.lean (compiles; exactly nine sorry = the row theorems RProof.exterior, availability_zero_one,
generic_selector, generic_transport, generic_selected, extreme_pair_zero, extreme_transport, extreme_selected, cv_R : CV.hyp_R),
NOTES_FINAL.md): winner A (spec-first on the accepted CV-event locus, X₁ consumed literally: F_±(S) = CV.X1Summand = wind·∏Ω₁ on Ind,
0 otherwise; Φ_±(Q) = fibreSum at that summand; X₁ = CV.X1; proved auxiliaries X1_eq_sum_fibreSum (closes the X₁ flag of the accepted
cores), rowTerm_eq_exterior_mul_touching, near_of_fibre_identities, sides_of_near (R6: cv_R = cv_R_near + chamberinv(ii)),
hyp_R_of_data) with grafts from B (row 170 SummandTransport with record data; 175/177 clause splits; row-178 architecture and the
bridge-consumption check smR_shape_of_hyp_R). B's row-172 field mixed_carrier was FALSE (kernel-checkable via LocalTable.succ wordE {a,b} =
[8,5,3,4,2,6,7,1,0]: the co-owned corners are the marks on the INCOMING edges, conv:selected-visits) — the panel's #eval is to be cited in
the review note so nobody "corrects" it the wrong way. Readings/risks: fixed labels a = x_ef, b = x_eg, c = x_fg with the canonical
branch (selected ac) plus relabelled ab/bc instances (F2(A)); sides named by local graphs, never by coorientation; the exterior factor
represented by the base row (equal to every representative by independent_of_A + wall_invariant; the printed full-availability binder
kept, not a narrowing); row 170 summand_transport stronger than the bare fibre identity (downgrade path recorded); presupposition
fields beyond the bare claims (listed in NOTES_FINAL) each a sentence of the RA Statement paragraphs; the skeleton↔carrier identification
is a proof obligation, not a clause; every Ω₁ transport across the wall needs record-invariance of pieceHomfly (lem:pieceintrinsic 156,
under review) — the shared obstacle; hn : 3 ≤ n an explicit parameter; SM.lit_homfly in #print axioms through homfly. PROVABLE NOW: row
172 R:generic_selector (whole) and the X₁-free presupposition clauses of 170/173/175/176/177 (unit U-PRE) and the assembly lemma
(U-A2); after 156: rows 168, 170; after 158 + G11: 173; after CV:singleton_D_i: 175; rows 174, 176, 177 need CV:thm:carrierfloor
(GAP-2) — statable, to be reported unprovable under the frozen interfaces. CV.hyp_R is declared in this draft (fixed name of the CV
hypothesis row); one declaration must be seen by the CV row, RProof.cv_R and Bridge.sm_R.
- 06:37Z: R-lane wave-1 provers launched on copies of work/drafts/rlane2/Statements_FINAL.lean — U-SEL (row 172 R:generic_selector
  whole), U-PRE (X₁-free presupposition clauses of rows 170/173/175/176/177 as standalone field lemmas), U-A2 (assembly lemma
  fibre_identities); assembler → RLaneX1_Statements.lean (portable, no placeholder: definitions, bundles, CV.hyp_R, auxiliaries, the
  proved row 172) + RLaneX1_Assembled.lean (eight rows still open). Status request sent to the chamberinv (ii) unit (running ~1h50m),
  pointing it at CV/PieceIntrinsic.lean's record-isomorphism lemmas for PieceHomflyTransported.

## CV:lem:pieceintrinsic ACCEPTED; CV:prop:chamberinv (147) completed and ported — 2026-09-14 ~06:46Z (pod executor)

CV:lem:pieceintrinsic: 3/3 faithful, 2 refuters clean (R1 family reading judged faithful and stronger; F4 polynomial form of "same
oriented link" recorded). Claims 81/132, checklist 138/192.
U5c delivered PieceHomflyTransported (via CV.exists_recordIso_of_geoCarrierCrossings_eq from CV/PieceIntrinsic + gausscode_polynomial +
U5a's chamber transports) and the row: CV/PieceHomflyTransport.lean (library) and CV/ChamberInvRow.lean (bundle ChamberInvData: the
accepted clause-(i) fields + x1_constant; theorems CV.chamberinv_ii, CV.chamberinv; axioms standard + lit_homfly/lp_lm/lp_lm_uniqueness
through X1). Kernel note (U5c REPORT §7): deterministic timeouts when four record clauses were proved in one theorem — split per clause.
Ported verbatim (headers only), built, mapped implemented; review launched (brief work/port/review_prompt_cv-prop-chamberinv.md); checker running.
- 06:49Z: three CV-DOM units launched on the now-accepted layer: U5b CV:lem:silence (151; work/drafts/cvdom/U5b/), CV:cor:groupedknot
  (158; all dependencies accepted; work/drafts/cvdom/CVGroupedKnot.lean), U6 geo agreement + Bridge:B4 statement (work/drafts/cvdom/U6/;
  the cb:products-dependent identification cornerHomfly = groupedPoly is proved from the fixed CbProductsData as an explicit hypothesis
  until SM.cb_products lands).

## cb:products (102) proved and ported — 2026-09-14 ~06:58Z (pod executor)

Seven units proved all 18 leaves (KL0 9, KL1 2 — the carrier record bridge, proved on the SM Carrier lane via ccpCornerPolygon_block and
componentMarkList_getElem_successor — KL2 1, KL3 1, T1 1, GL 1, AS 2); assembler produced work/drafts/cb/CBProducts_Assembled.lean (1936
lines, 0 placeholder, imports SM.CBBlocks; the row-101 declarations removed after verbatim check). Axioms of SM.cb_products: propext,
Classical.choice, Quot.sound, SM.lp_lm (through the accepted SM.blocks product law); the leaves standard only. Ported verbatim to
work/lean/SM/CBProducts.lean (header only), built, mapped implemented; review launched with R-1..R-12 disclosed; checker to follow.

## CV:prop:chamberinv ACCEPTED (row 147, clauses (i) and (ii)) — 2026-09-14 ~07:00Z (pod executor)

3/3 faithful, 2 refuters clean. With chamberinv (ii) the CV theorem row R:cv_theorem (RProof.cv_R = cv_R_near + chamberinv(ii), R6) and
Bridge:B4 (pointwise + SM.prop_C_chamber + chamberinv_ii) have their CV input; both still wait for cb:products (row 102, under review) /
the R-lane rows. cb:products review launched (brief work/port/review_prompt_cb-products.md).

## Bridge:B4 stated and proved (U6); ported — 2026-09-14 ~07:16Z (pod executor)

U6 delivered SM/GeoCarrierAgreement.lean (agreement of the geo layer with the accepted SM Carrier lane on SM-generic polygons; Omega1 =
cornerCoefficient given cb:products) and Bridge/B4.lean: `Bridge.B4Data` with pointwise (BRIDGE.md display (17): CV.X1 hn P
(generic_of_sm hn hP) = SM.cornerStateSum hn hP) and sides (display (18): for every CV-generic Q in the side chamber of
eventOfTriple hn g h, the SM side value at any side parameter equals CV.X1 Q; R7 shape, no quotient chamber object, BRIDGE.md 1441);
`Bridge.B4_of_cb` isolates cb:products as one hypothesis and `Bridge.B4 := B4_of_cb (SM.cb_products …)` (row 102 under review — B4
inherits its status). Axioms of Bridge.B4: standard + lit_homfly, lp_lm, lp_lm_uniqueness. Ported verbatim (headers only), built,
mapped implemented; review launched (brief work/port/review_prompt_bridge-b4.md); checker running. Targets: this closes the fifth
target's statement (Bridge.B4); Bridge.theorem (sm_R) waits for RProof.cv_R (R lane).

## CV:lem:silence (151) proved (U5b); ported — 2026-09-14 ~07:17Z (pod executor)

U5b delivered CV/PathX1Transport.lean (the chamber-transport chain re-bound to an arbitrary tier-2 path datum) and CV/Silence.lean:
`SilenceData` with sides (∀ tp > 0, tm < 0: X1 (E.curve tp) = X1 (E.curve tm), the all-sides form) and chambers (side-chamber form via
chamberinv_ii); `CV.silence`; silent_center_weakGeneric / silent_curve_weakGeneric for every parameter (new plane lemma
parallel_segments_meet_endpoint for rem:silentclauses). Axioms of CV.silence = those of chamberinv_ii. Fidelity note (REPORT §4.6): the
printed predicate-by-predicate exclusions are replaced by one fact (centre weakly generic) + the accepted local constancy of geometric
records along the path — proof matter. Ported verbatim (headers only); build and mapping queued behind the running checker; review
launched (brief work/port/review_prompt_cv-lem-silence.md).

## cb:products ACCEPTED (row 102) — 2026-09-14 ~07:18Z (pod executor)

3/3 faithful, 2 refuters clean. With 101/102 accepted, Bridge.B4's only non-accepted input is gone (B4 under review). cb:singleton (103)
remains blocked by thm:floor (GAP-2). CV:lem:silence mapped implemented (CV/Silence.lean built ~07:18Z); its review launched.

## R lane wave 1 done: row 172 R:generic_selector proved; RProof/X1Rows.lean ported (with CV.hyp_R) — 2026-09-14 ~07:22Z (pod executor)

U-SEL proved the whole row (all five fields; ownership convention kernel-checked with #eval on the accepted tables: succ wordE {a,b} =
[8,5,3,4,2,6,7,1,0], {b,c} = [8,2,3,7,5,6,4,1,0], wordP {a,c} = [4,2,3,1,8,6,7,5,0]); U-PRE proved the 12 X₁-free presupposition
clauses of rows 170/173/175/176/177 as field lemmas; U-A2 proved the assembly lemma fibre_identities and CvTheoremData.of the eight
bundles. Assembler: RLaneX1_Statements.lean (3003 lines, no placeholder; the eight open row theorems omitted, their bundles kept) — ported
verbatim as work/lean/RProof/X1Rows.lean (header only), built; rows mapped implemented: R:generic_selector → RProof.generic_selector,
CV:ax:R → CV.hyp_R (the R6 all-sides form, a Prop definition). Axioms: generic_selector and hyp_R standard + SM.lit_homfly (through
CV.X1). Reviews launched; checker running. The eight open rows (168, 170, 173-178) wait for: 168/170 record transport (now available via
CV/PieceHomflyTransport), 173 CV:cor:groupedknot (running) + G11, 175 CV:singleton_D_i (blocked), 174/176/177 CV:thm:carrierfloor (GAP-2),
178 = all of them + chamberinv(ii) (accepted).
- 07:25Z: R-lane wave 2 launched — U-EXT (row 168 R:exterior) and U-AV (row 170 R:availability_0_1) on copies of RLaneX1_Assembled.lean,
  using the now-available record transport (CV/PieceHomflyTransport, CV/PieceIntrinsic) and the chamber/path transports; assembler →
  RLaneX1Rows2.lean importing RProof.X1Rows. Also launched: fd:parameter-avoidance (85) unit (work/drafts/fd/) and a GAP-2 statement-only
  design memo (work/drafts/gap2/) covering CV:ax:etnyre, CV:ax:slbound, the carrierfloor theorems, thm:floor and rows 89-91/94.

## Front certificate rows 76-83: design panel decided; fidelity risks recorded BEFORE the rows are stated; executor decisions — 2026-09-14 ~07:27Z

Panel (work/drafts/frontrows/PLAN_FINAL.md, Statements_FINAL.lean (exactly eight sorry = the row theorems), Skeleton_FINAL.lean (26 leaf
sorries; glue, certificate_laws, word_bound and row 83's assembly proved)): winner B. Key finding F1: the accepted ArcCover clause
(LinkMoves.lean:208) forbids spectator strands inside a move disc, so β2's full-height block rectangles cannot serve as RI/RII/RIII
discs — design A's eleven site leaves were FALSE (e.g. [l 1 d] ++ [l 2 d', σ 1, r 2] ++ [r 1]); the FINAL routes four rows through
records (record core U2 + presentations / P_addFree / exists_smoothing_record) and four through vertex-moved realizations with
hugging convex discs. Effort ≈ 17-23k lines for rows 77-82 + 76(1) + 83 on words, 27-38k with the representation clause.
Risks to be cited by the reviewers: FR-8 class narrowing — rows 77-82, 76 sentence 1 and 81 sentence 1 are stated on realizations of
closed oriented words (SM.realize), the printed rows on fronts of ng:front-domain; justified by the printed section computing on
Rutherford's words (the moves exist only as word patterns) and CLOSED by the printed second sentence of ng:commutation kept as the
field `represent` (row 76) on the smooth class, from which row 83 is derived; rows 76 and 83 cannot be accepted before `represent`
lands. FR-9 "deformations through fronts without a singular event" = SmoothFront.NonsingularDeformation (jointly C^∞ family on
[0,1] × ℝ, constant circle count; a stronger hypothesis than the most liberal reading). FR-10 "represented by" = equal D, w, s plus a
named-record isomorphism of every rounding S(F) with the realization's diagram (hence P_{S(F)} = P_{realize W} by rp:record-polynomial)
— exactly what every consumer uses. FR-11 row 81 sentence 2 on PLFront with IsStandardCircles (general planarity leaf); word-reading
fallback recorded. FR-12 "the unique compatible smoothing" = the field unique_smoothing (a theorem about IsCuspSkein); "either
principal direction" = the symmetric IsCuspSkein; right-cusp templates outside the row (as in the accepted interface). FR-13 every
polynomial clause reaches SM.lp_lm through P; row 83 and word_bound additionally SM.ng_finite_word. FR-14 base_B proved on the
syntactic base through the accepted forward bridge. FR-15 no block-rectangle move discs (F1/F2): hugging convex discs, vertex-moved
diagrams, exterior index shift via β2's shiftIdx/extSlot/next_ext. FR-16 identity rounding on PL fronts: d(F) = degAZ (P F.diagram)
(FR-1's polygonal reading). FR-17 proof-route disclosures: row 77 compares realize W with a vertex-moved diagram by RI and transports
by the named record; row 82 identifies realize A' with (realize A).switch x by a RecordIso, not a Deform.
EXECUTOR DECISIONS (nobody to ask; AUTONOMOUS_EXECUTION): D-F7 invest U8's `represent` (the budget allows it; the FR-8 fallback — a
recorded class change on 76/83/93 — applies only if it stalls, and will then be reported as such); D-F8 row 81 sentence 2 stays on
PLFront (U7), the FR-11 fallback only if U7 stalls; D-F9 the lanes are confirmed at 17-23k lines. Wave 1 launched: U1 (counts + degAZ
leaves), U2 (record core infrastructure), U7 (PL circles) in parallel; U3/U4 after U2; U5/U6 after U4; U8 deformation leaves when a
lane is free, `represent` last. Row acceptance order 79, 78, 81, 80, 77, 82, then 76 and 83 together.

## CV:lem:silence ACCEPTED (row 151) — 2026-09-14 ~07:30Z (pod executor)

3/3 faithful, 2 refuters clean. Checker ~07:40Z passed with 144 mapped (rows R:generic_selector, CV:ax:R, Bridge:B4, CV:lem:silence
audited; receipt work/checks/dev-check-x1rows-silence-implemented.json). Reviews of Bridge:B4 and of R:generic_selector + CV:ax:R running.

## Bridge:B4 ACCEPTED (checklist row 182) — 2026-09-14 ~07:32Z (pod executor)

3/3 faithful, 2 refuters clean. The C = X₁ dictionary (17)/(18) is now an accepted bridge row; Bridge.theorem (Bridge.sm_R) waits only
for RProof.cv_R (R:cv_theorem), which in turn needs rows 168/170 (wave 2 running), 173 (groupedknot running + G11), 175
(CV:singleton_D_i, blocked), 174/176/177 (CV:thm:carrierfloor, GAP-2). Process note: the reviewer input for B4 left the helper theorems'
proof bodies in place (only the row theorem was stripped); reviewers did not rely on them — for future bridge rows strip every proof
in the module.

## CV:cor:groupedknot (158) proved from accepted rows; ported — 2026-09-14 ~07:35Z (pod executor)

Unit delivered work/drafts/cvdom/CVGroupedKnot.lean (939 lines, 53 declarations; report CVGROUPEDKNOT_REPORT.md): bundle GroupedKnotData
(label_union, retain_all, partition, tree, product, single, knot_diagram, grouped_polynomial, grouped_writhe, underlying_curve,
no_triple_points, no_piece), theorem CV.groupedknot on def:X1's binder; route = mp:blocks (SM.blocks) on the record of D(W) =
geoPositiveLift of the carrier, with four new tier-1 record lemmas (record arc order = traversal order; lift of a smaller carrier ≅
restricted record of a larger one; record interlacement = geometric interlacement; record blocks ≃ pieces on the carrier). cb:products
not needed. Readings: "≅" = record isomorphism with an actual clean-marked-join diagram (F4, D9); the tree existential via JoinForest;
tree/product over every record-isomorphic leaf family (stronger); k ≥ 1 as Nonempty. Axioms: standard + lit_homfly/lp_lm/lp_lm_uniqueness.
Ported verbatim (header only), built, mapped implemented; review launched (brief work/port/review_prompt_cv-cor-groupedknot.md); checker running.
Unblocks R:exterior's dependency list and CV:singleton_D_i's groupedknot input (165 still needs carrierfloor / cb:singleton — GAP-2).

## R:generic_selector (row 172) and CV:ax:R (CV.hyp_R) ACCEPTED — 2026-09-14 ~07:49Z (pod executor)

Both 3/3 faithful, 2 refuters clean (10 agents). Row 172 is the first X₁-dependent R obligation closed; the ownership convention was
kernel-checked by reviewers, refuters and the prover alike. CV:ax:R is a Prop definition (the hypothesis), its proof being the R lane's
final theorem row RProof.cv_R (178). Checker ~07:55Z passed with 145 mapped (CV:cor:groupedknot audited; receipt
work/checks/dev-check-groupedknot-implemented.json).

## GAP-2 statement memo received; reclassification of rows 89/90 and decisions — 2026-09-14 ~07:51Z (pod executor)

Memo work/drafts/gap2/GAP2_STATEMENTS_MEMO.md (+ compiling sketch Gap2Statements.lean: 31 structures/defs, no theorem). Findings:
GAP-2 bites in exactly one printed sentence of cp:finite-contact-path (91): "an actual ambient isotopy … yields H_{D_ε} = H_{D_T}" =
Reidemeister's theorem, excluded by D2 (HomflyClauses.descent over LinkEquiv); named as the Prop SM.AmbientIsotopyDescent (NOT an axiom).
Rows 89 ce:rounding and 90 ce:smoothing-record are NOT GAP-2-blocked (I had lumped them in; corrected): 90 is provable (~0.8k lines,
the ng:smoothing-record argument on the height marking) and 89 is provable with 3-5k lines of analysis. 94 fd:contact is blocked via 91,
the deferred fd block 84-88 and the undeclared src_contact interface. cf:thm-carrierfloor (99): clauses (R), (A), (B) statable and
provable now, (C) blocked via 94 and cf:lem-curl; thm:floor (100): z_parity provable, a_floor blocked via 99(C); CV:thm:carrierfloor
(155): (R)(A)(B)(C) through the polygon bridge, (D) provable now; CV:ax:slbound (162) statable on TransverseKnot (domain narrowing to
knots with a generic front, SM fd:contact's own domain), blocked via fd:contact.
DECISIONS: D-F10 CV:ax:etnyre (161): option (iii) — no independent sl object (CV never defines sl and calls the identity "only a
bridge"); the printed shape is kept as the parametrised bundle CV.SlBoundData (sl); a definitional sl := writhe (i) is rejected as a
substitution, a sixth axiom (ii) is rejected by the axiom policy. D-F11 statement-only bundles for the blocked rows are ported only
after a statement review and are NEVER mapped as implemented (the map's declarations are theorems); the four target names
(thm_C_soft, thm_C_S7, thm_comparison, cor_C_inherits) and SM.corner_laws_and_soft stay undeclared; FINAL_REVIEW carries the memo's
per-row sentences. D-F12 rows 90 then 89 go to prover units now (full claims); partial clauses of 99/100/155 are not pursued (no
claim closes without (C)/(a_floor)). Reporting: rows 89, 90, 99(R)(A)(B), 100(z_parity), 155(D) are not to be lumped with the
unprovable ones in FINAL_REVIEW.

## CV:cor:groupedknot ACCEPTED (row 158) — 2026-09-14 ~07:58Z (pod executor)

3/3 faithful, 2 refuters clean. Unblocks R:generic_transport's groupedknot input (173 still needs the RIII move G11) and
CV:singleton_D_i's (165 still needs CV:thm:carrierfloor and cb:singleton — GAP-2).

## fd:parameter-avoidance (85) proved; ported — 2026-09-14 ~08:00Z (pod executor)

Unit delivered work/drafts/fd/ParameterAvoidance.lean (514 lines, Mathlib only; report PARAMETER_AVOIDANCE_REPORT.md): hypotheses
ParameterAvoidanceHyp (compact, smooth on an open neighbourhood, rank q via finrank of the range of fderiv, d < q), bundle
ParameterAvoidanceData (isClosed, interior_eq_empty, finite_collection), theorem SM.fd_parameter_avoidance; route: the local zero set
parametrised by Mathlib's implicit function (C¹), Hausdorff dimension ≤ d + m − q < m for the projected parameter set, finite compact
cover, dense complement ⇒ empty interior (no Sard); finite collection via Baire. Axioms standard. FR-PA-1 (chart reading of "a compact
subset of a smooth d-dimensional coordinate manifold") is the main disclosed risk; FR-PA-2..5 recorded. Ported verbatim (header only),
built, mapped implemented; review launched (brief work/port/review_prompt_fd-parameter-avoidance.md); checker running.
- 08:02Z: fd block re-opened after row 85 closed in 514 lines (the deferral of 2026-09-14 ~04:33Z is revised): units launched for
  fd:linking-calculus (88; work/drafts/fd/LinkingCalculus.lean — the Gauss integral, symmetry, constancy under families, generic
  directions, uniform framing; constancy may need an isolated lemma if the derivative-under-the-integral route stalls) and for
  fd:transverse-neighborhood (84) + fd:contact-motions (86) with a feasibility memo first (work/drafts/fd/FD_84_86_FEASIBILITY.md;
  global flows of compactly supported fields and the coordinate contact identity are the expected Mathlib gaps). fd:generic-front (87)
  waits for 85 (under review) and 86.

## fd:parameter-avoidance ACCEPTED; curl lane provers done (54 leaves, two false unused leaves), port-prep launched — 2026-09-14 ~08:16Z (pod executor)

fd:parameter-avoidance (85): 3/3 faithful, 2 refuters clean (FR-PA-1 chart reading judged the printed proof's own setting and every
consumer's instance). Claims 88/132, checklist 146/192.
Curl lane: seven units proved 52 of 54 leaves; the two remaining, ξ_strictMonoOn / ξ_strictAntiOn (Unit G), are FALSE as stated in
the degenerate case β' < α' (U_G_REPORT: unit-circle counterexample; the frozen leaf lacks the hypothesis α' ≤ β'); the assembler
redirected their four uses to the proved restricted forms g_ξ_strictMonoOn / g_ξ_strictAntiOn, so the row SM.cf_lem_curl has no sorryAx
(axioms propext, Classical.choice, Quot.sound, SM.lp_lm; 8353-line assembly Curl_Assembled.lean). Statement pre-review (PREREVIEW.md):
satisfiable and non-trivial; no failed identities; FR-C1 mitigation (a) suggested — an old_crossingPoint field on CurlWitness (old
crossings keep their points). DECISION (chain repair, recorded like FR-R6/FR-C8): the two false leaves get the hypothesis α' ≤ β' (or are
deleted if unused); the optional FR-C1 mitigation is added only if the existing construction provides it; prose mentions of the
placeholder word reworded. Port-prep unit launched → work/drafts/curl/Curl_Port.lean → SM/Curl.lean.

## ce:smoothing-record (90) proved on the spatial-link vocabulary; ported — 2026-09-14 ~08:17Z (pod executor)

Unit delivered work/drafts/gap2/CeSmoothingRecord.lean (873 lines, 61 declarations; report CE_SMOOTHING_RECORD_REPORT.md): bundle
CeSmoothingRecordData with eight fields (the definition sentence split into four sub-clauses as FrontDomainDefinitionData does;
height_choice; same_record_as_endpoint; crossing_free_components; source_and_polynomial as a labelled consequence), theorem
SM.ce_smoothing_record; route = FrontSmooth §8 transported to CleanCuspSmoothing + HeightMarking.ofSmoothing + the composite record
isomorphism + presentations. Axioms standard + SM.lp_lm (as the accepted ng_smoothing_record). DECISION D-1 (vocabulary): the field
`collar` added to CleanCuspSmoothing (C^∞ jet agreement at the arc ends does not imply agreement on collars; ce:rounding's cutoff has
collars, sm-3:3083-3084) — rows 89 and 91 MUST import the vocabulary from SM/CeSmoothingRecord.lean rather than redeclare the memo's
sketch (K-8); the ce:rounding panel (running on the sketch) will be told at unit launch. Risks K-1..K-9 recorded in the report (K-3:
the D_ε fields quantify over CuspRoundingFamily — row 89's object — vacuous if that class were empty; the pairwise theorems carry the
content unconditionally; K-4 non-vacuity of CleanCuspSmoothing argued not kernel-checked; K-5 IsDisc convexity inherited from
GeomRounding). Ported verbatim (header only), built, mapped implemented; review launched (brief
work/port/review_prompt_ce-smoothing-record.md); checker running.

## cf:lem-curl (98) ported as SM/Curl.lean (8382 lines) — 2026-09-14 ~08:25Z (pod executor)

Port-prep (PORT_REPORT.md): the two false unused leaves ξ_strictMonoOn / ξ_strictAntiOn given the hypothesis α' ≤ β' and proved (chain
repair, like FR-R6/FR-C8); the FR-C1 mitigation ADOPTED — CurlWitness.old_crossingPoint (every old crossing of the kinked diagram keeps
its point) with the corresponding conjunct in CurlData.i; prose placeholder mentions reworded; #print axioms SM.cf_lem_curl = propext,
Classical.choice, Quot.sound, SM.lp_lm. Statement declarations byte-identical to Statements_FINAL.lean except CurlWitness (+1 field) and
CurlData (+1 conjunct) — the fixed-statement record for row 98 is Statements_FINAL.lean + PORT_REPORT.md §3. Built, mapped implemented;
reviewer input = the module's statement sections 1-4 with the row theorem's proof withheld (compiles); review launched (brief
work/port/review_prompt_cf-lem-curl.md); checker queued. cf:thm-carrierfloor (99) now has (A)/(B)/(R) inputs (rounding + curl); (C)
remains GAP-2 (via fd:contact).

## R lane wave 2 done: rows 168 R:exterior and 170 R:availability_0_1 proved; RProof/X1Rows2.lean ported — 2026-09-14 ~08:39Z (pod executor)

U-EXT (96 helpers) and U-AV (120 helpers) proved both rows whole on the wave-1 file, using the record transport of CV/PieceHomflyTransport
(the shared obstacle of NOTES_FINAL is closed) and the chamber/path transports; assembler produced RLaneX1Rows2.lean (3645 lines,
imports RProof.X1Rows + CV.PieceHomflyTransport, no placeholder; ASSEMBLY2_REPORT.md). Axioms of both rows: standard + lit_homfly, lp_lm,
lp_lm_uniqueness (through gausscode_polynomial). Ported verbatim (header only) as work/lean/RProof/X1Rows2.lean, built, rows mapped
implemented; reviews launched (brief work/port/review_prompt_r-exterior-availability.md); checker running. Remaining R rows: 173
(needs the RIII move G11 + groupedknot ✓), 175 (CV:singleton_D_i, blocked), 174/176/177 (CV:thm:carrierfloor, GAP-2), 178 (all).
Checker ~08:55Z passed with 148 mapped (ce:smoothing-record, cf:lem-curl audited; receipt work/checks/dev-check-ce90-curl-implemented.json).

## fd:contact-motions (86) proved modulo one explicit Mathlib gap; fd:transverse-neighborhood (84) stated only — 2026-09-14 ~08:42Z (pod executor)

Unit report work/drafts/fd/FD_84_86_REPORT.md, memo FD_84_86_FEASIBILITY.md. Row 86: work/drafts/fd/ContactMotions.lean (896 lines) proves
`SM.fd_contact_motions : SM.SmoothDependence → SM.ContactMotionsData` — every printed clause (global flow of X_H, group law, C^∞ inverse,
the contact identity with the exact conformal factor exp ∫ H_z ∘ φ, positivity, joint smoothness, finite compositions, C^k-closeness on
compacts) — with ONE explicit hypothesis `SmoothDependence` ("the global flow of a C^∞ compactly supported field on ℝ³ is C^∞ jointly in
(s, p)"), the genuine gap of this Mathlib pin (ODE: existence, uniqueness, Grönwall, time regularity; no differentiability in the initial
point). Global existence, uniqueness, the group law, α(X_H) = H, L_{X_H}α = H_z α and the contact identity for any jointly smooth flow are
proved unconditionally (standard axioms). Row 84: TransverseNeighborhood.lean (266 lines) = faithful statement bundle only; blocked by
the same smooth-dependence theorem twice (Moser flow, ambient flow) plus ≈ 3-5k lines (uniform IFT radius, coordinate Gray-Moser).
DECISION D-F13: rows 84/86 are NOT mapped as implemented (a row theorem with a hypothesis is not the row; D-F11 rule); a dedicated unit
attempts SmoothDependence (differentiability of ODE flows in the initial point, C^1 via the variational equation + Grönwall, then C^∞ by
induction; est. 4-6k lines); if it lands, row 86 closes with no other change and 87 (fd:generic-front) becomes provable from 85 + 86.
Otherwise FINAL_REVIEW reports 86 as "proved modulo the smooth-dependence theorem, stated" and 84 as "stated, blocked".

## ce:smoothing-record ACCEPTED (row 90) — 2026-09-14 ~08:45Z (pod executor)

3/3 faithful, 2 refuters clean. Disclosed weakenings recorded (K-5 IsDisc convexity inherited from GeomRounding; FR-1/FR-4; K-3
conditional D_ε fields). NOTE for the ce:rounding lane (89): CuspRoundingFamily is the object row 90 quantifies over — its `clean`
field must be satisfied in the D-1 sense (collar + IsDisc discs) by the constructed family, and row 89 should conclude
∀ L, 0 < c → CuspedProjection → Nonempty (CuspRoundingFamily L) (or a stronger form) so that row 90's D_ε content is unconditional.

## cf:lem-curl ACCEPTED (row 98) — 2026-09-14 ~08:49Z (pod executor)

3/3 faithful, 2 refuters clean; FR-C1 judged faithful for this lemma (record-level output class; consumers must read the curl at
record level — cf:thm-carrierfloor (A)/(B)/(R) are now statable and provable, (C) remains GAP-2). Claims 90/132, checklist 148/192.
- 08:50Z: CV:lem:curl (154) unit launched (work/drafts/cvdom/CVCurl.lean), the CV twin of cf:lem-curl through the polygon bridge as
  CV:lem:rounding was; FR-C1 (record-level carrying) inherited and to be disclosed.

## Rows 168 R:exterior and 170 R:availability_0_1 accepted — 2026-09-14 ~09:02Z (pod executor)

Review workflow (brief work/port/review_prompt_r-exterior-availability.md; 3 lens reviewers + 2 refuters per row): both rows 3/3
faithful, refuters clean; only NON-BLOCKING notes (recorded in work/reviews/r-exterior.json and r-availability.json): FullAvail /
availability card read on side t (side-invariant by the accepted FibrePartitionData.avail_same / rows 167, 171); hs quantified as in
every accepted R row; C_Q represented by the base row A = ∅; row 170's summand_transport is a disclosed strengthening of the spec's
proof instruction (carrier/record/selector/rotation/coefficient transport), record transport = equality of def:X1's record-derived
data w_{S,L}, P_{S,L}, rotation = |rot|. Process note (as for Bridge:B4): the reviewer statement file left six tactic lines of the
helper AV_170_fibre_identity visible (not the row proof); future R statement files will strip helper bodies too. Rows set accepted at
~09:02Z; checker run started (log work/checks/checker-run-0902.log). Progress line 09:02Z: claims verified 92/132, checklist 150/192.

## Ce:rounding lane (row 89): design panel decided; fidelity risks recorded BEFORE the row is stated — 2026-09-14 ~09:05Z (pod executor)

Panel (2 architects A/B + judge; work/drafts/cerounding/PLAN_FINAL.md, Statements_FINAL.lean = the frozen row statement
`SM.ce_rounding : CeRoundingData`, Skeleton_FINAL.lean 1103 lines compiling with 33 leaf sorries in 5 units U-P/U-G/U-C/U-L/U-E,
assembly PROVED). Winner A with grafts from B. Imports SM.CeSmoothingRecord (row 90's vocabulary SpatialLink, CuspedProjection,
RegularGenericProjection, HeightMarking, CleanCuspSmoothing WITH `collar`, CuspRoundingFamily — redeclared nothing, per D-1/K-8),
SM.Rounding, Mathlib SmoothTransition. Fidelity risks (PLAN_FINAL §6), to be cited in the review brief:
- CE-R1 (FR-1/GAP-1): RegularGenericProjection is "the diagram" (as def:transverse-front); the row delivers no polygonal Diagram or
  HeightMarking; consumers 90/91 take the marking as a hypothesis.
- CE-R2 (family index): the library's SpatialFamily indexes slices by all of ℝ, jointly C^∞ on ℝ × ℝ and embedded everywhere;
  printed is "0 ≤ λ ≤ 1", "embeddedness outside [0,1] not claimed". Met by the time clamp μ = Real.smoothTransition λ (on [0,1] the
  printed family reparametrized); the strip reading ContDiffOn (Icc 0 1 ×ˢ univ) is equivalent up to this reparametrization.
- CE-R3: "no cusps on another branch" is derived from `transverse` (CuspedProjection.not_isCusp_of_isDouble, no field);
  heights_distinct kept as the printed field although it follows from embedded.
- CE-R4 (construction differs from the printed constants; invisible in the statement): chart rectangle [−M², 2M²] × [u₋³, u₊³]
  instead of the disc V; cutoff periodicBump in the parameter instead of ρ(u); normalized sup-norm clearance with ε = M instead of
  |A| ε M √(1+y₀²) < d/2; the printed distance argument survives in exists_remote_clearance.
- CE-R5 (collar, D-1): "It cleanly smooths the cusps" refers to CleanCuspSmoothing WITH the collar field (accepted row 90); the
  construction supplies it (r < η).
- CE-R6 (witness extension): CuspRoundingWitness extends the accepted CuspRoundingFamily by intervals_disjoint_circle (the
  library's ℝ-disjointness admits wrap-around overlap), U and clean_in (one neighbourhood and one interval per cusp for the whole
  family = the intervals of the fixing clause); row 90 quantifies over the parent, delivered via toCuspRoundingFamily.
- CE-R7 (bundle shape, FR-R5 analogue): CeRoundingData fields 2-6 are projections of the witness; the theorem content is
  exists_family and const_of_no_cusps; same_velocity is a theorem (CuspRoundingFamily.deriv_eq_of_isDouble), not a field.
- CE-R8 (readings): "spatial embedding" = injective immersion of compact circles (embedded + regular); orientation = parameter
  direction (T-1); ExactCuspGerm on an OPEN interval with y' ≠ 0; the printed hypothesis 0 < c is never used (K-6).
- CE-R9 (scope): the two disclaimers and the contact computation sm-3:3132-3169 are commentary; nothing Legendrian / transverse /
  sl is stated; row 89 is not GAP-2-blocked; its only consumer is row 91 via row 90's D_ε.
- CE-R10 (chain audit): all 33 leaves judged true by the judge; false-leaf probes run on arc_no_crossing case 3, mem_Icc_of_u_mem
  (u decreasing), exists_remote_clearance (δ ≤ 1/3), chi_eq_zero_on_collar (1 − η > r), deriv_xz_ne_zero_of_notMem.
- CE-R11 (non-vacuity): CuspedProjection is nonempty (round circle at height 0); a kernel-checked witness (~40 lines) to be
  produced with the units before acceptance.
Decision D-2 (row-90 interface, PLAN_FINAL §7.1): the panel recommended folding intervals_disjoint_circle / U / clean into the
library's CuspRoundingFamily "before row 90 is accepted"; row 90 (ce:smoothing-record) was accepted at ~08:49Z, and an accepted
declaration is never rewritten, so the fold-in is NOT done: the extension CuspRoundingWitness stands and toCuspRoundingFamily
feeds row 90 (the panel confirms nothing breaks). §7.3 (strip reading for row 91) is recorded as an option for the row-91 unit; the
skeleton keeps the smoothTransition clamp. §7.4: row 90's K-3 non-vacuity may cite CeRoundingData.exists_cuspRoundingFamily later.
Units launched on byte-identical copies work/drafts/cerounding/U_{P,G,C,L,E}.lean (statements frozen; helpers prefixed).

## CV:lem:curl (row 154) ported: work/lean/CV/Curl.lean — 2026-09-14 ~09:08Z (pod executor)

Twin unit (work/drafts/cvdom/CVCurl.lean 383 lines, CVCURL_REPORT.md) read on the accepted SM.cf_lem_curl: CV's hypotheses, existence
sentence and clauses (i)-(iv) (d3_floor.tex 306-321) are word for word SM's (sm-3:3873-3888; SM's \status 3890 "transcribed from CV
lem:curl"); the single statement difference is the scoping sentence (CV 305 "rot as in def:rot") and in this lemma every rot is a
curve rot, so (iv) is read through the definitional CV.rotCurve (F6) with no identification theorem (contrast row 152). CV.CurlSite
duplicates SM.CurlSite field for field with rfl round trips toSM/ofSM (FR-CV-C1); the witness is SM.CurlWitness S.toSM Δ; bundle
CV.CVCurlData (exists_curl, exists_curl', disc, i, ii, iii, iv), row theorem CV.curl; corollaries curl_of_carried, curl_homfly_eq
(homfly letter; adds lit_homfly / lp_lm_uniqueness through P_eq_homfly — kept outside the bundle, FR-CV-C3), CurlSite.next (the
consumer's iteration). Inherited risks FR-C1..C6, C9; CV-specific FR-CV-C1..C5 (CVCURL_REPORT §5). Ported verbatim (header only),
`lake build CV.Curl` OK 09:07Z, axioms of CV.curl = propext, Classical.choice, Quot.sound, SM.lp_lm. Mapped CV:lem:curl → CV.curl
(implemented) 09:08Z; checker started (log work/checks/checker-run-0908.log). Reviewer input: the module with EVERY theorem proof
stripped (10 sorries; compiles) — work/reviews/cv-lem-curl-reviewer-input-statement.lean.txt; brief work/port/review_prompt_cv-lem-curl.md.

## Decision D-F14: fd:linking-calculus (row 88) proved modulo the degree formula RegularPoleCount; NOT mapped — 2026-09-14 ~09:10Z (pod executor)

Unit result work/drafts/fd/LinkingCalculus.lean (2075 lines, compiles, no placeholder, axioms standard) with LINKING_CALCULUS_REPORT.md:
`SM.fd_linking_calculus : LinkingCalculusData`, nine fields (symm, family_const, finite_crossings, crossing_formula, framing_uniform,
framing_invariant, framing_homotopy, transverse_uniform, self_linking_invariant), eight proved unconditionally; the field
crossing_formula is `RegularPoleCount → …` where RegularPoleCount (fd:regular-pole-count, sm-3:2894-2897) is the degree formula
∫ G^*ω = Σ_{G(p)=N} σ(p) for a regular value N of a smooth doubly periodic unit-vector map (finiteness of the preimage as an explicit
hypothesis). Its printed proof is Stokes/Green on the torus minus small discs with the primitive λ_N; Mathlib has only the box
divergence theorem and no degree theory. As for row 86 (D-F13), a row with a clause conditional on an unproved analytic fact is NOT
mapped as implemented: row 88 is reported "proved modulo RegularPoleCount, stated" (its consumers 91 and 94 are GAP-2 blocked in any
case). The module will be ported to work/lean/SM/LinkingCalculus.lean as library material (header disclosing the conditional field)
so the work is in the delivery; the row stays pending. Readings recorded by the unit (FR-LC-1..9): S¹ = ℝ/Pℤ with P > 0 a parameter
(reparametrisation invariance of ℓ not proved, not printed); smooth families on [0,1] = restrictions of jointly C^∞ maps on ℝ × ℝ;
planeDet ν x y = det(x, y, ν), "nearer the observer" = larger ⟪·, ν⟫, "parallel" includes both signs, crossings counted in one
fundamental domain; "embedded" = injective mod P; radius independence proved for every common radius with the disjointness property
(slight strengthening); the paper's normal-chart injectivity (reused at sm-3:3285) not proved. A feasibility probe for RegularPoleCount
via Mathlib's box divergence theorem may be run later if time allows.

## Checker 09:13Z passed with 151 mapped (CV:lem:curl audited); SM/LinkingCalculus.lean ported as library; SmoothDependence PROVED — 2026-09-14 ~09:16Z (pod executor)

Receipt work/checks/dev-check-cvcurl-implemented.json. Review of CV:lem:curl launched (3 lenses + 2 refuters). work/drafts/fd/LinkingCalculus.lean
ported verbatim to work/lean/SM/LinkingCalculus.lean with a header disclosing D-F14 (row 88 not mapped; crossing_formula conditional on
RegularPoleCount); `lake build SM.LinkingCalculus` OK 09:15Z. The SmoothDependence unit (work/drafts/fd/SmoothDependence.lean, 652 lines,
SMOOTH_DEPENDENCE_REPORT.md) PROVED `SM.SmoothDependence` in full (Lipschitz dependence via dist_le_of_trajectories_ODE; variational
estimate for HasFDerivAt of the time-T map; induction on C^k in space with the augmented field on E × (E →L E) cut off by a bump in the
linear variable; joint smoothness by suspension) — the estimate of 4000-6000 lines in FD_84_86_FEASIBILITY.md was ~10x too pessimistic.
Consequence: D-F13 is superseded for row 86 — the merged file ContactMotions_SmoothDependence_MERGED.lean ends with an UNCONDITIONAL
`SM.ContactMotionsData`; the unit is preparing ContactMotionsFinal.lean with the row theorem `SM.fd_contact_motions : ContactMotionsData`
for port/map/review. Feasibility probes launched (bounded): RegularPoleCount (row 88's gap) and rows 84/87 re-examined with smooth
dependence available (REGULAR_POLE_COUNT_FEASIBILITY.md, FD_84_87_FEASIBILITY_v2.md).

## fd:contact-motions (row 86) ported UNCONDITIONALLY: work/lean/SM/ContactMotions.lean; two library clashes fixed — 2026-09-14 ~09:26Z (pod executor)

work/drafts/fd/ContactMotionsFinal.lean (1437 lines: the row-86 module merged with the SmoothDependence unit; `SM.smoothDependence :
SmoothDependence` proved; row theorem `SM.fd_contact_motions : ContactMotionsData` unconditional, the former conditional theorem kept as
fd_contact_motions_of_smoothDependence; statement part byte-identical to the reviewed-draft statement except two docstring edits; axioms
standard; 0 exact name clashes) ported verbatim (header only) as work/lean/SM/ContactMotions.lean; `lake build SM.ContactMotions` OK
09:25Z; mapped fd:contact-motions → SM.fd_contact_motions (implemented); checker started (log work/checks/checker-run-0925.log). D-F13 is
superseded for row 86 (unconditional); row 84 stays stated-only pending the feasibility re-assessment. Reviewer input: the module with
EVERY theorem proof stripped (definitions in full) — work/reviews/fd-contact-motions-reviewer-input-statement.lean.txt; brief
work/port/review_prompt_fd-contact-motions.md (readings FR-CM-0..7 from FD_84_86_REPORT.md §4).
Library hygiene: the unit's clash scan found `SM.contactForm` declared in both SM/TransverseFront.lean (accepted) and the library module
SM/LinkingCalculus.lean ported at 09:11Z; my own scan found also `SM.crossingSign` (SM/Crossings.lean, accepted). Since the linking-
calculus module is unmapped library material ported minutes earlier (no accepted declaration touched), its two identifiers were renamed
lcContactForm / lcCrossingSign in the draft and the ported copy (header line records the edit); rebuilt OK. Rule going forward: run the
namespace-aware clash scan (work/port/… inline script) before every port.

## RegularPoleCount (row 88's gap) judged FEASIBLE; skeleton commissioned — 2026-09-14 ~09:30Z (pod executor)

Probe report work/drafts/fd/REGULAR_POLE_COUNT_FEASIBILITY.md: verdict FEASIBLE, 1400-2000 lines, no topology. Route ("bump primitive"):
replace the singular primitive λ_N of the area form by the globally smooth λ_χ = k_χ(Z)·(N × x)·dx with k_χ(Z) = (χ(Z) − 1)/(4π(1 − Z)),
χ a ContDiffBump at Z = 1; the pointwise identity d(G^*λ_k) = D·(2Zk − (1 − Z²)k′) du∧dv (proved algebraically in /tmp) gives
gaussIntegral = ∫∫ D·φ′(Z∘G) with φ = (1 + Z)χ/(4π); exactness on the torus by FTC per slice + periodicity; the right side is supported
in G⁻¹(small cap) ⊂ disjoint inverse-function neighbourhoods of the preimages, where Mathlib's change of variables
(integral_image_eq_integral_abs_det_fderiv_smul) with the chart F = (⟪G,e₁⟫, ⟪G,e₂⟫), det DF = D·Z, turns each piece into
sign(D p)·∫ψ = sign(D p) (polar coordinates + FTC). A different PROOF from the printed disc-deletion argument, proving exactly the encoded
statement SM.RegularPoleCount; its discharge makes row 88's crossing_formula unconditional (then row 88 can be mapped and reviewed,
superseding D-F14). The probe agent is writing the leaf skeleton RPC_Skeleton.lean + RPC_PLAN.md; prover units follow.

## CV:lem:curl (row 154) accepted — 2026-09-14 ~09:31Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/cv-lem-curl.json; non-blocking notes listed there: IsDisc reading, closed-Δ reading
of (iii), FR-C5 arc-wide isolation, FR-CV-C3 letter P versus homfly, FR-C1 CV-native, redundant `short`, a docstring citation nit).
Checker 09:29Z passed with 152 mapped (fd:contact-motions audited; receipt work/checks/dev-check-contactmotions-implemented.json). Row set
accepted 09:31Z; checker restarted (log work/checks/checker-run-0932.log). Progress 09:31Z: claims verified 93/132, checklist 151/192.
Row 155 CV:thm:carrierfloor (C) remains GAP-2 (CV:ax:slbound / CV:ax:etnyre) — see the GAP-2 memo.

## fd rows 84 and 87 re-assessed with smooth dependence: 84 FEASIBLE (~3.5k), 87 HARD (~5.2k); fidelity risks recorded BEFORE the rows are stated — 2026-09-14 ~09:36Z (pod executor)

Memo work/drafts/fd/FD_84_87_FEASIBILITY_v2.md. Row 84: the printed Gray–Moser/Cartan step is explicit polynomial algebra in the paper's chart (Moser identity checked in Lean: work/drafts/fd/MoserIdentityCheck.lean); the time-dependent periodic flow is a corollary of the proved smooth dependence by suspension; the existing statement work/drafts/fd/TransverseNeighborhood.lean needs no change. Row 87: clear route, row 85 used three times ((d,q) = (1,2), (2,3), (3,4)), no Sard; statement work/drafts/fd/GenericFront_Statement.lean (SM.GenericFrontData := ∀ L, GenericFrontHyp L → ∃ Φ, GenericFrontConclusion L Φ). Both lanes commissioned (skeletons, then prover units); consumers (94 via 91) stay GAP-2 blocked, the rows count as claims. Fidelity risks (verbatim from the memo §1.6, §2.6):
### 1.6 Fidelity risks (row 84)

* **FR-TN-1** (sm-3:2397) `S¹ = ℝ/2πℤ` as `2π`-periodic lifts; "embedded" = injective mod `2π` + immersion.
* **FR-TN-2** (sm-3:2399-2400) "smooth embedding `H : S¹ × D_δ → ℝ³`" = `C^∞` on the open solid torus +
  injective mod `2π` + immersion + images of open sets relatively open; the proof gives a global
  diffeomorphism onto an open set, so the field is weaker than what is proved, never stronger.
* **FR-TN-3** (sm-3:2401-2403) `h` quantified with `H`, only `h > 0` demanded (printed clause); the proof's
  `h` is smooth but smoothness is not a printed clause.
* **FR-TN-4** (sm-3:2405, 2490-2502) "positive transverse pushoff" = a small positive circle of a
  transverse annulus with `L` as zero circle (the paper's "source convention", sm-3:2501-2502);
  if a consumer needs Etnyre's pushoff a bridge lemma is required.
* **FR-TN-5** (sm-3:2405-2406, 2503-2504) transverse isotopy ends at an orientation-preserving
  reparametrization `T∘ρ` (`T(θ+κb)`).
* **FR-TN-6** (sm-3:2481-2482, 2501) the annulus domain is the open `(−ε, b)`; the closed end `s = b`
  is reached only through the isotopy clause.
* **FR-TN-7** (sm-3:2406-2408, 2538-2541) "ordinary ambient isotopy … preserving their orientations" =
  compactly supported family of `C^∞` diffeomorphisms of `ℝ³` with `Ψ_1∘L = T` as parametrized
  circles; the extension to `S³` and orientation-preservation of `Ψ_t` (sm-3:2538-2541) are not
  clauses of the statement and are not stated.

### 2.6 Fidelity risks (row 87)

* **FR-GF-1** (2614) circles as `2π`-periodic lifts; "embedding" = injective mod `2π` + immersion.
* **FR-GF-2** (2614-2615) `IsContactIsotopy` includes **compact support**, absent from the printed
  statement, present in the printed proof (2632-2638, 2769-2772) and used by the consumer
  (sm-3:3480-3481 "the two smooth compactly supported ambient flows").  Deliberate strengthening.
* **FR-GF-3** (2616-2617) "cusp" = parameter with `x′ = 0` (consumer's reading sm-3:3470-3474);
  "semicubical" is carried by the germ clause; finiteness counted on one period.
* **FR-GF-4** (2617) double points as ordered pairs distinct mod `2π`; transversality = nonzero
  determinant of the front velocities `(x′, z′)`; the printed `x′(θ)x′(η)(y(η) − y(θ))` is this
  determinant for Legendrian curves (2717-2721).
* **FR-GF-5** (2621-2626) exact germ: `y′(θc) ≠ 0` makes `u = y − y₀` a local coordinate; "may
  increase or decrease" = no sign condition on `y′(θc)`; identities on a `θ`-neighbourhood.
* **FR-GF-6** (2627-2629) "a chosen thin positive-pushoff annulus" = any `IsPushoffAnnulus` of `L`
  (row 84's notion, sm-3:2490-2502); "thin" imposes no extra condition; the conclusion is quantified
  over all such annuli, which the proof supports (2773-2779).
* **FR-GF-7** (2629-2630) oriented knot type as in §2.4 (parametrized ambient isotopy class).
* **FR-GF-8** (2615) `L_g` is identified with the parametrized `Φ 1 ∘ L` (2632 "`Φ_a∘L`"); no
  reparametrization is allowed at the end of the contact isotopy.

Decision D-F15: FR-GF-2 (compact support inside IsContactIsotopy, produced by the printed proof and consumed at sm-3:3480-3481) is a deliberate, disclosed strengthening of the row-87 conclusion; FR-GF-7 renders "oriented topological knot type" as the compactly supported ambient-isotopy class of the parametrized oriented embedding (the consumer's usage at 3476-3490) — to be judged by the reviewers.

## fd:contact-motions (row 86) ACCEPTED; ce:rounding (row 89) lane PROVED — 2026-09-14 ~09:40Z (pod executor)

Row 86: review 3/3 faithful (two with zero discrepancies), 2 refuters clean (work/reviews/fd-contact-motions.json); accepted 09:37Z;
checker restarted (log work/checks/checker-run-0940.log). Progress 09:37Z: claims verified 94/132, checklist 152/192.
Row 89: all five units proved all 33 leaves (P 3, G 10, C 7, L 9, E 4; no false leaf; CE-R10 probe confirmed mem_Icc_of_u_mem true in
the decreasing case); assembler produced work/drafts/cerounding/CeRounding_Assembled.lean (0 sorry, `#print axioms SM.ce_rounding` =
standard, Statements_FINAL byte-identical inside, 14 prefixed helpers, no clashes; ASSEMBLY_REPORT.md). Pre-review (PREREVIEW.md):
SATISFIABLE, no blocking issue; NonVacuity.lean (imports SM.CeSmoothingRecord only, 0 sorry, standard axioms) kernel-checks the round
circle at height 0 as a CuspedProjection, RegularGenericProjection, its constant CleanCuspSmoothing (WITH collar) and constant
CuspRoundingFamily (row 90's K-3 non-vacuity), plus heights_distinct_of_embedded (CE-R3) and eq_of_no_cusps. Pre-review additions to the
risk list, recorded BEFORE mapping: CE-R12 (= row 90's K-5) IsDisc is a CONVEX compact disc for the clean cusp neighbourhood — an
unprinted restriction inherited from the accepted vocabulary; CE-R13 no kernel-checked CUSPED witness (the per-cusp fields of
CleanCuspSmoothing are exercised by the row's own proof, which constructs them for every cusp, but a standalone cusped example was not
built); CE-R7 addendum: bundle fields 2-6 quantify over any c (0 < c omitted, as CE-R8 says of the hypothesis). Unit pitfalls for the
record: Mathlib's strictMonoOn_of_deriv_pos / exists_deriv_eq_slope are outside the import closure of SM.CeSmoothingRecord + SM.Rounding
(Lagrange re-proved from Rolle as in SM/Curl.lean). Port next: work/lean/SM/CeRounding.lean (row) and SM/CeRoundingNonVacuity.lean
(evidence), after the running checker finishes.

## ce:rounding (row 89) ported and mapped: work/lean/SM/CeRounding.lean (+ SM/CeRoundingNonVacuity.lean) — 2026-09-14 ~09:44Z (pod executor)

CeRounding_Assembled.lean (1825 lines) ported verbatim (header only) as work/lean/SM/CeRounding.lean; NonVacuity.lean (325 lines) as
work/lean/SM/CeRoundingNonVacuity.lean (one docstring phrase reworded to avoid a command directive in prose; header records it). Clash scan
(namespace-aware, both files against work/lean): none. `lake build SM.CeRounding SM.CeRoundingNonVacuity` OK 09:40Z; axioms of
SM.ce_rounding standard. Mapped ce:rounding → SM.ce_rounding (implemented) 09:41Z; checker started (log work/checks/checker-run-0948.log).
Reviewer input: the module with all 122 theorem proofs stripped (definitions in full; compiles) — work/reviews/ce-rounding-reviewer-input-
statement.lean.txt; brief work/port/review_prompt_ce-rounding.md (CE-R1..CE-R13); review workflow launched (3 lenses + 2 refuters).
Checker 09:40Z (run 0940) passed with 152 mapped (row 86 accepted; receipt work/checks/dev-check-contactmotions-accepted.json).

## RegularPoleCount lane launched (row 88's gap) — 2026-09-14 ~09:50Z (pod executor)

Skeleton work/drafts/fd/RPC_Skeleton.lean (577 lines, compiles, 29 leaf sorries in units A 11 / B 8 / C 6 / D 4; 13 calibration lemmas
and the assembly PROVED; `SM.regularPoleCount : SM.RegularPoleCount` and the corollary `SM.crossing_formula_unconditional` depend on
sorryAx only through the leaves), plan RPC_PLAN.md (~1570 lines estimated; three numeric identities probed; C1 strict, C3 needs 0 < r,
C5 needs rOut < 1 — supplied by the glue; B4's det API shape least verified, fallback given). Four prover units + assembler launched on
byte-identical copies RPC_U_{A,B,C,D}.lean. Plan for row 88 once the lane lands (D-F14 → D-F16): SM/LinkingCalculus.lean is UNMAPPED
library material (no accepted declaration), so its conditional bundle will be renamed (LinkingCalculusDataOf / fd_linking_calculus_of)
and a new row module SM/LinkingCalculusRow.lean (imports SM.LinkingCalculus + the ported SM.RegularPoleCount) will declare the
unconditional `SM.LinkingCalculusData` (same nine fields, crossing_formula without the antecedent) and `SM.fd_linking_calculus`;
then map, checker, review (readings FR-LC-1..9 already recorded).

## ce:rounding (row 89) ACCEPTED — 2026-09-14 ~09:53Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/ce-rounding.json; all notes non-blocking and among CE-R1..CE-R13, plus: "oriented
decorated data" rendered as same_doubles + sign equality + height-order iff, plane position / velocities being theorems; open-interval
disjointness with closed disjointness from clean_in; docstring citation nit 3029-3062 → 3029-3058). Accepted 09:53Z; checker restarted
(log work/checks/checker-run-0953.log). Row 91 cp:finite-contact-path now has both its inputs (89, 90) accepted and remains blocked ONLY by
GAP-2 (ambient isotopy ⇒ LinkEquiv); row 94 fd:contact additionally waits on 84, 87, 88, 93.

## Row 91 "modulo the descent clause" lane commissioned — 2026-09-14 ~10:02Z (pod executor)

With rows 89 and 90 accepted on the shared vocabulary, the GAP-2 row 91 cp:finite-contact-path is now blocked only by the descent clause
(ambient isotopy ⇒ equal polynomials = Reidemeister's theorem for spatial isotopies; SM.AmbientIsotopyDescent in the GAP-2 memo). An
architect agent is restating ContactPathData and AmbientIsotopyDescent on the accepted vocabulary and skeletonising
`SM.cp_finite_contact_path_of_descent : AmbientIsotopyDescent → ContactPathData` (concatenated family, row-90 record transport, P via
record isomorphisms). Such a conditional theorem is library material (D-F11/D-F14 pattern): it will be ported after review of its
statement but never mapped as implemented unless GAP-2 closes; its fidelity risks FR-CP-* will be recorded before the row is stated.

## Rows 84 and 87 prover lanes launched — 2026-09-14 ~10:08Z (pod executor)

Skeletons by the feasibility agent: work/drafts/fd/TN_Skeleton.lean (959 lines, 40 leaves in units A chart / B forms+Moser field / C
suspended flow / D model H = F∘Φ₁ / E Legendrian+annulus / F ambient isotopy; statement part byte-identical to
TransverseNeighborhood.lean 67-238; Moser identities proved; numerical truth checks in TN_PLAN.md §0) and GF_Skeleton.lean (625 lines,
26 leaves in units P0-P6; statement part byte-identical to GenericFront_Statement.lean 79-255; two leaves corrected before proving:
P5.4 needs f′(y₀) = 0 and f″(y₀) = 2A, P5.6 needs Ψ contact — GF_PLAN.md §3). Six + seven prover units and two assemblers launched on
byte-identical copies TN_U_{A..F}.lean, GF_U_{P0..P6}.lean. Row 87's statement carries the disclosed strengthening FR-GF-2 (compact
support inside IsContactIsotopy) and the knot-type reading FR-GF-7 (compactly supported ambient isotopy class of the parametrized
oriented embedding) — decision D-F15 above.

## RegularPoleCount PROVED; row 88 fd:linking-calculus restated UNCONDITIONALLY and mapped (decision D-F16, supersedes D-F14) — 2026-09-14 ~10:20Z (pod executor)

Lane result: all 29 leaves proved (A 11, B 8, C 6, D 4; no false leaf; unit pitfalls in RPC_U_*_REPORT.md — e.g. the IFT layer
HasStrictFDerivAt.toOpenPartialHomeomorph is outside the skeleton's import closure, replicated via ApproximatesLinearOn); assembler
work/drafts/fd/RPC_Assembled.lean (1297 lines, 0 sorry, `#print axioms SM.regularPoleCount` and `SM.crossing_formula_unconditional` =
standard; no clashes; RPC_ASSEMBLY_REPORT.md). Ported verbatim (header only) as work/lean/SM/RegularPoleCount.lean.
Restructuring (no accepted declaration touched — SM/LinkingCalculus.lean was unmapped library material): its conditional bundle and
theorem renamed LinkingCalculusDataOf / fd_linking_calculus_of (header records the edit); new row module work/lean/SM/LinkingCalculusRow.lean
declares `SM.LinkingCalculusData` (the nine fields byte-identical except that crossing_formula no longer takes `RegularPoleCount →`) and
`SM.fd_linking_calculus : LinkingCalculusData` (each field from fd_linking_calculus_of; crossing_formula discharged by regularPoleCount).
`lake build` OK; mapped fd:linking-calculus → SM.fd_linking_calculus (implemented) 10:20Z; checker started (log work/checks/checker-run-1020.log).
Reviewer input: the row module with the row proof stripped — work/reviews/fd-linking-calculus-reviewer-input-statement.lean.txt; the
reviewer may read SM/LinkingCalculus.lean as the definitions module (helper proofs not under review); brief
work/port/review_prompt_fd-linking-calculus.md (FR-LC-1..9); source excerpt lines 2785-2826. The degree formula is proved by a different
argument from the printed disc-deletion one (bump primitive + change of variables), which is a proof difference, not a statement difference.

## Row 91 cp:finite-contact-path PROVED MODULO the descent clause; fidelity risks recorded BEFORE the statement is ported — 2026-09-14 ~10:26Z (pod executor)

Architect result (work/drafts/gap2/CPRow91_Statements.lean 182 lines, CPRow91_Skeleton.lean 685 lines, CPRow91_PLAN.md): every leaf provable now — `SM.cp_finite_contact_path_of_descent : AmbientIsotopyDescent → ContactPathData` is a THEOREM (0 sorry; axioms standard + lit_homfly, lp_lm, lp_lm_uniqueness through presentations / P_eq_homfly), with corollaries from the LinkEquiv form (Reidemeister proper) and from the printed split AmbientIsotopyDescentLit ∧ IsotopyExtension. Decision D-CP-1: the clause consumed is the homfly form — for a SpatialFamily H whose two ends have RegularGenericProjections, any polygonal readings X₀, X₁ (HeightMarking) have homfly X₀ = homfly X₁; it is lit:homfly's descent clause read on spatial isotopies, which the frozen SM.lit_homfly states over LinkEquiv (design D2), so deriving it is Reidemeister's theorem — out of scope, no sixth axiom. Key finding FR-CP-2: the printed proof treats D_ε as having a polynomial; on the accepted layer a polygonal reading of p(L₁) must be constructed — the skeleton shows the diagram S of the clean smoothing S(F) also carries D_ε (record transport through the projection), so the row asserts no carrier existence. Fidelity risks (verbatim from CPRow91_PLAN.md §5):
- **FR-CP-1 (tex 3221-3230; FR-1/GAP-1, = CE-R1).**  "D_T is an ordinary finite regular generic
  diagram" and "S(F)" are SMOOTH diagrams; `P` exists only on polygonal `Diagram`s, so both are read
  through `HeightMarking` and the row is quantified over the readings (`Nonempty (… HeightMarking …)` as
  hypotheses, the shape of the accepted row 90).  No existence of a polygonal carrier is asserted; for a
  smoothing/endpoint without a reading the row says nothing.  Same reading as def:transverse-front,
  ng:front-domain, rows 89/90.
- **FR-CP-2 (tex 3238-3239, 3243-3251).**  The printed proof uses "the diagram D_ε" of `L_1` as if it
  had a polynomial; here `P_{D_ε}` is `P Xε` for a reading `Xε` of `p(L_1)`, and the proof CONSTRUCTS one:
  the polygonal diagram `S` carrying `S(F)` also carries `D_ε` (unit C).  So display cp:smoothing-record is
  realised by the accepted row 90 applied to `Xε := S` (where it is `P S = P S`) — the content of
  ce:smoothing-record is absorbed into the transport `toSmoothing`, which is the same record-isomorphism
  argument (the accepted `ofSmoothing` reversed).  Fidelity is intact (the printed sentence "the two
  actual diagrams have identical named decorated records" is exactly what `readingOfSmoothing` states),
  but a reviewer should know the step is not a black-box citation of row 90 alone.
- **FR-CP-3 (tex 3254-3257).**  The printed `η` ("smooth and increasing, endpoint values 0, 1, every
  positive-order derivative zero at both endpoints; e.g. the normalized integral of exp(−1/(s(1−s)))") is
  `Real.smoothTransition` (Mathlib): `C^∞`, `0` on `(−∞,0]`, `1` on `[1,∞)`, values in `[0,1]`,
  monotone.  Strict increase is not used by the proof and not asserted.
- **FR-CP-4 (tex 3258-3264; = CE-R2).**  The printed `H_s` lives on `[0,1]`; `SpatialFamily` is indexed
  by all of `ℝ` and demands embedded regular slices everywhere.  `contactPath` is defined on `ℝ`, equals
  `L_1` for `s ≤ 0` and `T` for `s ≥ 1` (constant outside `[0,1]`), and its slices are exactly the
  `L_λ`, `G_t` with `λ, t ∈ [0,1]` (B-17).  Joint smoothness at the join is proved by the identity
  `H = A + B − L` in `ℝ³`, not by the printed vanishing of one-sided time derivatives — the same fact.
- **FR-CP-5 (tex 3221-3223).**  "a supplied jointly smooth family of oriented spatial embeddings G_t" is
  a `SpatialFamily` on ALL of `ℝ` — a hypothesis STRONGER than a family on `[0,1]` (a narrowing of the
  row's domain).  Any printed family on `[0,1]` becomes one by the clamp `t ↦ smoothTransition t`
  (as row 89 does, CE-R2), so nothing is lost, but the consumer (fd:contact / cf:thm-carrierfloor (C))
  must supply the family in this form.  Row 89's output is already of this form.
- **FR-CP-6 (tex 3223-3225).**  "ends at T, whose specified xz projection D_T": `T := F.G 1` and its
  "specified" diagram is `(F.G 1).RegularGenericProjection` read with `T`'s OWN heights (over = smaller
  `y` of `T`, the fd:contact convention sm-3:3406-3407) — `(F.G 1).HeightMarking (F.G 1).projLoop X`.
  Nothing else is "specified" by the text.
- **FR-CP-7 (tex 3264-3316).**  The isotopy-extension construction (normal charts, uniform normal
  radius, weighted normal extension of `∂_s H_s`, compactly supported field, ODE flow, orientation) is
  NOT formalised: the hypothesis `AmbientIsotopyDescent` is stated on the smooth FAMILY OF EMBEDDINGS,
  so it absorbs that step together with the literature premise.  The split is recorded
  (`AmbientIsotopy`, `AmbientIsotopyDescentLit`, `IsotopyExtension`, `cp_finite_contact_path_of_lit`);
  `IsotopyExtension` is true and provable in principle (its own lane if ever wanted).  `AmbientIsotopy`
  includes `compact_support` and smooth two-sided inverses, exactly what the printed flow delivers
  ("fixes the complement of a compact set and preserves ambient orientation" — orientation preservation
  follows from `start` by connectedness and is not a field).
- **FR-CP-8 (tex 3313-3316; THE GAP).**  "The retained global source premise yields H_{D_ε} = H_{D_T}"
  is consumed as the hypothesis `hdesc : AmbientIsotopyDescent`; the frozen `SM.lit_homfly` cannot
  supply it (§1).  The row theorem is CONDITIONAL and, per D-F11/D-F14, may be ported as library
  material after statement review but is NEVER mapped as implemented while GAP-2 is open.
- **FR-CP-9 (tex 3211, 3230; = CE-R8/K-6).**  `0 < c` ("nonempty") is a hypothesis of every field but is
  used by no proof (row 90's `source_and_polynomial` takes it and ignores it); "oriented" = parameter
  direction (T-1); "smooth embedding with nonvanishing parameter derivative" = `embedded` + `regular`
  (injective immersion of compact circles); the hypothesis fields 1-5 are read-backs of the structures
  (the accepted `CeRoundingData` pattern, CE-R7).
- **FR-CP-10 (tex 3231, 3319-3327).**  "No contact condition is imposed …" and the closing paragraph
  (cusped diagram at the join harmless because `H_s` is a spatial embedding throughout; the rounding is
  not Legendrian; no self-linking transported) are commentary: no field, nothing about `contactForm`
  or `sl` is stated.  The join slice `H_{1/2} = L` has a CUSPED projection and is a `SpatialLink` (B-16),
  which is all the descent clause needs of it.


Handling (D-F11/D-F14 pattern): statement review launched (3 lenses + 2 refuters, brief work/port/review_prompt_cp-finite-contact-path.md); after a clean review the conditional theorem is ported as library material (work/lean/SM/ContactPathOfDescent.lean) and NEVER mapped as implemented while GAP-2 is open; FINAL_REVIEW will carry PLAN §6's paragraph. Row 91 stays pending.

## fd:linking-calculus (row 88) ACCEPTED — 2026-09-14 ~10:37Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/fd-linking-calculus.json; non-blocking notes among FR-LC-1..9 plus docstring nits of the
definitions module). Accepted 10:36Z; docstring-only edits to the unaccepted library module SM/LinkingCalculus.lean right after (header,
citation 2785-2830 → 2785-2826, the "main declaration" paragraph now pointing to SM/LinkingCalculusRow.lean; a remaining sentence at
~line 526 "this Stokes-type argument is not formalised here" is still true of that module — the formula is proved in SM/RegularPoleCount.lean;
to reword at a layer rebuild); rebuilt; checker restarted (log work/checks/checker-run-1036.log). Progress 10:37Z: claims verified 96/132,
checklist 154/192. The fd block now stands: 85, 86, 88 accepted; 84 and 87 in prover lanes; 93 waits on 83 (certificate rows); 94 on 91 (GAP-2).

## Row 91 conditional theorem reviewed and PORTED as library; row 173 proved MODULO G11 and ported as library — 2026-09-14 ~10:52Z (pod executor)

Row 91: statement review of `SM.cp_finite_contact_path_of_descent : AmbientIsotopyDescent → ContactPathData` — 3/3 faithful, 2 refuters clean
(work/reviews/cp-finite-contact-path-conditional.json; raw in …-review-workflow-raw.json). Key reviewer finding (FR-CP-7 sharpened): the clause
AmbientIsotopyDescent is stated on a smooth family of embeddings and therefore absorbs the isotopy-extension step the printed proof performs
by hand (sm-3:3264-3313) together with the literature premise (3313-3316); the proved split AmbientIsotopyDescentLit ∧ IsotopyExtension →
AmbientIsotopyDescent records this. So the honest label is "row 91 proved modulo Reidemeister's theorem for SMOOTH isotopies (literature
premise + isotopy extension)". The docstring sentence claiming "exactly what the printed proof consumes at 3313-3316" was corrected to cite
3264-3316 at port time (docstring-only edit of an unaccepted draft). Ported as work/lean/SM/ContactPathOfDescent.lean (library; NOT mapped;
`lake build` OK 10:50Z; no clashes). FINAL_REVIEW paragraph: work/drafts/gap2/CPRow91_PLAN.md §6 (to be adjusted for the sharpened label).
Row 173: wave-3 unit W3_GT (work/drafts/rlane2/W3_GT_REPORT.md) proved fields endpoint_rows_canonical / endpoint_rows_relabelled and the
abstract endpoint transport in full, and the field empty_row (hence the whole row: `RProof.GT_generic_transport_of_G11`) MODULO the open
fact `GT_G11` — HOMFLY invariance of the distinguished carrier's grouped diagram across the RIII wall (the printed "ordinary oriented
Reidemeister III move on D_P followed by a record isomorphism"); the accepted library has only the geometric SM.homfly_reidemeister_III
(needs an RIIIData disc site) and record-isomorphism transport, no record-level RIII invariance. Portable file RLaneX1Rows3.lean (3354
lines, no sorry, axioms standard + lit_homfly/lp_lm/lp_lm_uniqueness) ported as work/lean/RProof/X1Rows3.lean (library; row 173 NOT
mapped; no clashes; built 10:50Z). A G11 architect (design + skeleton; recommended route: six-vertex flat subdivision of the lift, translate
the middle strand inside a disc, verify RIIIData, record iso via GT_homfly_wall_gen; est. 1500-3000 lines) has been commissioned; if it
lands, row 173 is proved, mapped and reviewed. Rows 174/176/177 remain GAP-2; 175 remains blocked by CV:singleton_D_i; so RProof.cv_R and
Bridge.theorem stay incomplete regardless.

## Row 84 fd:transverse-neighborhood PROVED (lane result) — 2026-09-14 ~10:55Z (pod executor)

Units A-F proved 39 of 40 leaves; leaf C2 `hasCompactSupport_Yfield` was FALSE as stated (the suspended field's first component χ_τ(τ) = 1
on {0} × ℝ × ℝ²; kernel-checked counterexample tc2_not_hasCompactSupport_Yfield). It was an internal construction lemma, not part of the
row statement; the assembler applied unit C's repair with no statement change: isGlobalFlow_Theta re-proved from boundedness + global
Lipschitz (row-86 exists_isGlobalFlow), contDiff_Theta from the general lemma tc9_contDiff_uncurry_of_bounded (joint smoothness of the flow
of a smooth bounded field via a bump cut-off + ODE uniqueness + ContactMotions.contDiff_uncurry), C2 removed. Assembled
work/drafts/fd/TN_Assembled.lean 3150 lines, 0 sorry, `#print axioms SM.fd_transverse_neighborhood` = standard; statement part
byte-identical to TransverseNeighborhood.lean 67-238; no clashes (TN_ASSEMBLY_REPORT.md). Ported as work/lean/SM/TransverseNeighborhood.lean,
mapped fd:transverse-neighborhood → SM.fd_transverse_neighborhood (implemented); checker started (log work/checks/checker-run-1055.log);
reviewer input = module with every theorem proof stripped; brief work/port/review_prompt_fd-transverse-neighborhood.md (FR-TN-1..7).
D-F13 is now fully superseded (rows 84 and 86 both unconditional).

## fd:transverse-neighborhood (row 84) ACCEPTED — 2026-09-14 ~11:16Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/fd-transverse-neighborhood.json; non-blocking notes within FR-TN-1..7, listed there).
Accepted 11:16Z; checker restarted (log work/checks/checker-run-1116.log). The fd block now: 84, 85, 86, 88 accepted; 87 in its prover lane;
93 waits on 83 (certificate rows); 94 waits on 91 (GAP-2) and 87/93. Progress: claims verified 97/132.

## G11 (row 173's gap) judged HARD but FEASIBLE; skeleton written — 2026-09-14 ~11:30Z (pod executor)

Architect result: work/drafts/rlane2/G11_Skeleton.lean (1018 lines, imports RProof.X1Rows3, compiles, 49 leaf sorries in groups A carrier→
config 18 / B subdivision 6 / C moved polygon 6 / D disc + RIII site 10 / E record twist 1 / P parameters 1 / F assembly 4 / X branches 3),
G11_PLAN.md, G11_probe.py (20 000 random configurations, 0 violations for the geometric leaves C2/C4/D9). Route (no Deform): subdivide the
moved strand by three flat vertices (accepted CS3 appendVertex lemmas), move one vertex to an apex beyond the triangle so the outside match
is the identity on traversal points, disc = homothetic enlargement of the triangle, verify RIIIData, then the record twist (three adjacent
transpositions) matched with D_E via ExactTriangleVisitOrders and gausscode_polynomial. Statement-level finding: the wave-3 `def GT_G11`
lacks the hypothesis that the three triangle pairs are crossings of P; with exactly two crossings present its hypotheses are contradictory
only by Gauss parity (not in the library). Decision D-G11: the row `RProof.generic_transport` (exact sibling-row shape; not previously
declared anywhere in work/lean) is derived through the strengthened `GT_G11_strong` (= GT_G11 + the three IsCrossing clauses), which the
RIII route proves; the literal GT_G11's two-crossing branch (leaf X2, needs parity) is NOT on the row's path and may stay unproved (dropped
at port time). GenericTransportData (the accepted statement panel) is unaffected. Size estimate 3 500-5 500 lines (precedents: curl K2
4 000, smoothing splice 4 600). The architect is applying a local reformulation of two clearance leaves (A8/A15) before the units start;
then 6 prover units + assembler.

## G11 prover lane launched (row 173) — 2026-09-14 ~11:48Z (pod executor)

Skeleton revised: clearance leaves in the local form (clear_frontier + clear_vertex, with the proved glue G11_Config.clear_edge via
preconnectedness of the edge segment); X2 and the two literal-GT_G11 declarations marked NOT ON THE ROW'S PATH; 1086 lines, 49 leaves,
compiles; probe re-run 0/20 000 violations. Six units U1-U6 (7/14/9/9/4/5 leaves, PLAN §7) + assembler launched on byte-identical copies
G11_U1..U6.lean. Assembly target: RProof.generic_transport derived through GT_G11_strong (axioms expected = the accepted sibling rows').

## Row 87 fd:generic-front PROVED (lane result), ported and mapped — 2026-09-14 ~11:55Z (pod executor)

Units P0-P6 proved 25 of 26 leaves; leaf P2.2 `stage1_stable` was FALSE as stated (same-width collar persistence: the probe curve
L = (sin 2θ, sin θ, cos θ − cos 3θ/3) has a double point at circular distance exactly π = δc that every nearby H^x perturbation moves inward;
GF_U_P2_REPORT.md §2, GF_U_P2_probe.py). It was an internal construction lemma, not part of the row statement; the assembler removed it and
re-proved its only consumer `step2` (statement unchanged) with the true half-width form gp2_stage1_stable_of_lt (δ′ < δc) — the same
repair pattern as row 84's C2. Design deviation in P1.1 (statement unchanged): two global Hamiltonians χ·cos y, χ·sin y (Wronskian minor y′³)
instead of per-cusp bumps. Assembled work/drafts/fd/GF_Assembled.lean 5411 lines, 0 sorry, `#print axioms SM.fd_generic_front` = standard;
statement part byte-identical to GenericFront_Statement.lean 79-255; no clashes (one short-name shadow SM.GenericFront.SameParam vs
SM.SameParam, different types, no ambiguity; GF_ASSEMBLY_REPORT.md). Ported as work/lean/SM/GenericFront.lean (`lake build` OK 11:53Z),
mapped fd:generic-front → SM.fd_generic_front (implemented); checker started (log work/checks/checker-run-1152.log); reviewer input = the
module with every theorem proof stripped; brief work/port/review_prompt_fd-generic-front.md (FR-GF-1..8, D-F15). The whole fd block is now
proved: 84, 85, 86, 88 accepted, 87 under review; 93 waits on 83; 94 on 91 (GAP-2).

## fd:generic-front (row 87) ACCEPTED — 2026-09-14 ~12:15Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/fd-generic-front.json; non-blocking notes within FR-GF-1..8 / D-F15, listed there).
Accepted 12:15Z; checker restarted (log work/checks/checker-run-1215.log). The fd block: 84, 85, 86, 87, 88 accepted; 93 waits on 83
(certificate rows lane); 94 fd:contact waits on 91 (GAP-2) and 93. Progress: claims verified 98/132.

## Remaining pending rows surveyed; feasibility probe opened for rows 57 / 104 — 2026-09-14 ~12:20Z (pod executor)

Pending after row 87: 36 checklist rows. In lanes: 76-83 (certificate rows, wave 2 finishing), 173 (G11 lane). Reachable after them: 93
(fd:ng-bound, restates 83 in self-linking form — lane once 83 lands). GAP-2-blocked (via 91 → 94 → 99 → 100 → 103/110, and 105 → 112 →
122/127/128 → 184; 155 via 162 → fd:contact; 165/174-178 → 183 → 184): 21 rows. Not GAP-2 but deferred: 57 lem:gauss-two-discs (PL
Jordan–Schoenflies) and its sole non-GAP-2 consumer 104 cb:embedded-rotation (rotation ±1 of an embedded regular polygon; the printed proof
cites 57 only for a straight triangulation of the bounded region). Row 161 CV:ax:etnyre: D-F10 (iii) — no separate object; its content is
the composite CV.SlBoundData with 162 (GAP-2). Given the lane machinery's record today (3-5.5k-line proofs in a few hours), the early
deferral of 57/104 is re-examined by a bounded feasibility probe (work/drafts/pldiscs/PLDISCS_FEASIBILITY.md): row 104 possibly provable
directly (turning number of a simple polygon = ±1, e.g. two-ears induction) without the full two-disc theorem; row 57's clauses
assessed one by one. Reachable ceiling without GAP-2: 98 + 9 (76-83, 93) + 1 (173) = 108, +2 if 57/104 land.

## Certificate rows wave 2 done: rows 81 and 82 proved inside the merged skeleton; wave 3 launched — 2026-09-14 ~12:30Z (pod executor)

Wave-2 units: U3 proved all five record leaves (comm_recordIso, zigzag_recordIso, circle_recordIso_addFree, skein_site, skein_unique; 331
helper declarations; design deviation: first returns conjugated to the active superset ActE rather than a bijection of all slots),
U4 delivered the geometry-core API (polygon discs from half-planes, moved slot diagram, Clean, genericity, MatchData, arcs, exits, congruences;
190 declarations, no leaves), U8D proved the three deformation leaves (deform_downCount, deform_writhe, deform_P; six Mathlib imports
added), U8R reduced `represent` to the single Prop `U8R.SweepStatement F` (record layer and first analytic layer proved) — the sweep proper
remains (5.5-8k lines estimated). Merger: work/drafts/frontrows/Skeleton_W2.lean (14 891 lines, compiles, 5 leaf sorries: typeIII_site,
typeII_move, typeI_move, crossedCusp_move, represent); rows 81 SM.ng_circle and 82 SM.ng_cusp_skein are sorry-free in it (axioms standard
+ SM.lp_lm); 76-80, 83 wait on the leaves (MERGE2_REPORT.md). Launched: wave 3a (U5 typeIII_site → row 79; U6 typeII/typeI/crossedCusp →
rows 78/77/80; merger → Skeleton_W3.lean); a sweep architect (leaf skeleton for SweepStatement, then prover units → rows 76, 83, then 93);
an extraction of a sorry-free module FrontRows_W2_Clean.lean for rows 81/82 (to port/map/review now; the later delta module will import
it). Decision D-FR1: the certificate rows are ported incrementally as sorry-free modules (clean subset now, delta modules as leaves close),
never a file containing a sorry.

## Rows 57 / 104 probe: 104 FEASIBLE without 57 (~2.5k lines), 57 INFEASIBLE now (12-20k); fidelity risks for 104 recorded BEFORE the row is stated — 2026-09-14 ~12:45Z (pod executor)

Memo work/drafts/pldiscs/PLDISCS_FEASIBILITY.md; statement work/drafts/pldiscs/EmbeddedRotation_Statement.lean (typechecked); leaves EmbeddedRotation_Leaves.lean. Row 104 cb:embedded-rotation: the STATEMENT does not cite row 57 (only the printed proof does, for a triangulation); route = polygonal secant lift (Hopf Umlaufsatz on the accepted rotationNumber / principalTurn / IsLiftOn layer): base the polygon at a supporting vertex, lift the secant direction on the convex region ½ ≤ t − s ≤ n − ½ with the accepted exists_lift_of_unit, telescope around the region's boundary: Σϑ = 2I + 2ϑ₀ with |I| ≤ π and I ≡ π − ϑ₀, hence Σϑ = ±2π; identity checked numerically on random non-convex simple polygons. New vocabulary: Embedded P (nonzero edges, remote segments disjoint, consecutive segments meet exactly in the shared vertex — flat vertices allowed as sm-3:4791 requires), IsSupportingVertex. Decision D-ER1: 104 is proved INDEPENDENTLY of 57 (DEPENDENCIES.json lists 57 under 104 only for next-unit selection; the accept note will say so). Row 57 lem:gauss-two-discs stays DEFERRED (clause 57a two regions HARD 4-6k; 57b PL discs = PL Schoenflies 5-8k with new PL vocabulary; 57c/d extensions cheap only on convex model discs; 57e sphere 1.5-2.5k; Mathlib has no Jordan / winding number / planar Euler / triangulations) — correction to the earlier note: the topological-extension clause is the easy one, the Schoenflies content is 57b. Fidelity risks for row 104 (verbatim from the memo §1.8):
### 1.8 Fidelity risks (row 104)

* **FR-ER-1** (4762 "embedded"): rendered as the simple closed polygonal curve `Embedded P` on
  def:polygon vocabulary, wider than "generic with `m = 0`" (flat vertices allowed, as 4791 requires);
  the narrower consumer form is reached by the bridge leaf.  Reviewers should confirm `Embedded` is
  what "embedded" means at 4762 (the proof's "the region is an embedded disc", 4792, agrees).
* **FR-ER-2** (4762-4764 "according to its traversal orientation around the bounded complementary
  region"): the bounded complementary region is not defined in the accepted layer (it is row 57's
  object); the sign clause is read at supporting (convex-hull) vertices, where the bounded region lies on
  the polygon's side and a left turn means "bounded region on the left".  Consumers use only `|r| = 1`
  (4811).  A global rendering (winding number of `P` about a point just inside a supporting vertex
  equals `rot`, and vanishes far away) would cost ≈ 800–1 200 more lines and is not proposed.
* **FR-ER-3** (4762 "regular"): `Regular P` is kept as a hypothesis although `Embedded P` implies it
  (leaf `Embedded.regular`); harmless.
* **FR-ER-4** (4797-4798 "the opposite traversal negates every turn and gives −1"): not a separate field;
  it is lem:rot (iii) `rotationNumber (reversal P) = -rotationNumber P` in `SM.rotation_number`, and the
  sign clause covers both orientations through the sign of the supporting turn.
* **FR-ER-5** (4765-4767): the proof route differs from the printed one (no row 57, no Euler count).
  `blueprint/DEPENDENCIES.json` lists `lem:gauss-two-discs` under `cb:embedded-rotation`; `tools/claims.py`
  uses that column only to pick the next unit (not a checker gate), so the accept must record "proved
  independently of row 57" in the review brief and AUTHOR_NOTES.
* **FR-ER-6** (4791 "including zero at a straight subdivision"): flat vertices are in the domain and
  the sector lemma yields increment 0 for a positively collinear pair, as printed.
* **FR-ER-7**: `IsSupportingVertex` uses the Euclidean `planeDot` with `N` pointing into the polygon's
  half-plane; the lowest-leftmost vertex is supporting for `N = (1, 0)`.


The probe agent is assembling a single skeleton (statement + leaves + row proved from the leaves, 3 units); prover lane next.

## Rows 81 ng:circle and 82 ng:cusp-skein ported (clean wave-2 module) and mapped — 2026-09-14 ~12:58Z (pod executor)

work/drafts/frontrows/FrontRows_W2_Clean.lean (14 665 lines = Skeleton_W2.lean minus the five open leaves and their 23 dependents — rows
76-80/83 statements and theorems, P_type*/P_crossedCusp, certificate_laws, word_bound; W2_CLEAN_REPORT.md lists the removed ranges for the
delta module) ported verbatim (header only) as work/lean/SM/FrontRowsW2.lean; `lake build` OK 12:52Z (50 s); axioms of SM.ng_circle and
SM.ng_cusp_skein = standard + SM.lp_lm; clash scan 0. Mapped ng:circle → SM.ng_circle, ng:cusp-skein → SM.ng_cusp_skein (implemented);
checker 12:56Z passed with 158 mapped (receipt work/checks/dev-check-frontrowsw2-implemented.json). Reviewer input: the module with all 936
theorem proofs stripped (definitions in full; new stripper work/port/strip_proofs.py — block detection by column-0 lines and bracket-depth
split, after two failures on `(W := W)` named arguments and `omit … in` prefixes) — work/reviews/ng-circle-cusp-skein-reviewer-input-
statement.lean.txt (compiles). Briefs cite FR-1/FR-5 (accepted) and FR-8, FR-11, FR-12, FR-13, FR-14, FR-15 (recorded in the frontrows
design entry). Note for the delta module: the six row-statement structures of rows 76-80/83 were removed from the clean module and must
be re-declared verbatim there.

## Row 104 cb:embedded-rotation prover lane launched — 2026-09-14 ~13:05Z (pod executor)

Skeleton work/drafts/pldiscs/EmbeddedRotation_Skeleton.lean (411 lines, compiles, 23 leaf sorries in units A traversal/embeddedness 11, B
lift + increment lemmas 7, C boundary telescoping 5; assembly and the row theorem SM.cb_embedded_rotation PROVED from the leaves;
statement part byte-identical to EmbeddedRotation_Statement.lean 22-54), plan ER_PLAN.md (truth checks: Σϑ = 2I + 2ϑ₀ on random simple
polygons incl. flat vertices and an L-shape; sector lemma and half-plane bound on 2 000 random paths). Three units + assembler launched on
copies ER_U{A,B,C}.lean. Fidelity risks FR-ER-1..7 recorded above (12:45Z); decision D-ER1 (proved independently of row 57).

## Rows 81 ng:circle and 82 ng:cusp-skein ACCEPTED — 2026-09-14 ~13:10Z (pod executor)

Reviews 3/3 faithful each, 2 refuters clean each (work/reviews/ng-circle.json, ng-cusp-skein.json; non-blocking notes = the disclosed
readings FR-8, FR-11, FR-12, FR-1/FR-16 and the adjacency reading of "separated"). Accepted 13:10Z; checker restarted (log
work/checks/checker-run-1310.log). Certificate rows remaining: 77-80 (wave 3a running), 76 and 83 (sweep lane), then 93.

## Row 104 cb:embedded-rotation PROVED (lane), ported and mapped — 2026-09-14 ~13:20Z (pod executor)

All 23 leaves proved (A 11, B 7, C 5; no false leaf; A8 much simpler than planned); assembler work/drafts/pldiscs/EmbeddedRotation_Assembled.lean
(0 sorry, `#print axioms SM.cb_embedded_rotation` = standard, statement part byte-identical, no clashes; ER_ASSEMBLY_REPORT.md). Ported as
work/lean/SM/EmbeddedRotation.lean (`lake build` OK 13:17Z), mapped cb:embedded-rotation → SM.cb_embedded_rotation (implemented; proved
independently of row 57 — D-ER1); checker started (log work/checks/checker-run-1320.log). Reviewer input = module with all 51 theorem proofs
stripped (compiles); brief work/port/review_prompt_cb-embedded-rotation.md (FR-ER-1..7; the reviewers are asked to judge FR-ER-2 — the
supporting-vertex reading of "traversal orientation around the bounded complementary region" — explicitly). Checker 13:14Z (run 1310)
passed with 158 mapped (rows 81/82 accepted; receipt work/checks/dev-check-frontrowsw2-accepted.json).

## Sweep lane launched (leaf `represent` → rows 76, 83) — 2026-09-14 ~13:30Z (pod executor)

Architect result: work/drafts/frontrows/W3_U8R_Skeleton.lean (15 587 lines = Skeleton_W2.lean + one U8R sweep block; `represent` PROVED
as represent_of_sweepStatement F (sweep_proof F); sweep_proof PROVED from 54 leaf sorries in units S1 cut 16 / S2 cusp 5 / S3 crossing 1 /
S4 word 17 / S5 Φ 4 / S6 traversal 11; compiles), plan W3_U8R_PLAN.md (route, definitions, truth checks — cusp sign law on 1692 random
germs, over = smaller slope, letter bits vs IsDownCusp — per-leaf table, dependencies, decisions §5, doubtful leaves §6; one false draft
leaf ΦFun_eq_slotAt removed before freezing). Estimate ≈ 9.9k lines (8-11k; the wave-2 estimate 5.5-8k was optimistic). Eight prover
units (S1a/S1b, S2, S3S5, S4a/S4b, S6a/S6b) + merger launched on copies W3S_*.lean. Final assembly plan: Skeleton_W2 + wave-3a hunks
(U5/U6) + the sweep hunks = one file; the delta module for rows 76-80, 83 imports the ported SM/FrontRowsW2.lean (D-FR1).

## cb:embedded-rotation (row 104) ACCEPTED — 2026-09-14 ~13:40Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/cb-embedded-rotation.json; all notes non-blocking: FR-ER-1..5 as disclosed, the
non-vacuity field, [NeZero n], the labelled representative). Accepted 13:40Z; checker restarted (log work/checks/checker-run-1340.log).
Its consumer 105 lem:corner-values stays GAP-2-blocked (cb:singleton ← thm:floor). Row 57 stays deferred (infeasible now).

## Row 173 R:generic_transport PROVED (G11 lane), ported and mapped — 2026-09-14 ~14:30Z (pod executor)

G11 lane: units U1/U3/U4/U5/U6 proved all their leaves; U2 proved 12 of 14 and found two SKELETON bugs — leaves G11_clear and G11_cfg_hpq
lacked section variables (hG; hfg hcfg) that this Lean includes only when the statement mentions them, so as frozen they were false /
unprovable (probe counterexample: an 8-gon with a quadruple point; G11_U2_probe.py). The assembler applied the minimal repair: `include hG in`
/ `include hfg hcfg in` before the two internal leaves (theorem text byte-identical; call sites given the extra arguments), bodies from
U2's proved gu2_clear / gu2_cfg_hpq. These are internal construction lemmas; the row statement `RProof.generic_transport` is byte-identical
to the skeleton and to the sibling rows' shape; GenericTransportData (the accepted statement panel) untouched. Assembled
work/drafts/rlane2/G11_Assembled.lean (11 175 lines, 0 sorry; `#print axioms RProof.generic_transport` = standard + lit_homfly, lp_lm,
lp_lm_uniqueness — the accepted sibling set; X2 and the literal-GT_G11 declarations removed; imports added: two Mathlib affine modules +
SM.CS3; no clashes; G11_ASSEMBLY_REPORT.md). Ported as work/lean/RProof/GenericTransport.lean (`lake build` OK 14:24Z), mapped
R:generic_transport → RProof.generic_transport (implemented); checker started (log work/checks/checker-run-1425.log). Reviewer input: the
row module with all 1118 theorem proofs stripped (stripper extended for `let x := …` inside statements) — compiles; the bundle
GenericTransportData is reviewed with its row (brief work/port/review_prompt_r-generic-transport.md; spec = R_GENERIC_COMMON_TRANSPORT_PROOF.md
whole file). Remaining R rows: 175 (CV:singleton_D_i, blocked), 174/176/177 (GAP-2), 178/183/184 (all of the above).

## R:generic_transport (row 173) ACCEPTED — 2026-09-14 ~14:45Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/r-generic-transport.json; the bundle GenericTransportData of the accepted panel reviewed
with its row; all notes non-blocking — accepted R-row patterns and the disclosed readings). Accepted 14:45Z; checker restarted (log
work/checks/checker-run-1445.log). R rows now: 164, 166, 167, 168, 169, 170, 171, 172, 173 accepted; 175 blocked by CV:singleton_D_i (165 ←
CV:thm:carrierfloor, GAP-2); 174/176/177 GAP-2; 178 → 183 → 184 wait on all. Progress: claims verified 102/132.

## End-of-work preparation started — 2026-09-14 ~14:50Z (pod executor)

With the fd block, the R rows reachable without GAP-2 and rows 81/82/104 accepted, two agents prepare the closing artefacts in parallel with
the last lanes: (a) work/FINAL_REVIEW_DRAFT.md (the completed checklist of FINAL_REVIEW.md with per-row status, disclosed readings,
GAP-2 paragraph, deferrals, process) and (b) the work/delivery/ package skeleton (pins, declaration map, reviews, receipts, progress
history, README, refresh.sh) — both to be finalized after the certificate rows (77-80, 76, 83) and row 93 land; then `python3
tools/check_lean.py work/lean --all`, the final FINAL_REVIEW.md, and the delivery refresh. A row-93 architect prepares the statement and the
algebraic derivation from row 83 (NgBound_Statement.lean, NGBOUND_PLAN.md).

## Row 93 fd:ng-bound: statement and derivation prepared (waits only on row 83) — 2026-09-14 ~15:00Z (pod executor)

work/drafts/frontrows/NgBound_Statement.lean (122 lines, compiles, no sorry): bundle `SM.NgBoundClauses` (slNg_eq : slNg F = w − D as
integers; ng_input : ∀ F S, F.IsRounding S → F.slNg ≤ −degAZ (P S) − 1) and `fd_ng_bound_of (h83 : NgLocalFrontBoundClauses) :
NgBoundClauses` PROVED (row 83's front_inequality verbatim; `degAZ_P_isMaxDegA` certifies the "max deg_a" reading from P ≠ 0 and degAZ_spec;
cross-checks via the accepted defect_nonneg_iff_slNg). `SmoothFront.slNg` already exists in the accepted SM/FrontSmooth.lean:732 and is
reused; `NgLocalFrontBoundClauses` is re-declared byte-identically (sha-checked) in this file only — porting recipe (NGBOUND_PLAN.md):
the delta module for rows 76-80/83 must import this statement module and not re-declare the structure (Recipe A), or the reverse if the
delta lands first (Recipe B). Fidelity risks FR-NB-1..7 recorded in NGBOUND_PLAN.md §3 (max deg_a = degAZ, unbotD convention never
exercised since P ≠ 0; c↓ = downCount; the display's definitional half as a field; the rounding quantifier as in row 83; class
SmoothFront inherited from 83; the two closing sentences are commentary; axioms lp_lm + ng_finite_word). Final theorem after 83:
`SM.fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`.

## FINAL_REVIEW draft and delivery skeleton prepared; hyp:R row commissioned — 2026-09-14 ~15:05Z (pod executor)

work/FINAL_REVIEW_DRAFT.md (590 lines, on FINAL_REVIEW.md's checklist: per-row lines for the 160 accepted rows with audited axioms and the
one-clause disclosed reading, per-row reasons for the 32 pending rows, the GAP-2 paragraph relabelled, the R-obligation and
SM.corner_laws_and_soft clause tables, remaining gaps, process; nine [UPDATE] marks) and work/delivery/ (README, refresh.sh, pins,
declaration-map, reviews, receipts, progress, tools/gen_final_review_tables.py) written by a drafting agent; to be finalized after the
last rows. Inconsistencies it flagged, to fix at the end: STATUS.md header still says 28/132 (only the appended checkpoints are current);
the GAP-2 count is 22 claim rows (+ src:contact, hyp:R), not 21; RProof/X1Rows3.lean needs a "superseded by RProof/GenericTransport.lean"
header note (docstring-only, unaccepted library); FINAL_REVIEW.md's computation-certificates sentence does not apply (focused package,
certificates: []); the SM row hyp:R (fixed name SM.hyp_R, a Prop DEFINITION, `\status{hyp}`) is statable now — an architect is stating it on
the accepted vocabulary consistently with smR_shape_of_hyp_R and Bridge/B1-B4, for a definition-row statement review (as CV:ax:R was);
Bridge.theorem (CV.hyp_R → SM.hyp_R) stays undeclared (needs RProof.cv_R, GAP-2). src:contact stays undeclared (its only consumers,
fd:contact and CV:ax:etnyre, are GAP-2-blocked; the interface would be an unused axiom).

## hyp:R (SM Hypothesis R) STATED and mapped: work/lean/SM/HypR.lean; consumer check Bridge/SmR.lean — 2026-09-14 ~15:15Z (pod executor)

Architect unit work/drafts/hypr/HypR.lean (HYPR_PLAN.md): `SM.hyp_R : Prop := ∀ n [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k), g.TripleAt e f k → ∀ tp tm : g.SideParameter, cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property` — the all-sides form of the accepted prop:C-silent for the identical printed phrase; equivalent forms HypRDiagonal (one common parameter — the conclusion shape of the accepted smR_shape_of_hyp_R) and HypRBase proved equivalent via prop:C-chamber; `SM.sm_R_of_cv_R : CV.hyp_R → SM.hyp_R` PROVED from accepted rows (B4 pointwise), so Bridge:theorem becomes `Bridge.sm_R := SM.sm_R_of_cv_R RProof.cv_R` once R:cv_theorem lands (GAP-2). Ported as SM/HypR.lean (Parts 1-2; axioms of hyp_R = standard + lit_homfly through C) and Bridge/SmR.lean (Part 3, library; Bridge.sm_R NOT declared); built 15:12Z; mapped hyp:R → SM.hyp_R (implemented; the row is a definition, SKIP for claims.py, one of the 192 mapped rows); checker started (log work/checks/checker-run-1515.log); reviewer input = the module with its 8 sanity proofs stripped; brief work/port/review_prompt_hyp-R.md. Fidelity risks recorded BEFORE the port (verbatim from HYPR_PLAN.md §3):
* **FR-HR-1 (all-sides vs one representative vs chamber value).** Printed `C(P₊)=C(P₋)` is an equality of
  chamber values (def:germ's `F(P_±)`), well defined only through prop:C-chamber. Three renderings: all pairs of
  side points (`hyp_R`), one common parameter (`HypRDiagonal`), the base points (`HypRBase`). All three are
  PROVED equivalent in HypR.lean via the accepted `SM.prop_C_chamber` + `sidePolygon_mem_side`; the chosen
  form is the one used by the accepted prop:C-silent for the identical phrase and by CV:ax:R (R6; its review
* **FR-HR-2 (class of walls).** Only SIMPLE TRIPLE walls: def:walls (T) = `TripleAt`, which includes the three
  sign-change conditions ("the sign-change conditions exclude tangential germs", sm-1:776-777). Not
  `TripleCenterAt` alone (the centre kind without sign changes), not every germ with `Z_c` a single triple
  (lem:triple-sides' wider hypothesis), not CV's `IsSimpleRIII` (the CV class; B1-B3 prove SM-(T) ⊆ CV-RIII, the
  converse is not asserted, BRIDGE.md §4). The triple is unordered (`{{e,f,k}}`; `tripleAt_support_iff`), so no
* **FR-HR-3 (`hn : 3 ≤ n`, `[NeZero n]`).** Labelled presuppositions (C's binder; ZMod indexing), same as
  prop:C-silent and `CV.hyp_R`; vacuous restriction since `TripleAt` forces n ≥ 6.
* **FR-HR-4 (labelled vs quotient).** `cornerStateSum` is defined on labelled generic tuples; the printed sides
  are chambers of the cyclic quotient `𝓤_n/(ℤ/n)`. `g.sideTuple b t` is a labelled representative of a point of
  the side `g.side b ⊆ GenericPolygon n`; prop:C-chamber (stated on `GenericTuple` via `polygonProjection` /
  `chamber`) is exactly what identifies representatives' values with the chamber value. Same convention as every
  accepted C row.
* **FR-HR-5 (orientation of the sides).** `true` ↔ `P((0,ε))` = P₊, `false` ↔ `P((−ε,0))` = P₋ (def:germ
  sm-1:683-684; `sideTime`). The equation is symmetric, so a swap would not change the proposition.
* **FR-HR-6 (no shrinking clause).** The printed hypothesis has no "after shrinking the interval"; `hyp_R`
  asserts the equality for every side parameter inside the germ's radius — legitimate because each whole
  punctured side lies in one chamber (def:germ), i.e. no δ-form is needed (contrast `SignChanges`, which is a
  δ-form because the source says "there is δ>0").
* **FR-HR-7 (evaluation on generic sides).** C is only defined on generic polygons; the sides are generic by
  `generic_punctured` (`sideTuple`'s proof component). No value at the nongeneric centre enters. (The weak
  state sum def:C-weak is not involved.)
* **FR-HR-8 (hypothesis, not claim; no axiom).** `SM.hyp_R` must be a `def … : Prop`; the audit records kind
  "definition" (as for `CV.hyp_R`). Nobody may `axiom SM.hyp_R`; the policy mode is `explicit_parameter`.
  thm:comparison (row 132, pending; deps include `hyp:R`) and the final assembly consume it as an explicit
  argument or via `Bridge.sm_R`.


src:contact remains undeclared (consumers GAP-2-blocked).

## Sweep lane done: `represent` PROVED, row 76 ng:commutation closed in the merged skeleton — 2026-09-14 ~15:30Z (pod executor)

Eight units proved 52 of 54 sweep leaves (S1a 8, S1b 6 of 8, S2 5, S3S5 5, S4a 9, S4b 8, S6a 6, S6b 5); the two unproved leaves
dirBit_of_cont_before / dirBit_of_cont_after are FALSE as stated (Cont F q a does not exclude q itself being the cusp bounding the arc;
counterexample in W3S_S1b_REPORT.md), consumed by nothing, with corrected forms (extra hypothesis ¬ F.IsCusp q) proved as s1b_dirBit_of_cont_*;
PLAN §6's doubted entry-level limits were true and proved in full. Merger: work/drafts/frontrows/W3S_Merged.lean (23 404 lines, compiles,
6 sorries = the 4 L-geo leaves of wave 3a + the 2 false unused leaves; three verbatim relocations forced by Lean's no-forward-reference
rule, documented; W3S_MERGE_REPORT.md). `#print axioms`: represent, sweep_proof, recordIso standard; SM.ng_commutation (row 76) = standard +
SM.lp_lm — CLOSED; ng_local_front_bound (83) now has sorryAx only through certificate_laws ← the four L-geo leaves. Decision D-FR2: the two
false unused leaves are REMOVED at port time (as X2 was in the G11 lane) — a false internal statement never enters work/lean. Decision
D-FR3 (pipelining): row 76 is ported now as the delta module SM/FrontRowsW2S.lean (the sweep block + represent + NgCommutationClauses +
ng_commutation, importing SM.FrontRowsW2; extraction agent running), mapped and reviewed; rows 77-80 and 83 follow in a final delta
importing it once wave 3a's U6 (typeI/typeII/crossedCusp moves) lands. Total lane size so far ≈ 23.4k lines (D-F9 predicted 17-23k).

## hyp:R (SM.hyp_R) ACCEPTED (definition row) — 2026-09-14 ~15:45Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/hyp-R.json; non-blocking notes FR-HR-1/3/4 and inherited def:walls normalisations).
Accepted 15:45Z; checker restarted (log work/checks/checker-run-1545.log). Both hypotheses of the package are now stated (CV:ax:R and
hyp:R); Bridge:theorem = `SM.sm_R_of_cv_R RProof.cv_R` waits only on R:cv_theorem (GAP-2 through rows 174/176/177 and 175). src:contact
stays undeclared (consumers GAP-2-blocked).

## Row 76 ng:commutation ported (sweep delta module) and mapped — 2026-09-14 ~16:00Z (pod executor)

work/drafts/frontrows/FrontRows_W2S_Delta.lean (8 600 lines = the U8R sweep block minus the two false unused leaves + represent +
NgCommutationClauses + ng_commutation; imports SM.FrontRowsW2; W2S_DELTA_REPORT.md with the provenance and the final-delta recipe) ported
verbatim (header only) as work/lean/SM/FrontRowsW2S.lean; `lake build` OK 15:53Z (42 s); axioms of SM.ng_commutation = standard + SM.lp_lm,
of SM.FrontRows.represent = standard; clash scan 0. Mapped ng:commutation → SM.ng_commutation (implemented); checker started (log
work/checks/checker-run-1600.log). Reviewer input: the module with all 518 theorem proofs stripped (stripper extended once more: column-0
`by` / term continuations are not block ends) — compiles; brief work/port/review_prompt_ng-commutation.md (FR-8, FR-9, FR-10, FR-13,
FR-1/FR-16). Checker 15:48Z (run 1545) passed with 161 mapped (hyp:R accepted; receipt work/checks/dev-check-hypr-accepted.json).

## ng:commutation (row 76) ACCEPTED — 2026-09-14 ~16:25Z (pod executor)

Review 3/3 faithful, 2 refuters clean (work/reviews/ng-commutation.json; non-blocking notes = the disclosed readings FR-8/9/10/13/16 and
inert conventions). Accepted 16:25Z; checker restarted (log work/checks/checker-run-1625.log). Progress: claims verified 103/132, checklist
162/192. Remaining certificate rows: 77-80 (wave 3a U6 finishing the three front-move leaves; typeIII_site done), 83 (needs the four
leaves), then 93 (one-liner from 83).

## Certificate rows wave 3a: U5 done, U6 wrapped with 2 of 3 leaves; follow-up unit for typeII_move — 2026-09-14 ~16:55Z (pod executor)

U5 proved typeIII_site (13:27Z). U6, after ~4 h and an executor wrap-up request, delivered typeI_move and crossedCusp_move PROVED (standard
axioms) with an 11 100-line infrastructure block (generic slot-level RI/RII assembly, discs, the three-leaf machinery), and typeII_move
left open with two of its four IsTypeII variants fully proved (typeII_a, typeII_c), variant (b) at the word level, variant (d) and the
dispatch remaining (W3_U6_REPORT.md "What remains", precise). Decision D-FR4: rows whose leaves are proved (77 ng:front-I via typeI_move,
79 ng:front-III via typeIII_site, 80 ng:deletions via crossedCusp_move + the wave-2 zigzag leaf) are ported and reviewed as soon as the
wave-3a merger produces Skeleton_W3.lean, in a delta module SM/FrontRowsW3.lean importing SM/FrontRowsW2S.lean; row 78 (typeII) and row 83
(certificate_laws needs all four leaves) follow in a further delta once the follow-up unit (W3_U6b.lean, launched now on U6's file) closes
typeII_move; row 93 then is the one-liner of NgBound_Statement.lean.

## Reassessment rule adopted; stagnation audit for row 78 (typeII_move) — 2026-09-14 ~17:00Z (pod executor)

Mark's rule /workspace/repos/lean/reassessment_rule.md (audit after two substantive attempts or 60 minutes of active work without a newly
accepted source claim; helpers and compiles do not reset stagnation; a complete kernel-proved claim whose acceptance is merely delayed is an
acceptance bottleneck, not a mathematical stall) is adopted for the remaining work and applied per branch at every progress report.
Audit — certificate rows 77-80: kernel-proved leaves exist for typeIII_site (U5), typeI_move and crossedCusp_move (U6); the accepted
count has not moved since 16:25Z (row 76) because the leaves are still in unit copies — an ACCEPTANCE bottleneck; response: merge →
delta module → map → review for rows 77, 79, 80 as soon as Skeleton_W3.lean exists (in progress). Audit — row 78 ng:front-II (and 83, 93
behind it): claim = the front type-II move preserves B (sm-3:1972-1975), remaining claim-critical obligation = the leaf typeII_move (an
RII site between the two standard realizations with the record data) in its four IsTypeII variants: (a), (c) PROVED, (b) word level
proved / geometry open, (d) open, plus the dispatch; diagnosis = decomposition/effort, not mathematics (the same machinery proved (a), (c),
typeI and crossedCusp; (b)/(d) are mirrors); first substantive attempt = U6 (≈4 h, wrapped by executor request); second attempt =
the follow-up unit W3_U6b launched 16:55Z with the precise remaining obligation and the mirror templates. Decision: CONTINUE with ONE
bounded test — success = `typeII_move` proved and compiled in W3_U6b.lean (0 errors, standard axioms) by ~18:30Z; consequence on failure
= no third unit: rows 78, 83 (certificate_laws needs all four leaves), 93 are reported INCOMPLETE with the precise remaining obligation
(variants (b) geometry, (d), dispatch) and the proved partial (typeII_a, typeII_c) kept in the delta module as library material. Accepted
count unchanged by this audit (103/132).

## Rows 77 ng:front-I, 79 ng:front-III, 80 ng:deletions ported (wave-3 delta module) and mapped — 2026-09-14 ~17:15Z (pod executor)

work/drafts/frontrows/FrontRows_W3_Delta.lean (13 266 lines: the five row-statement structures, the U5 block + typeIII_site, the U6 block +
typeI_move + crossedCusp_move, the consumers P_typeI/P_typeIII/P_crossedCusp, rows 77/79/80; imports SM.FrontRowsW2S; typeII_move,
P_typeII, row 78, certificate_laws, word_bound, row 83 left for the last delta; W3_DELTA_REPORT.md with provenance and the last-delta
recipe — note: the U6 block declares nine global tactic macros, listed in the header, which the last delta must not re-declare) ported
verbatim (header only) as work/lean/SM/FrontRowsW3.lean; `lake build` OK 17:11Z (58 s); axioms of the three rows = standard + SM.lp_lm, of
the three leaves standard; clash scan 0. Mapped ng:front-I → SM.ng_front_I, ng:front-III → SM.ng_front_III, ng:deletions → SM.ng_deletions
(implemented); checker started (log work/checks/checker-run-1715.log). Reviewer input: the module with all 989 theorem proofs stripped
(compiles) — work/reviews/ng-front-moves-reviewer-input-statement.lean.txt; brief work/port/review_prompt_ng-front-moves.md (FR-1/5/6/8/13/15/16).
The wave-3a workflow's own merger never started (its U6 agent returned its JSON inline after the executor's wrap-up request); the delta
was extracted directly from the unit files — no Skeleton_W3.lean is needed.

## Row 78 audit outcome: typeII_move PROVED within the bound — 2026-09-14 ~17:30Z (pod executor)

The bounded test of the 17:00Z stagnation audit succeeded before its 18:30Z bound: the follow-up unit W3_U6b.lean proved `typeII_move`
(variant (b) by its own construction along the U6 design; variant (d) and the dispatch reused verbatim from the U6 unit, which — having
been resumed by the executor's status request — completed the same leaf on its own copy W3_U6.lean at 17:15Z; both files compile, standard
axioms; W3_U6_REPORT.md rewritten, W3_U6b_REPORT.md). Decision D-FR5: the last delta takes W3_U6.lean's version (one namespace); W3_U6b.lean
is the independent cross-check, not merged (duplication). An extraction agent builds FrontRows_W3b_Delta.lean (the type-II material, the
leaf, P_typeII, rows 78 and 83, certificate_laws, word_bound; imports SM.FrontRowsW3) and NgBound_Final.lean (row 93, recipe B). Accepted
count at this point: 103/132 (rows 77/79/80 under review).

## Rows 77 ng:front-I, 79 ng:front-III, 80 ng:deletions ACCEPTED — 2026-09-14 ~17:40Z (pod executor)

Reviews 3/3 faithful each (several with zero discrepancies), 2 refuters clean each (work/reviews/ng-front-I.json, ng-front-III.json,
ng-deletions.json; non-blocking notes = the disclosed readings FR-1/5/6/8/13/16 and inert guards/conventions). Accepted 17:40Z; checker
restarted (log work/checks/checker-run-1740.log). Progress: claims verified 106/132, checklist 165/192. Remaining certificate rows 78 and 83
(typeII_move PROVED; last delta extraction running) and 93 (NgBound_Final). The wave-3a workflow's merger also completed (Skeleton_W3.lean,
MERGE3_REPORT.md: rows 77-80 sorry-free there too) — used as a cross-check only.

## Rows 78 ng:front-II, 83 ng:local-front-bound, 93 fd:ng-bound ported and mapped — 2026-09-14 ~17:50Z (pod executor)

work/drafts/frontrows/FrontRows_W3b_Delta.lean (3 366 lines: the U6 type-II continuation from W3_U6.lean L22209-25423 verbatim, the leaf
typeII_move, P_typeII, rows 78 and 83, certificate_laws, word_bound; imports SM.FrontRowsW3; two new global tactic macros bII_pair /
dII_pair; W3B_DELTA_REPORT.md) ported verbatim (header only) as work/lean/SM/FrontRowsW3b.lean; work/drafts/frontrows/NgBound_Final.lean
(107 lines: NgBoundClauses, fd_ng_bound_of, `fd_ng_bound : NgBoundClauses := fd_ng_bound_of ng_local_front_bound`; imports SM.FrontRowsW3b;
recipe B of NGBOUND_PLAN.md — the structure NgLocalFrontBoundClauses lives in FrontRowsW3) as work/lean/SM/NgBound.lean. `lake build` OK
17:46Z; axioms: ng_front_II standard + lp_lm; ng_local_front_bound and fd_ng_bound standard + lp_lm + ng_finite_word (as the \status lines
predict); typeII_move standard; clash scans 0. Mapped ng:front-II → SM.ng_front_II, ng:local-front-bound → SM.ng_local_front_bound,
fd:ng-bound → SM.fd_ng_bound (implemented); checker started (log work/checks/checker-run-1750.log). Reviewer inputs: both modules with all
theorem proofs stripped (compile); combined brief work/port/review_prompt_ng-front-ii-local-bound-ng-bound.md. The certificate rows lane
(76-83) is now fully proved: total ≈ 39.9k lines across SM/FrontRowsW2 (14 665), W2S (8 600), W3 (13 266), W3b (3 366) [+ SM/NgBound 108]
— D-F9 predicted 17-23k (correction 18:20Z: the earlier sum "26.8k" was an arithmetic slip). Checker 17:44Z (run 1740) passed with 165 mapped (rows 77/79/80 accepted; receipt dev-check-frontrowsw3-accepted.json).

## Library docstring hygiene before the final run — 2026-09-14 ~18:00Z (pod executor)

Comment-only edits (no declaration changed) to two unaccepted library modules flagged by the FINAL_REVIEW drafter: RProof/X1Rows3.lean header
now records that it is superseded as the row module by RProof/GenericTransport.lean (accepted row 173) and remains its imported library;
SM/LinkingCalculus.lean's remaining "not formalised here" sentence now points to SM/RegularPoleCount.lean and SM/LinkingCalculusRow.lean.
Dependents rebuilt (statement hashes unchanged; the accepted rows are unaffected); checker restarted (log work/checks/checker-run-1800.log).
STATUS.md's stale 2026-09-13 header replaced by a current-state header (the old one kept below as historical). Checker 17:53Z (run 1750)
passed with 168 mapped (rows 78/83/93 audited; receipt dev-check-frontrowsw3b-implemented.json).

## Rows 78 ng:front-II, 83 ng:local-front-bound, 93 fd:ng-bound ACCEPTED — the certificate rows lane is complete — 2026-09-14 ~18:05Z (pod executor)

Reviews 3/3 faithful each (row 83 with two zero-discrepancy reviews), 2 refuters clean each (work/reviews/ng-front-II.json,
ng-local-front-bound.json, fd-ng-bound.json; notes = the disclosed readings FR-1/5/8/13/14/16 and FR-NB-1..7). Accepted 18:05Z; checker
restarted (log work/checks/checker-run-1805.log). All eight certificate rows 76-83 and their consumer 93 are accepted; the front block
(rows 73-94 minus the GAP-2 rows 91 and 94) is complete. Progress: claims verified 109/132 (the reachable ceiling without GAP-2 recorded at
12:20Z), checklist 168/192. Remaining: 22 claim rows GAP-2-blocked (+ src:contact, unused), row 57 deferred. Next: the stage check
`python3 tools/check_lean.py work/lean --all` (expected to stop at the first unaccepted row — reported as incomplete), FINAL_REVIEW.md
finalization from work/FINAL_REVIEW_DRAFT.md, the delivery refresh, the final checkpoint and the Discord report.

## Stage check run; closing sequence — 2026-09-14 ~18:10Z (pod executor)

`python3 tools/check_lean.py work/lean --all` (18:06Z, log work/checks/stage-all-attempt-1806.log) FAILED as expected: "stage is incomplete;
unaccepted rows: Bridge:theorem, CV:ax:etnyre, CV:ax:slbound, CV:singleton_D_i, CV:thm:carrierfloor, R:cv_theorem, R:extreme_pair_zero,
R:extreme_selected, R:extreme_transport, R:generic_selected, SM:corner_laws_and_soft, cb:singleton, cf:thm-carrierfloor, cor:C-inherits,
cp:finite-contact-path, fd:contact, lem:corner-values, lem:gauss-two-discs, prop:anchor-values, src:contact, thm:C-S7, thm:C-soft,
thm:comparison, thm:floor" — the focused stage is INCOMPLETE and is reported as such (work/checks/stage-1.json records passed=false). The
development receipt work/checks/dev-check-frontrowsw3b-accepted.json (18:05Z run: passed, 168 mapped, 36 079 audited) binds the accepted
state. work/delivery/ refreshed (926 files, MANIFEST.sha256); FINAL_REVIEW_DRAFT tables regenerated (accepted 168, pending 24). A documentation
agent finalizes FINAL_REVIEW.md (root, completed review appended below the checklist) and the delivery README; then the final development
checker run (the root FINAL_REVIEW.md is in the checker's bundle), the last delivery refresh, the final tarball and the Discord report.
