You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/def-gauss-record-source-excerpt-lines-352-370.tex.txt
   (= reference/SM/sm-3-statesum.tex 352-370, def:gauss-record). Context, read ONLY to fix notation:
   reference/SM/sm-3-statesum.tex 325-351 (def:positive-lift and the bridge paragraph: diagrams here
   are finite polygonal immersions; "The named record defined next (crossing occurrences, successor,
   pairing, over/under bits and signs) is what this section … call[s] the crossing record of a
   diagram"), 371-427 (lem:gauss-pl-model, the finite PL models — read only to see what the
   extension clause is used for), reference/SM/sm-1-polygons.tex 138-160 (def:crossings), 240-268
   (def:gauss: the Gauss word, visits and their cyclic order on the traversal circle).
2. The Lean statement with the proof replaced by `sorry`:
   work/reviews/def-gauss-record-reviewer-input-statement.lean.txt (bundle
   GaussRecordDefinitionData, main declaration SM.gauss_record_definition). Its module docstring maps
   notation — verify it, do not trust it.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; helper proofs are not
   under review): LinkDiagram (namespace SM.Link: Shadow, Strand, Crossing, Visit, Pt, eval, dir,
   Diagram, overStrand, underStrand, IsPositive, sign, isOver, overVisit, underVisit — definitions
   only), LinkRecord (Record with its fields and axioms, RecordIso — definitions only), LinkDiagramRecord
   (compOf, visitPt, visitCoord, cycBetween, nextVisit, visitSucc, twin, pairPerm, overBit,
   Diagram.record, VisitBetween, RecordIso.ExtendsToCircleMaps — definitions and docstrings only),
   LinkRecordExtension (RecordIso.ExtendsPiecewiseAffine, rexPL_arcLen; and LinkDiagram's
   Diagram.cyclicOffset — definitions and docstrings only; the
   statements of record_succ_no_between, nextVisit_comm_iff_visitBetween_iff,
   RecordIso.visitBetween_iff and record_of_single_polygon may be read as statements), Traversal
   (TraversalPoint, traversalKey, traversalBetween, traversalEvaluation; accepted), GaussVisits
   (Visit, visitPosition; accepted row def:gauss), Crossings (accepted row def:crossings), Polygon
   (LabelledTuple, edge), EuclideanPlane (det). Do NOT open work/lean/SM/GaussRecordDefinition.lean (it contains the row proof); in
   LinkRecordExtension read definitions and docstrings only.

YOUR TASK: decide whether the bundle pins down exactly the printed definition, read on the records
of oriented link diagrams (the source states it for one oriented circle; the Lean states it for
every component circle of a diagram — say whether that generalisation is faithful, in particular
for one-component diagrams). Check: (a) "Let γ : C → S² be an actual generic immersion of an
oriented circle in an oriented sphere, with over/under choices at its transverse double points":
the Lean diagram (polygonal, generic, with over strands) and its parametrizing circles (traversal
points with the traversalKey coordinate) — is the sphere versus plane difference immaterial here?
(b) "Its finite crossing-occurrence set M has forward successor s" (fields occurrences, successor:
occurrences = visits; successor = the next occurrence on the same circle with no occurrence of that
circle strictly between — is this the forward successor along the oriented circle?), "pairing
involution τ without fixed points" (field pairing: the other occurrence of the same crossing),
"an over/under bit at each occurrence" (field bits), "crossing signs σ(c) = sgn det(u_{c,O},
u_{c,U})" (field signs: the directions of the over and under strands; stored on both occurrences;
nonzero by transversality — check the argument order O, U). (c) "A named record isomorphism is a
bijection Φ : M → M' preserving successor, pairing, over/under bits and these signs" (field iso —
the Lean RecordIso also carries a bijection e of the circles respected by Φ: is that implied by
successor preservation for one circle / a faithful extra for many circles?). (d) "The parametrizing
circles are oriented; the finite bijection must preserve their cyclic orders. It does not prescribe
a map at every unmarked parameter and does not permit traversal reversal." (field cyclic_order: a
RecordIso preserves VisitBetween on each circle; the absence of a map at unmarked parameters is
structural; is "does not permit traversal reversal" rendered by cyclic-order preservation?). (e)
"After a finite subdivision we choose an orientation-preserving piecewise-linear circle map Φ̄ : C →
C' extending Φ: on each interval between successive marked points use the positive affine map in
oriented interval coordinates. If M is empty, choose any positive circle parametrization." (field
extension: `ι.ExtendsPiecewiseAffine`, module SM/LinkRecordExtension.lean — definitions
`RecordIso.ExtendsPiecewiseAffine`, `rexPL_arcLen`, `Diagram.cyclicOffset` may be read: existence of
orientation-preserving bijections of the parametrizing circles carrying each occurrence to its image,
with the forward distance from an occurrence scaled by the ratio of the arc lengths on each arc from
an occurrence to its successor — the positive affine map in oriented interval coordinates — and the
linear rescaling k'/k on an occurrence-free circle; judge whether this clause of the printed
definition is a construction ("we choose") whose content is the existence of such a map, whether the
rendering matches "piecewise-linear … positive affine … any positive circle parametrization" (the
Lean fixes ONE positive parametrization, the linear rescaling — is that faithful to "any"?), and
whether the single-mark case (the arc from an occurrence to itself is the whole circle) is right.) Expand
definitions to primitives; say where the Lean is STRONGER or WEAKER; any printed notion without a
Lean counterpart, or any Lean clause without a printed counterpart, is a discrepancy. Default to
"not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
