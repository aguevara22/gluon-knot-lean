You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE row against ONE printed source statement (frame SM15):
cb:embedded-rotation (row 104), Lean declaration `SM.cb_embedded_rotation` (module SM/EmbeddedRotation.lean; bundle
`SM.EmbeddedRotationData P` with fields pm_one, orientation, exists_supporting; hypotheses `3 ≤ n`, `Regular P`, `Embedded P`).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cb-embedded-rotation-source-excerpt-lines-4760-4765.tex.txt (= reference/SM/sm-3-statesum.tex
   4760-4765, Lemma cb:embedded-rotation "Exterior-angle count for an embedded polygon": "Every embedded regular polygon has rotation +1
   or −1, according to its traversal orientation around the bounded complementary region."). Context, ONLY to fix notation and to see which
   objects the statement names: sm-3:4766-4800 (its printed proof — a triangulation / Euler-count argument citing lem:gauss-two-discs; the
   Lean proof is DIFFERENT (a polygonal turning-number argument) and is not under review; note 4791 "including zero at a straight
   subdivision" — flat vertices are in the domain), 428-436 (lem:gauss-two-discs, DEFERRED/unproved in this project — the Lean statement
   of row 104 must not depend on it), 4801-4830 (lem:corner-values, the consumer: it uses only |rotation| = 1), reference/SM/sm-1-polygons.tex
   (def:polygon, def:regular, lem:rot = the rotation number via principal turns — find the definitions of polygon, edge, regular, principal
   turn, rotation number).
2. The Lean statement: work/reviews/cb-embedded-rotation-reviewer-input-statement.lean.txt — the module SM/EmbeddedRotation.lean with EVERY
   theorem proof replaced by `sorry`; definitions in full. The STATEMENT PART is lines 25-60 (Embedded, IsSupportingVertex,
   EmbeddedRotationData) and the theorem `cb_embedded_rotation` near line 476; everything else (secant region, retraction, lift,
   boundary decomposition — the proof's construction) is shown only because definitions are not withheld. It compiles. Do NOT open
   work/lean/SM/EmbeddedRotation.lean or anything under work/drafts/pldiscs/.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/Polygon.lean (LabelledTuple, edge, edgeSegment,
   remote, adjacent, traversal, shift, reversal), SM/EuclideanPlane.lean (det, planeDot, normalize), SM/RegularLocus.lean (Regular,
   principalTurn), SM/RotationNumber.lean and SM/RotationTheorem.lean (rotationNumber; the accepted lem:rot SM.rotation_number: its clauses
   incl. rotationNumber (reversal P) = −rotationNumber P), SM/TurnLift.lean (IsLiftOn, principalAngle, RegularPair), SM/Crossings.lean
   (Crossing), SM/Generic.lean (Generic), SM/LinkDiagram.lean (Shadow, IsCrossingFreeCircle — the consumer chain's crossing-free notions),
   and Mathlib.

DISCLOSED FIDELITY RISKS recorded by the executor BEFORE the row was stated (work/AUTHOR_NOTES.md entry "Rows 57 / 104 probe" of 2026-09-14
— you MAY read it, and work/drafts/pldiscs/PLDISCS_FEASIBILITY.md §1.1, §1.6, §1.8 ONLY):
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


YOUR TASK: decide whether the hypotheses + bundle render exactly the printed lemma: "embedded" (Embedded P: nonzero edges, remote edge
segments disjoint, consecutive segments meet exactly in the shared vertex — is this the simple closed polygonal curve; are flat vertices
correctly allowed; is anything missing, e.g. is n ≥ 3 printed or implicit?); "regular polygon" (Regular P — the accepted def:regular;
FR-ER-3 says Embedded implies it, kept as printed); "has rotation +1 or −1" (pm_one with the accepted rotationNumber); "according to its
traversal orientation around the bounded complementary region" (the field orientation: at every SUPPORTING vertex — the polygon in the
closed half-plane beyond the vertex — a left turn forces +1 and a right turn forces −1; and exists_supporting: such a vertex with nonzero
turn exists. Judge FR-ER-2 explicitly: "bounded complementary region" is not an object of the accepted layer (it is row 57's Jordan
content); is the supporting-vertex reading a faithful rendering of the printed sign clause — at a supporting vertex the bounded region
lies on the polygon's side, so "traversal orientation around the bounded region" = the sign of the turn there — or a blocking change? note
the consumer uses only |rotation| = 1). Hypotheses added or dropped; every field a printed clause or a disclosed extra. Also confirm the
theorem's statement does not mention or depend on lem:gauss-two-discs (D-ER1). Expand definitions to primitives; say where the Lean is
STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
