You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE definition row against ONE printed source definition (frame SM15).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/ng-front-domain-source-excerpt-lines-1825-1841.tex.txt (= reference/SM/
   sm-3-statesum.tex 1825-1841, ng:front-domain "Finite oriented fronts"). Context, ONLY to fix notation:
   reference/SM/sm-3-statesum.tex 1806-1824 (the text introducing fronts), 1843-1875 (ng:smoothing-record and the first
   uses of S(F), D(F), w(F), s(F)), 3210-3230 (the exact semicubical germ of cp:finite-contact-path — only to see what
   "ordinary semicubical cusp" and "semicubical parameter u" denote), 325-351 (def:positive-lift: "a diagram here is a
   finite polygonal immersion, or a regular smooth immersion …" — the polygonal reading of every diagram), 352-370
   (def:gauss-record: the named record). You MAY read the executor's recorded fidelity risks FR-1..FR-7 in
   work/AUTHOR_NOTES.md (entry "Front block: representation adopted" of 2026-09-14) — in particular FR-1 (S(F) read
   polygonally through a named-record Marking on a Diagram), FR-2 (cusp criterion in derivative form), FR-3 (smooth =
   C^∞; a parameter circle = a 1-periodic map of ℝ), FR-4 (parametrized rounding).
2. The Lean statement with the row proof replaced by `sorry`: work/reviews/ng-front-domain-reviewer-input-statement.lean.txt
   (module SM/FrontSmooth.lean). The definitions ARE under review as part of the row: SmoothLoop, Param / SameParam,
   SmoothFront (one structure field per printed clause), eval/vel/acc/jerk, IsCusp, cuspDisc, IsDownCusp/IsUpCusp/
   IsLeftCusp/IsRightCusp, slope, IsDouble, IsOverUnder, crossSign, cuspSet, doubleSet, crossingPairs, downCount,
   upCount, writhe, sCount, CuspFree, occSet/Occ/Marking, Cusp/GeomRounding, Rounding, IsRounding; the bundle
   FrontDomainDefinitionData (20 fields) and theorem SM.front_domain_definition at the end. Helper lemmas' proofs are
   not under review; germFront / dOf / defect are library material for later rows (not clauses of this row). Do NOT
   open work/lean/SM/FrontSmooth.lean. ROUND 2: the round-1 review found the rounding notions provably EMPTY (open-interval
   `clean`; the rounded curve typed as a SmoothFront). They were repaired: GeomRounding now stores the arc endpoints
   a c < cusp < b c (b − a < 1), uses the CLOSED interval in `clean`, adds `arc_in` (F's closed arc lies in the disc) and
   `arc_simple` (F meets the disc in that single embedded arc — stated on the CLOSED arc, the executor's deliberate choice),
   keeps inside / regular / simple / no_crossing / agree on the OPEN arc, and targets plain C^∞ loops G : Fin c → SmoothLoop;
   Rounding S = ⟨G, geom, marking : F.Marking S⟩ — the record of S(F) is F's own named record, justified by the module's
   lemmas (the rounded curves agree with F, with velocities, at every double point and create none: isDouble_iff,
   deriv_eq_of_isDouble, regular_everywhere, transverse, no_triple — statements only, proofs not under review). Judge in
   particular (i) whether the repaired rounding is exactly the printed clean-disc replacement, neither stronger nor weaker,
   and NOT provably empty (the module's non-vacuity comment; SmoothFront.not_cuspFree documents why the old typing failed),
   (ii) whether reading the record of S(F) as F.Marking is faithful to "the resulting ordinary diagram is denoted S(F)"
   given FR-1, (iii) the new fields rounding_no_crossing and rounding_ordinary against "no crossing" / "ordinary diagram".
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/LinkDiagram.lean (Diagram,
   componentCount, compOf, sign, overBit/isOver, twin), LinkDiagramRecord.lean (Diagram.record, visitCoord, cycBetween,
   twin), LinkRecord.lean (Record, RecordIso), LinkMoves.lean (IsDisc, Clean — the clean-disc vocabulary),
   TurningNumber.lean (ClosedC1Curve — a related accepted smooth model, for comparison), EuclideanPlane.lean (det).

YOUR TASK: decide whether the definitions + bundle pin down exactly the printed definition. Clause by clause:
(a) "A front F is an actual map of a nonempty finite union of parameter circles to the oriented (x,z) plane" (SmoothFront:
c ≥ 1 components, each a SmoothLoop = C^∞ 1-periodic map ℝ → Plane — is C^∞ the printed "actual map … smooth"?
is a 1-periodic map the printed parameter circle? is the plane's orientation used (det convention)?); (b) "with finitely
many transverse double points" (doubleSet finite; IsDouble; transversality det(vel p, vel q) ≠ 0); (c) "and ordinary
semicubical cusps" (IsCusp: vel = 0 with det(acc, jerk) ≠ 0 — FR-2: is the derivative-form criterion exactly "ordinary
semicubical cusp"?); (d) "no other singularities" (every non-immersive parameter is a cusp; no triple point); (e) "no
vertical tangencies on regular arcs" (vel ≠ 0 → (vel).1 ≠ 0); (f) "The limiting tangent at every cusp is also
nonvertical: in a semicubical parameter u with cusp at u = 0, require x''(0) ≠ 0" ((acc p).1 ≠ 0 at cusps — is the
Lean's arc-length/parameter the printed semicubical parameter, or is the condition parametrization-invariant?);
(g) "Cusps meet no other strand or singularity" (cusp_alone); (h) "At a crossing the branch with smaller dz/dx is over"
(slope, IsOverUnder, the Xor); (i) "A downward cusp is traversed from its locally upper arm to its locally lower arm"
(IsDownCusp := IsCusp ∧ x''·det(acc, jerk) < 0 — FR-2: the docstring justifies this sign rule; judge whether the
rendering is faithful or an unproved identification; is the left/right cusp typing printed here or an addition?);
(j) "Write D(F) for the number of downward cusps, w(F) for the sum of the over-first tangent-determinant crossing
signs, and s(F) for the number of crossings plus cusps" (downCount, writhe with crossSign = sign det(vel over, vel
under) summed over crossingPairs (each double point once, over-first), sCount); (k) "In disjoint clean cusp discs
replace each cusp by a simple regular arc with the same oriented attachments and no crossing. The resulting ordinary
diagram is denoted S(F)" (GeomRounding: disjoint discs U c containing the cusp point, the replaced arc inside, regular,
simple (InjOn), no crossing with anything else, agreement outside the intervals I c; IsRounding S := ∃ cusp-free G
with a GeomRounding and a Marking of S — S a polygonal Diagram carrying G's named record (FR-1): is that the printed
"resulting ordinary diagram", is the Marking exactly the named record (components, cyclic order of occurrences,
pairing, over bits, signs)?). Also: every Lean field must have a printed counterpart — flag any that does not (e.g.
the left/right cusp clause, the SameParam machinery) as a discrepancy, labelled non-blocking if it is a harmless
definitional unpacking. Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; default to "not
faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
