You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE CONDITIONAL row against ONE printed source statement (frame SM15):
cp:finite-contact-path (row 91), Lean declaration `SM.cp_finite_contact_path_of_descent : SM.AmbientIsotopyDescent → SM.ContactPathData`.
This row is NOT claimed as proved: the project records that the printed proof's sentence "the retained global source premise yields
H_{D_ε} = H_{D_T}" (sm-3:3313-3316) needs Reidemeister's theorem for spatial isotopies, which is outside the formal scope (GAP-2). The
theorem under review proves the row FROM the named clause `AmbientIsotopyDescent`. You review TWO things: (A) is `ContactPathData` exactly
the printed lemma, and (B) is `AmbientIsotopyDescent` exactly the missing sentence — no stronger than what the printed proof invokes, and
not something derivable from the frozen literature interface `SM.lit_homfly`?

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/cp-finite-contact-path-source-excerpt-lines-3210-3233.tex.txt (= reference/SM/sm-3-statesum.tex
   3210-3233, Lemma cp:finite-contact-path "The supplied contact-path diagram endpoints": hypotheses on C, L, F, the exact cusp germs
   cp:exact-cusp, the multiple points, the supplied family G_t from L to T with D_T an ordinary finite regular generic diagram; conclusion
   P_{S(F)} = P_{D_T} for every clean ordinary cusp smoothing S(F) with smaller y over at the unchanged crossings; the disclaimer 3231).
   Context, ONLY to fix notation and to see which objects the proof uses: sm-3:3234-3327 (its proof — read it: the rounding family, D_ε,
   the flattened family H_s 3254-3264, the isotopy-extension analysis 3264-3313, the descent sentence 3313-3316, the closing paragraph),
   3029-3058 (ce:rounding, accepted), 3170-3209 (ce:smoothing-record, accepted), 341-343 (def:transverse-front), 905-935 (lit:homfly's
   registry text: "Its value depends only on the oriented link presented by D") and blueprint/AXIOM_REGISTRY.md section lit:homfly.
2. The Lean statement: work/reviews/cp-finite-contact-path-reviewer-input-statement.lean.txt — the statements module (ContactPathData with
   one field per printed clause; AmbientIsotopyDescent; the alternative forms AmbientIsotopyLinkEquiv with its proved implication
   `.descent`, AmbientIsotopy, AmbientIsotopyDescentLit, IsotopyExtension, `ambientIsotopyDescent_of_lit`) followed by the theorem with
   its proof withheld. It compiles. Do NOT open work/drafts/gap2/CPRow91_Skeleton.lean or CPRow91_PLAN.md.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/CeSmoothingRecord.lean (row 90: SpatialLink,
   CuspedProjection, RegularGenericProjection, HeightMarking, CleanCuspSmoothing, SpatialFamily, CuspRoundingFamily, CeSmoothingRecordData),
   work/lean/SM/CeRounding.lean lines 1-200 (row 89 statement part), SM/TransverseFront.lean, SM/FrontSmooth.lean, SM/FrontRecordBridge.lean,
   SM/LinkInterfaces.lean (HomflyClauses with its field `descent`, the axiom lit_homfly, homfly), SM/LinkMoves.lean (LinkEquiv, RI/RII/RIII,
   PlanarIsotopic — definitions), SM/LinkDiagram.lean (Diagram), SM/LocalPolynomial.lean (P), SM/PolynomialBlock.lean (P_eq_homfly —
   statement), and Mathlib.

DISCLOSED READINGS (you MAY read work/AUTHOR_NOTES.md entries of 2026-09-14 on GAP-2 (D-F10..D-F13), on rows 89/90 (D-1, CE-R1..CE-R13, K-1..K-8)
and "Row 91 cp:finite-contact-path PROVED MODULO the descent clause" which lists FR-CP-1..FR-CP-10 and decision D-CP-1): FR-CP-1 smooth
diagrams are read through HeightMarking to polygonal Diagrams, quantified over readings, no carrier existence asserted; FR-CP-2 P_{D_ε}
realised on a constructed reading; FR-CP-3 η = Real.smoothTransition (strict increase not asserted); FR-CP-4 the family is on all of ℝ,
constant outside [0,1]; FR-CP-5 "a supplied jointly smooth family G_t" is a SpatialFamily on ℝ — a hypothesis on the whole line, a
narrowing of the printed [0,1] family (judge whether it is faithful given every family on [0,1] extends, or a blocking narrowing);
FR-CP-6 D_T read with T's own heights; FR-CP-7 isotopy extension absorbed into the clause; FR-CP-8 the gap itself; FR-CP-9 0 < c unused,
orientation = parameter direction, fields 1-5 are read-backs of the hypotheses; FR-CP-10 the disclaimers are commentary.

YOUR TASK: (A) compare the printed hypotheses (C finite nonempty union of oriented circles; L a smooth embedding with nonvanishing
derivative; F regular except at finitely many cusps each with the exact germ; only finitely many transverse double points, none at a
cusp, distinct y values; the supplied family G_t from L to T; D_T ordinary finite regular generic) and the conclusion ("every clean
ordinary cusp smoothing S(F), with smaller y over at the unchanged crossings, has P_{S(F)} = P_{D_T}") with ContactPathData, expanding
every definition to primitives through the accepted row-89/90 vocabulary; is "clean ordinary cusp smoothing" the accepted CleanCuspSmoothing
(with collar, D-1)? is "with smaller y over at the unchanged crossings" rendered? is P_{D_T} read faithfully (FR-CP-6)? (B) judge
AmbientIsotopyDescent: does it say exactly "two spatial links joined by a jointly smooth family of oriented spatial embeddings whose end
projections are ordinary regular generic diagrams have polygonal readings with equal HOMFLY–PT values" — the printed premise "depends
only on the oriented link" applied along the isotopy; is it STRONGER than what the proof needs (e.g. does it quantify over more families
or readings than the proof uses), could it be derived from lit_homfly's `descent` over LinkEquiv without Reidemeister's theorem (say
precisely why not), and is it a true statement of mathematics (so the conditional theorem asserts nothing false)? Say where the Lean is
STRONGER or WEAKER; label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
