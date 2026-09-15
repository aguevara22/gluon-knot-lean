You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the definition you are reviewing. Your job is a statement-fidelity review of ONE hypothesis row —
a Prop DEFINITION, not a claim — against its printed source statement (frame SM15):
hyp:R (SM's Hypothesis R), Lean declaration `SM.hyp_R : Prop` (module SM/HypR.lean; checker-fixed name; policy mode
explicit_parameter — it must be a `def … : Prop`, never an axiom).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: work/reviews/hyp-R-source-excerpt-lines-1149-1151.tex.txt (= reference/SM/sm-4-knotlaws.tex 1149-1151,
   Hypothesis R: "At every simple triple wall, C(P₊) = C(P₋)."). Context, ONLY to fix notation: reference/SM/sm-1-polygons.tex 680-700
   (def:germ: a wall germ, its two sides P((−ε,0)) and P((0,ε)) as chambers, F(P_±)), 737-777 (def:walls: the wall types, in particular
   (T) "Simple triple at {e,f,g}" 762-766 with its sign-change conditions; "the sign-change conditions exclude tangential germs"),
   697-703 (lem:triple-sides statement), reference/SM/sm-3-statesum.tex 1688-1700 (def:C, the corner state sum), reference/SM/sm-4-knotlaws.tex
   36-40 (prop:C-chamber — makes C(P±) well defined on chambers), 101-105 (prop:C-silent — the accepted precedent for the identical phrase
   "C(P₊) = C(P₋)" and its side convention), 1153-1170 (lem:triple-types, how the triple wall is used), reference/BRIDGE/BRIDGE.md
   1446-1480 (how Hypothesis R is consumed by the bridge), and reference/R/CV/d10_axioms.tex 18-33 (CV's Hypothesis R, ax:R — the accepted
   CV twin CV.hyp_R, for comparison of the two forms).
2. The Lean definition: work/reviews/hyp-R-reviewer-input-statement.lean.txt (module SM/HypR.lean with the proofs of its sanity lemmas
   replaced by `sorry`; the row is the DEFINITION `hyp_R` near line 83 — under review; the equivalent forms HypRDiagonal (one common side
   parameter) and HypRBase (the base points) and the lemmas hyp_R_iff / hyp_R_iff_hasWallKind / hyp_R_iff_diagonal / hyp_R_iff_base are
   evidence (their proofs withheld); the module docstring maps notation — verify it, do not trust it). Do NOT open work/lean/SM/HypR.lean
   or work/lean/Bridge/SmR.lean or anything under work/drafts/hypr/.
3. Lean definition modules (definitions and docstrings; proofs not under review; accepted rows def:germ, def:walls, def:C, prop:C-chamber,
   prop:C-silent): work/lean/SM/WallGerm.lean (WallGerm, Parameter, SideParameter, sideTime, sideTuple, center, side), GermDefinition.lean,
   GermSignChange.lean (SignChanges), NamedWallPredicates.lean (TripleAt — read it and compare clause by clause with def:walls (T);
   tripleAt_support_iff), WallCenterKinds.lean (TripleCenterAt, HasWallKind — the centre kinds), GermSides.lean (sidePolygon_mem_side: each
   side lies in one chamber), CornerStateSum.lean (cornerStateSum = def:C), CChamber.lean (the accepted prop:C-chamber bundle — statement
   only), CSilent.lean (the accepted prop:C-silent bundle CSilentData — statement only, the side convention precedent), RProof/X1Rows.lean
   (the accepted `CV.hyp_R` definition and the theorem statement smR_shape_of_hyp_R — statements only), Bridge/B4.lean header (what B4
   provides).

DISCLOSED READINGS recorded by the executor BEFORE the row was stated (work/AUTHOR_NOTES.md entry "hyp:R" of 2026-09-14 and
work/drafts/hypr/HYPR_PLAN.md §3-§4 — you MAY read them): FR-HR-1 (all-sides form: C(P₊) = C(P₋) rendered as the equality of
cornerStateSum on EVERY pair of side parameters tp, tm — the accepted prop:C-silent convention for the identical phrase; the one-parameter
(diagonal) and base-point forms are proved equivalent via prop:C-chamber); FR-HR-2 (class of walls: only def:walls (T) = TripleAt including
the three sign-change conditions; not the centre kind alone, not lem:triple-sides' wider germs, not CV's IsSimpleRIII — SM's (T) ⊆ CV's
RIII by B1-B3, the converse not asserted; the triple unordered); FR-HR-3 (hn : 3 ≤ n and [NeZero n] presuppositions, vacuous since
TripleAt forces n ≥ 6); FR-HR-4 (labelled representatives, identified with chamber values by prop:C-chamber); FR-HR-5 (true ↔ P₊ =
P((0,ε)), false ↔ P₋ = P((−ε,0)); the equation is symmetric); FR-HR-6 (no shrinking clause: each punctured side lies in one chamber);
FR-HR-7 (C evaluated on generic sides only); FR-HR-8 (a def : Prop, never an axiom; consumed as an explicit parameter or via
Bridge.sm_R).

YOUR TASK: decide whether `SM.hyp_R` pins down exactly the printed hypothesis: (a) "at every simple triple wall" — `∀ n [NeZero n] (hn : 3 ≤ n)
(g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k → …`: expand TripleAt and compare with def:walls (T) clause by clause (the support
{e,f,k}, Z_pt, Z_c, the sign changes; does "simple" add anything beyond the type clauses?); is the wall germ class def:germ's?; (b) "C(P₊) =
C(P₋)" — `∀ tp tm : g.SideParameter, cornerStateSum hn (g.sideTuple true tp).property = cornerStateSum hn (g.sideTuple false tm).property`:
are sideTuple true/false the two sides of def:germ, is quantifying over all side parameters the printed statement about the two side
chambers (exact via prop:C-chamber, or presupposing something not accepted?), is the naming of ± immaterial; (c) compare with the accepted
CV.hyp_R (form R6) and say whether the SM form is the same kind of rendering; (d) confirm the declaration is a definition (kind def, Prop)
and not an axiom or a theorem. Expand definitions to primitives; say where the Lean is STRONGER or WEAKER than the printed hypothesis
(FR-HR-1: label the all-sides form non-blocking or reject it, with reasons); label non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
