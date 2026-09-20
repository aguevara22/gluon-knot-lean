You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did not write the
declaration you are reviewing. Your job is a statement-fidelity review of ONE literature interface — the `axiom`
`SM.src_contact` (the fifth and last admitted literature input, fixed policy name; lean/axiom-policy.json) — against
its printed registry text.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

BACKGROUND: the package admits five literature inputs as axioms whose statements must be transcribed from
blueprint/AXIOM_REGISTRY.md. The adopted pattern (accepted axioms lit_homfly, lp_lm, ng_finite_word): a Prop structure
whose fields are the printed clauses, in ∃-form over the literature's objects where the document itself does not define
them, the objects then fixed by Classical.choose. Here the literature's quantities r (rotation number) and tb
(Thurston–Bennequin) are never defined by the document, so the axiom is `∃ r tb : (ℝ → E3) → ℝ, SrcContactClauses r tb`;
the self-linking number IS defined by the document (fd:framed-linking, sm-3:2820-2824, the Gauss integral of a
transverse knot and its ∂_y-pushoff, accepted as `SM.selfLinking` with row 88 `SM.fd_linking_calculus`) and is made
radius-free as `SM.slCircle` / `SM.sl`; the identification with the literature's sl is the document's own
rem:sl-convention (sm-3:3012-3022). Every convention / provenance / scope sentence of the registry text is a theorem or
commentary, not a field (precedent ng:finite-word).

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed registry text, verbatim: work/reviews/src-contact-registry-excerpt.md.txt (= blueprint/AXIOM_REGISTRY.md
   section src:contact, quoting reference/SM/sm-3-statesum.tex 3341-3365); context ONLY to fix notation and conventions:
   sm-3:2786-2825 (fd:linking-calculus: the Gauss pairing, the observer/over rule, the framed number sl(T_s) =
   ℓ(T_s, T_s + ε∂_y)), 3012-3022 (rem:sl-convention), 341-343 (def:transverse-front), 2380-2520 (the fd block's
   Legendrian helix / pushoff annulus / positive pushoff conventions; grep "pushoff"), 3404-3492 (fd:contact — the only
   consumer — and its proof: the cusp calculation tb − r = w − D = sl_Ng(F), and "identifies Ng's pushoff as Etnyre's
   positive pushoff").
2. The Lean declaration: work/reviews/src-contact-reviewer-input-statement.lean.txt (the module SM/SrcContact.lean with
   every proof replaced by sorry: the conversions toE3/toSpace, TransverseKnot.circle/spatial, slCircle, sl,
   IsLegendrianFrontOf, the structure SrcContactClauses, the axiom src_contact, rot/tb/src_contact_spec, and the sanity
   theorems SrcContactClauses.pushoff_slNg, SrcContactConsequence, src_contact_iff_consequence — the sanity theorems are
   evidence, not under review; their statements tell you what the axiom is provably equivalent to). Its docstrings quote
   the registry — verify them, do not trust them.
3. Lean definition modules under work/lean/SM/ (definitions and docstrings; proofs not under review): TransverseFront.lean
   (Space, xOf/yOf/zOf/xzOf, contactForm, TransverseKnot, front, SmoothKnotDiagram.isOver/crossSign/writhe),
   GenericFront.lean and TransverseNeighborhood.lean (IsEmbeddedCircle, IsPositiveTransverse, IsLegendrian, alpha,
   IsPushoffAnnulus, IsPositivePushoff, IsCircleReparam, TransverselyIsotopic, GenericFrontHyp, IsGenericFront, front,
   cuspSet), LinkingCalculus.lean (linking, pushoff, ey, selfLinking, IsPositiveTransverseEmbedding, TransverseFamily,
   lcContactForm, lcCrossingSign — use grep; the module is long) and LinkingCalculusRow.lean (LinkingCalculusData),
   FrontSmooth.lean (SmoothFront, IsDownCusp, downCount, upCount, writhe, slNg — grep), NgBound.lean (NgBoundClauses).
4. Disclosed readings: work/AUTHOR_NOTES.md entry "Contact lane (src:contact, SM.sl, rows 94 …)" of 2026-09-15 with
   decisions D-SC-1..6 and the fidelity risks FR-SC-1..11 (including the judge's numeric consistency probe summary).
   Do NOT open work/drafts/.

YOUR TASK: compare the registry text clause by clause with the axiom and its clause structure. Every printed FORMULA
must be a field and every field a printed formula: "for an oriented Legendrian front with downward and upward cusp
counts D, U" (binder IsLegendrianFrontOf L F; D = F.downCount, U = F.upCount, w = F.writhe on the accepted class
SmoothFront of ng:front-domain — is IsDownCusp Etnyre's downward cusp? is the class narrower than "an oriented
Legendrian front" (FR-SC-2: knots only, ng:front-domain) and is that a WEAKENING only?), "r = (D−U)/2" (rotation),
"tb = w − (D+U)/2" (thurston_bennequin), "sl(T₊(L)) = tb(L) − r(L)" (pushoff_self_linking: quantified over EVERY
GenericFront.IsPositivePushoff — is that the literature's T₊(L), FR-SC-3?), "For a generic positive transverse front
(Definition def:transverse-front), self-linking equals its front writhe" (transverse_front_writhe on TransverseKnot,
sl K = writhe of K.front — over = smaller y, sign det_xz). Judge: (1) is the ∃-form over r, tb faithful (FR-SC-1) —
the document defines neither, the sanity theorem shows the axiom equivalent to the substituted consequence
(sl(T₊(L)) = w − D on the Legendrian class ∧ sl = w on the transverse class): does the ∃-form add or lose content
relative to the printed three formulas? (2) is `sl` the right number (FR-SC-4): the document's fd:framed-linking
number at row 88's radius, real-valued (FR-SC-10); check slCircle's definition and its 0-default off the class
(FR-SC-9); (3) is the axiom STRONGER than printed anywhere (a serious defect), e.g. does any field assert something for
objects outside the printed classes, or with the wrong sign convention (audit: over = smaller y ↔ observer at −∂_y,
det_xz(u_O,u_U), the pushoff direction +∂_y, Etnyre's "positive y axis into the page"; the printed proof of fd:contact
3432-3452 fixes these) — is the axiom TRUE mathematics on the accepted definitions (consistency is fatal if not)?
(4) WEAKER anywhere (fine, but list it); (5) are the sentences without fields (contact space and orientation
convention, the D+U remark, the Geiges/Etnyre provenance parenthesis, "These are the local front and pushoff source
formulas only") correctly treated as conventions/commentary (FR-SC-6/8)? Expand definitions to primitives. Default to
"not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason" (clause-by-clause, cite
registry and statement-file line numbers), "discrepancies", "stronger_than_source", "weaker_than_source" (arrays of
strings), "supporting_definitions_inspected" (Lean names), "reviewer_files_read" (relative paths).
