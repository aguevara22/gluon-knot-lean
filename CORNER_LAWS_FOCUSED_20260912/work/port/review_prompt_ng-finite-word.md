You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the declaration you are reviewing. Your job is a statement-fidelity review of ONE
literature interface — an `axiom` declaration — against its printed registry text. The row is
ng:finite-word (blueprint/AXIOM_REGISTRY.md, "ng:finite-word — AXIOM"), Lean axiom `SM.ng_finite_word :
SM.NgFiniteWordClauses` in module SM/FrontInterfaces.lean.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

BACKGROUND: the package admits exactly five literature inputs as axioms with fixed names (work/lean/axiom-policy.json,
"literature"); their statements must be transcribed from blueprint/AXIOM_REGISTRY.md — an axiom STRONGER than the
registry text is a serious defect, an axiom weaker than it fails its consumers. The other three accepted interfaces
(SM/LinkInterfaces.lean) use a Prop structure whose fields are the printed clauses; this one has a single field because
the registry block supplies no map (no ∃). The front block's design (work/reports/front-block-design-FINAL-20260913.md
§5-§8 and its fidelity risk FR-6; work/AUTHOR_NOTES.md entries "FR-1..FR-7" of 2026-09-14 — you MAY read both) fixes:
fronts on the word level are Rutherford's elementary front words (sm-3:1906-1925), closed oriented words `OWord`; the
moves of items 1-3 are the word rewrite relations of SM/FrontWords.lean.

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed registry text, verbatim: work/reviews/ng-finite-word-registry-excerpt.md.txt (= blueprint/AXIOM_REGISTRY.md
   78-121, quoting reference/SM/sm-3-statesum.tex 2170-2206). The surrounding printed text, to fix the meaning of every
   term: reference/SM/sm-3-statesum.tex 1900-1925 (the elementary front words: letters l_m, r_m, σ_m, the strand
   positions, the cusp directions), 1921-1949 (ng:commutation: typed disjoint-gadget commutations and the index
   changes), 1950-2007 (ng:front-I, II, III: the three local front moves and their word patterns), 2008-2045
   (ng:deletions: zigzag deletion and the crossed-cusp shortcut), 2046-2075 (ng:circle: the standard front circle and its
   deletion), 2076-2169 (ng:cusp-skein and eq. ng:cusp-words: the crossing interchange, its reflected pattern, the (t,u)
   table of compatible smoothings), 2207-2300 (the word procedure: in particular 2278-2279 "Only deletion directions of
   types I and II occur here; type III, commutations and cusp-skein changes preserve s" and 2284-2290, the two
   Rutherford corrections), 1825-1841 (ng:front-domain: s(F) = crossings + cusps).
2. The Lean module in full: work/reviews/ng-finite-word-reviewer-input-statement.lean.txt (= SM/FrontInterfaces.lean:
   the structure NgFiniteWordClauses, the axiom ng_finite_word, the definitions Move, PrincipalChain,
   Word.IsStandardCircleBase / OWord.IsStandardCircleBase, and theorems whose proofs are evidence, not under review —
   e.g. principalChain_iff_chain, Descends.of_principalChain, PrincipalChain.step_sCountSyn_eq,
   Skein.smoothing_sCountSyn_lt, the consumer projections ng_finite_word_chain / _finiteWordStatement / _bound). Its
   docstrings quote the registry — verify them, do not trust them. You MAY also read the unit's report
   work/drafts/front/FINITEWORD_REPORT.md (clause → field map, readings R1-R10, mismatches M1-M3) as the author's
   claims, to be checked.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/FrontWords.lean in full
   (Letter, Cuts, act, step, run, Word, Closed, crossingCount / cuspCount / sCount, OWord, sCountSyn, downCountSyn,
   writheSyn; the rewrite relations IsCommStep / IsComm, IsTypeI, IsTypeII, IsTypeIII, IsZigzagDeletion,
   IsCrossedCuspShortcut, IsCircleDeletion, IsCuspSkeinStep / IsCuspSkein; Pres, Del, Skein; Moves, Moves.Chain, Laws,
   wordMovesOf, FiniteWordStatement, word_bound_of), work/lean/SM/FrontPL.lean (definitions only, if needed for the
   word/front correspondence), work/lean/SM/FrontSmooth.lean (definitions only; sCount of a front if needed).

YOUR TASK: compare the registry text sentence by sentence with the axiom, expanding every Lean definition to primitives.
Decide in particular: (a) DOMAIN — "an actual finite front word on the domain of Definition ng:front-domain" versus
`∀ W : OWord` (every closed oriented word): is every closed oriented word an actual finite front word (does closedness
plus the cusp bits give exactly the words of sm-3:1906-1925), and does the axiom say anything about words that are not
actual? (b) THE MOVES — is `Move W W' := Pres W W' ∨ Del W W' ∨ ∃ C, Skein W W' C` exactly items 1-3: `Pres` =
commutations (IsComm: the disjoint-gadget exchange with the printed index changes) + the three local front moves
(IsTypeI, IsTypeII only in the deletion direction — judge against 2278-2279 — and IsTypeIII in both directions); `Del`
= zigzag deletion, crossed-cusp shortcut, deletion of a separated standard front circle; `Skein` = the cusp-skein
interchange "or its reflected pattern" with its compatible smoothing (check the (t,u) table of ng:cusp-words against
IsCuspSkeinStep's bit conditions and the reading of "reflected pattern" as the other principal direction). A move
missing from `Move` makes the axiom STRONGER than printed (a chain with fewer moves is claimed); a move present in
`Move` that the printed items do not list makes it WEAKER. Check every pattern's letters, indices (1-based) and bits
against the printed patterns. (c) THE CHAIN — "supplies a finite principal chain ... Stop at the first strict decrease of
s or at the standard-circle base": PrincipalChain's constructors base / stop / step with `s = OWord.sCountSyn` (the
letter count = crossings + cusps: is that s(F) of ng:front-domain on words?) and `Base = OWord.IsStandardCircleBase`
(defined on words by a labelled run: no crossing letter and every right cusp joins the two arms of one left cusp — is
that exactly "the standard-circle base", i.e. a union of separated standard front circles of ng:circle?); is
"principal" rendered (at a skein step the chain follows A → A′, the smoothing C is the side branch)? (d) THE OTHER
SENTENCES of the block ("Before that decrease the selected procedure does not increase s", "Secondary progress ...",
"Arm-string extension ...", "Thus every nonbase front has a finite principal chain to a front of smaller s", "At each
cusp-skein interchange, the compatible smoothing branch has smaller s", the scope paragraph): the file renders them as
theorems or as commentary rather than as fields — is any of them a clause that the axiom must state (so that the axiom
is WEAKER than the registry), or is any of them contradicted by the axiom's shape? (e) NOTHING EXTRA — is there any
content in the axiom beyond the registry text (e.g. a chain-length bound, a specific procedure, a claim about words the
source excludes)? Default to "not faithful" if in doubt; label non-blocking notes "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite registry and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
