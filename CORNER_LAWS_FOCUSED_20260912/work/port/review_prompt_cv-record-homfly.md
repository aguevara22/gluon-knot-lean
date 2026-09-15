You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE definition row of the CV lane against ONE printed source definition of the
paper "CV" (reference/R/CV/d1_setup.tex, frozen). The row is named in your task.

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed source, verbatim: CV:def:record → work/reviews/cv-def-record-source-excerpt-lines-522-551.tex.txt
   (= d1_setup.tex 522-551); CV:def:homfly → work/reviews/cv-def-homfly-source-excerpt-lines-552-564.tex.txt
   (= d1_setup.tex 552-564). Context, ONLY to fix notation: the other excerpt; reference/SM/sm-3-statesum.tex 352-370
   (SM def:gauss-record: the crossing record of a diagram and named record isomorphisms — the SM rendering of the same
   object, accepted), 1180-1190 (lp:split-circle), 905-990 (the literature inputs: H_D, skein); reference/R/CV/
   d10_axioms.tex 342-360 (CV:ax:homfly, derived in this project as CV.ax_homfly — accepted); reference/R/CV/d1_setup.tex
   315-344 (CV def:diagrammatic: the traversal circle and its crossings), 565-591 (def:piecediagram, only for the
   words "record" and "traversal circle" if needed).
2. The Lean statements with the two row proofs replaced by `sorry`:
   work/reviews/cv-record-homfly-reviewer-input-statement.lean.txt (module CV/RecordHomfly.lean: module docstring with
   the notation map and the readings chosen — verify, do not trust; the definitions SingleCircle, PreservesCyclicOrder,
   CarriesDoublePoints, CarriesOverUnder, IsRecordIsoData, Isomorphic (under review as part of the rows); helper
   lemmas with proofs NOT under review; bundle `CV.RecordDefinitionData` / theorem `CV.record_definition`; bundle
   `CV.HomflyDefinitionData` / theorem `CV.homfly_definition`). Do NOT open work/lean/CV/RecordHomfly.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/SM/LinkRecord.lean (Record:
   comps, M, comp, succ, pair, isOver, sgn and their axioms; componentCount; Crossing; RecordIso with fields e, Φ,
   succ_eq, pair_eq, bit_eq, sgn_eq, comp_eq; refl/symm/trans), LinkDiagramRecord.lean (Diagram.record, nextVisit, twin,
   VisitBetween, cycBetween, visitCoord; RecordIso.ExtendsToCircleMaps), LinkDiagram.lean (Diagram, componentCount,
   Visit, overStrand, sign, compOf), GaussRecordDefinition.lean (the accepted SM def:gauss-record bundle — statement
   only), LinkInterfaces.lean (homfly), LinkMoves.lean (IsSkeinTriple, LinkEquiv, IsSplitCircleAddition),
   LinkLaurentRing.lean (R.a, R.aInv, R.z, R.zInv, R.delta), CV/Axioms.lean (bundle CV.AxHomflyData — statement only),
   PolynomialBlock.lean END (lp:core, lp:split-circle bundles — statements only).

YOUR TASK. CV:def:record — printed: "A record consists of an oriented circle Γ; a finite subset V ⊂ Γ of marked
points; a partition of V into two-element sets, the double points; for each double point a designation of one of its
two points as the over position and the other as the under position; and for each double point a sign in {±1}. The
record of a link diagram is the one obtained by taking Γ to be its traversal circle, V the preimages of its crossings,
the partition the crossing correspondence, and the over/under and sign data those of the diagram. A record isomorphism
… is a bijection φ : V → V′ that (a) preserves the cyclic order …; (b) carries double points to double points; (c)
carries over positions to over positions and under to under; (d) preserves signs. Condition (a) says exactly that φ
extends to an orientation-preserving homeomorphism Γ → Γ′ carrying V onto V′, and any two such extensions are isotopic
… Records are isomorphic when such a φ exists; the relation is an equivalence." Judge: field `record` (CV's record as
an SM Record with one circle: finite M, one succ-cycle, double points = pairs, over/under bits opposite on a pair, signs
±1 equal on a pair — is the SM Record with SingleCircle exactly CV's record? is CV's "oriented circle Γ with a finite
subset V" faithfully replaced by the cyclic successor on V (the abstract circle is not carried — is that a loss?));
field `diagram_record` (the record of a diagram: traversal circle, visits, twin pairing, over/under, signs);
field `iso` (what a RecordIso provides: (a)-(d)); field `iso_iff` (on one-component diagrams, a bijection satisfying
(a)-(d) — PreservesCyclicOrder one-directional, CarriesDoublePoints, CarriesOverUnder, signs — is exactly the Φ of a
RecordIso: is this the printed definition of record isomorphism, and is restricting the characterisation to
one-component diagrams CV's domain?); field `extension` (φ extends to orientation-preserving circle maps —
ExtendsToCircleMaps: expand it; is the isotopy-uniqueness sentence "any two such extensions are isotopic" rendered, and
if not, is it a definitional clause or a justification? the docstring says it is not rendered — judge); field
`equivalence` (Isomorphic is an equivalence relation). Is anything printed missing, anything in Lean unprinted?
CV:def:homfly — printed: "P_H is normalized by the first two identities below; the third is their consequence,
obtained by applying the skein relation at a crossing between L and a split unknot, and is displayed because it fixes
the reader's convention for a split component: P(○) = 1, aP(L₊) − a⁻¹P(L₋) = zP(L₀), P(L ⊔ ○) = ((a − a⁻¹)/z) P(L)."
Judge: fields unknot, skein (same convention as SM's?), split_circle (IsSplitCircleAddition D D′ → homfly D′ =
(R.a − R.aInv) * R.zInv * homfly D — is IsSplitCircleAddition the printed L ⊔ ○, a split unknot added to L?),
normalized ("normalized by the first two identities" read as uniqueness among LinkEquiv-invariant maps with those two
identities — faithful reading of "normalized"?), split_circle_consequence ("the third is their consequence": every such
normalised map satisfies the third identity — faithful? the printed derivation route (skein at a kink) is not what is
rendered, only the claim). Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; default to
"not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
