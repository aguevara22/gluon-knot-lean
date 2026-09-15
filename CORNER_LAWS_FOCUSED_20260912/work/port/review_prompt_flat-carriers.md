You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE row against its printed source statement (frame SM15). The row is named in
your task: def:flat-carriers (definition) or cor:flat-carriers (corollary).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

WHAT YOU MAY READ (nothing else under work/ ):
1. The printed sources, verbatim: work/reviews/def-flat-carriers-source-excerpt-lines-788-804.tex.txt (=
   reference/SM/sm-3-statesum.tex 788-804, def:flat-carriers) and work/reviews/cor-flat-carriers-source-excerpt-
   lines-805-836.tex.txt (= 805-836, cor:flat-carriers with clauses (i),(ii),(iii), the closing sentences and the
   \status line — read the \status line: round 4 broadened clause (ii)'s rotation sentence to cover the centre
   copy). Context, ONLY to fix notation: reference/SM/sm-3-statesum.tex 836-905 (the printed proof), 9-60
   (def:decomposition, def:smoothing with the reconnection ρ_S, conv:selected-visits, lem:carriers), 242-260
   (def:uniform), reference/SM/sm-1-polygons.tex 778-826 (lem:flat-sides, whose hypotheses these rows carry;
   clauses (ii),(iii) give the common cyclic Gauss word and the fused-edge bijection), 240-268 (def:gauss,
   def:interlace), 138-160 (def:crossings), and its def:germ / def:walls (grep `label{def:germ}`,
   `label{def:walls}`: the right side is τ_j = −1, the left side τ_j = +1 — verify at sm-1:743-744 or wherever the
   naming is printed; the plan cites sm-4:205 for W(right) − W(left) = W(del)).
2. The Lean statements with the two row proofs replaced by `sorry`: work/reviews/flat-carriers-reviewer-input-
   statement.lean.txt (= the design's Statement_FINAL.lean: ~730 lines of DEFINITIONS — the "geo*" carrier
   machinery on `CrossingGeometry` (geoMarkPosition, geoMarkList, geoMarkSuccessor, geoSmoothingSuccessor,
   GeoComponent, geoOwner, geoComponentMarkList, geoComponentPlaneCycle, geoComponentCornerList, geoCornerCount,
   geoCornerMark, geoCornerPolygon, geoCornerTurn, geoCarrierCrossings, GeoIndependent, cornerSelector,
   geoCarrierSelector), the flat-wall objects (CommonSupports, IsRightSide, IsLeftSide, markTransport,
   transportSupport, deletionSupport, fusionMark, delMark, centralCarrierThroughJ, deletionCopyThroughJ,
   geoComponentEquivGeneric), the spec `GeoCarrierSpec`, the bundles `FlatCarriersDefinitionData` (def row) and
   `FlatCarriersData` (cor row) — and the two theorems `flat_carriers_definition`, `flat_carriers` with the
   hypotheses of lem:flat-sides). Supporting lemma proofs are not under review. Do NOT open work/lean/SM/
   FlatCarriers.lean or work/lean/SM/FlatCarriersDefs.lean (same text) or work/drafts/flatcarriers/U*.lean.
3. The executor's recorded statement decisions: work/drafts/flatcarriers/PLAN_FINAL.md §2 (clause → field table for
   both rows) and §3 (STRONGER / WEAKER list) — these are the dispositions you must judge, not trust.
4. Lean definition modules (definitions and docstrings only), all accepted rows: work/lean/SM/FlatSides.lean
   (FlatSidesData, flat_sides — lem:flat-sides), FlatFusionData.lean, GeometricRecords.lean (GeometricRecordsAgree),
   GeometricTransport.lean (CrossingParameterOrderAgrees), CrossingGeometry.lean, WallGerm*.lean / GermDefinition.lean
   (WallGerm, sideTuple, SideParameter, center, radius), DeletionChamber.lean (deleteVertex), SmoothingDefinition.lean
   (SmoothingData — def:smoothing), SelectedVisitsConvention.lean, CarriersLemma.lean (CarriersLemmaData), the
   Carrier lane definitions (CarrierMarks.lean Mark/markPosition, CarrierSuccessor.lean markSuccessor,
   CarrierSmoothing.lean selectedMarkPerm/smoothingSuccessor/Component/owner, CarrierClosedTrace.lean,
   CarrierTrueCorners.lean, CarrierCornerPolygon.lean ccpCornerPolygon), UniformDefinition.lean (carrierRotation),
   RotationNumber.lean (rotationNumber), Chirotope.lean (turn), Polygon.lean, EuclideanPlane.lean.

YOUR TASK (for YOUR row): decide whether the definitions + bundle pin down exactly the printed text.
def:flat-carriers: "Under the hypotheses of lem:flat-sides" (the theorem hypotheses hn g hz hb hc hsc and the
radius); "identify the crossing visits of the two sides, of the centre P(0) and of the deletion P(0)∖j through the
common cyclic Gauss word of that lemma's clauses (ii) and (iii)" (fields common_gauss_word, identify_deletion,
identify_sides_marks, identify_deletion_marks — the last two extend the identification to marks: STRONGER,
judge); "fix an independent set S in their common interlacement graph" (common_interlacement,
independent_supports); "In each of these four configurations mark the traversal circle at every original vertex
and every crossing visit, exchange the two outgoing successors at the two visits of every selected crossing — the
reconnection of def:smoothing with conv:selected-visits — and trace the resulting oriented closed cycles by the
inherited straight subsegments" (one `GeoCarrierSpec` per configuration: centre_carriers, deletion_carriers,
side_carriers — read GeoCarrierSpec's fields: marks, successor gap, reconnection ρ_S = ρ ∘ swap, carriers = cycles,
traced successor, inherited pieces; is this exactly the printed construction, "no genericity being assumed" at
the centre?); "These oriented closed polygonal cycles are the carriers of S in that configuration"
(carriers_are_cycles); "On the two generic sides they are the carriers of def:smoothing"
(sides_are_smoothing_carriers: geo* = accepted* through geoComponentEquivGeneric and the accepted SmoothingData);
"at the centre and on the deletion the same words define them, no genericity being assumed"
(centre_deletion_same_words). cor:flat-carriers: "fix an independent set S … form the carriers of S on both
sides, at the centre and on the deletion" (named_sides: right = τ_j < 0 side? check IsRightSide/IsLeftSide against
the printed naming); (i) "The carriers correspond under their named traversal arcs" (correspond_sides,
correspond_deletion — read as ρ_S-conjugation + owner-iff + surjectivity: judge the reading of "named traversal
arcs"); "Exactly one contains μ_j" (unique_through_mu_j); "The central copy of that carrier differs from its
deletion copy only by the positive-flat subdivision at μ_j" (central_vs_deletion_through_mu_j: five conjuncts
incl. mark-cycle and corner-cycle identities with μ_j erased, StrictBetween, fused positive multiples); "every
other central carrier is unchanged by deletion" (others_unchanged: mark, corner and plane cycles); "Every carrier
has nonzero segments and no antiparallel corner; except for that one central zero turn, all corner turns are
nonzero" (nonzero_segments, no_antiparallel, turns_nonzero — four configurations; turn = 0 ↔ corner = μ_j at
the centre); (ii) "Corresponding carriers have the same retained self-crossing visits, pairing, signs and positive
over/under bits" (same_retained_crossings, same_pairing, same_signs); "They have the same signed rotation and hence
the same absolute rotation" (same_rotation, incl. the centre copy per the round-4 status note); "Every
corresponding corner away from μ_j has the same turn sign on both sides and in the deletion" (same_turn_signs;
centre_turn_signs is a flagged broadening from the proof text — judge); "The extra corner at μ_j is right on the
right side and left on the left side" (extra_corner: turn −1 on the right side, +1 on the left; is right = −1 the
printed convention?); (iii) the selector definition (cornerSelector / geoCarrierSelector / selector_def: 1 if all
turns right, (−1)^c if all c turns left, 0 if mixed), "W_right − W_left = W_del" for the carrier through μ_j
(selector_identity), "All other corresponding carrier selectors agree" (other_selectors_agree); the closing
sentences (geometric/combinatorial data only; no state-sum value at the flat centre) are non-definitional.
Expand definitions to primitives where feasible (the geo* machinery is long — verify at least that each printed
notion has the right primitive content: marks = vertices ⊕ visits at their traversal positions; successor = next
mark on the traversal circle; reconnection = swap of the two visits of each selected crossing; carriers = cycles;
corner polygon = the true corners in cyclic order; turn = sign det(in, out)). Say where the Lean is STRONGER or
WEAKER; default to "not faithful" if in doubt; label non-blocking discrepancies "non-blocking".

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite source and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
