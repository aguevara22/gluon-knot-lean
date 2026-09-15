You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statement you are reviewing and you must not read its proof. Your job is a
statement-fidelity review of ONE R-lane row against its frozen specification text:
R:generic_transport (checklist row 173), Lean `RProof.generic_transport : … → ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ`
(module RProof/GenericTransport.lean), with the bundle `RProof.GenericTransportData` declared in the accepted statement panel
work/lean/RProof/X1Rows.lean (line ~1344; fields canonical_branch, empty_row, endpoint_rows_canonical, endpoint_rows_relabelled) — the
bundle IS under review (it was fixed with the nine R obligations but is reviewed with its row).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

BACKGROUND: the R rows have no printed theorem statement; their content is specified by frozen texts (reference/R/RA/*.md,
R_ASSEMBLY_SPEC.md, OPEN_WORK.md) and rendered as Prop bundles with one field per specified clause; the accepted rows R:localization /
R:parity / R:fibre_partition / R:generic_table (work/lean/RProof/Cores.lean), R:generic_selector (RProof/X1Rows.lean), R:exterior and
R:availability_0_1 (RProof/X1Rows2.lean) set the pattern — you MAY read their reviews work/reviews/r-*.json for the accepted readings
(δ-shape over all opposite punctured pairs, hs quantified rather than asserted, hn explicit, availability read on one side, C_Q base row).
The statement design record is work/drafts/rlane2/NOTES_FINAL.md (you MAY read it: the clause map of row 173 and its readings).

WHAT YOU MAY READ (nothing else under work/ ):
1. The frozen specification, verbatim: work/reviews/r-generic-transport-source-excerpt-R_GENERIC_COMMON_TRANSPORT_PROOF.md.txt
   (= reference/R/RA/R_GENERIC_COMMON_TRANSPORT_PROOF.md in full: "Statement and canonical branch" — the relabelled graph P/E, the sign
   identity (1), "Every generic branch can be put in this form by relabelling the strands in their transitive angular order", the
   transports (2) T_P(∅) = T_E(∅), T_P(a) = T_E(a), T_P(c) = T_E(c) — and the proof sections; the row's claim is the Statement:
   the empty row and the two endpoint singleton rows transport across the wall in every generic branch). Context: reference/R/RA/
   R_ATTACHMENT_WARRANTS.md (R-LOC-2, R-PAR-v6 — presuppositions consumed at a common radius), R_GENERIC_ORBIT_ACTUAL_TABLE.md and
   R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (the generic orbit, the selected pair, the six nonalternating sign triples), R_ASSEMBLY_SPEC.md
   (the fibre-sum assembly, full availability), reference/R/CV/d1_setup.tex 487-530 and 908-929 (def:wind, def:X1: the complete X₁ term
   τ of a row).
2. The Lean statement with every proof replaced by `sorry`: work/reviews/r-generic-transport-reviewer-input-statement.lean.txt (the row
   module RProof/GenericTransport.lean: 1118 theorems stripped; the row theorem `generic_transport` near line 6594 with the sibling-row
   shape hn E e f g h3 h4e h4f h4g hE → ∃ δ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ; everything else in the file — the
   G11 construction: subdivision, moved polygon, disc, RIII site, record twist — is the proof's construction, shown only because
   definitions are not withheld; do not review it). Do NOT open work/lean/RProof/GenericTransport.lean or anything under work/drafts/rlane2/
   except NOTES_FINAL.md.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/RProof/X1Rows.lean (the accepted panel:
   rowTerm := CV.X1Summand, Punctured, OppositeSides, outsideSupports, FullAvail, transportSupport, strandSign, ExtremeLocal,
   SelectedAB/AC/BC, xPair, the bundle GenericTransportData — READ IT IN FULL with its docstrings), RProof/X1Rows2.lean and
   RProof/X1Rows3.lean (definitions only: GT_G11, GT_G11_strong, ExactTriangleVisitOrders, the transport toolkit — the row theorem does not
   mention them), RProof/Cores.lean (LocalizationData, FibrePartitionData, genericAt, geomAt, triangleCrossings, transportSupport),
   CV/Events.lean (Event, IsSimpleRIII, Ind, CV.rep), CV/X1.lean (X1, Omega1, groupedPoly), CV/ChamberInvII.lean (X1Summand — definition
   lines only), SM/FlatCarriersDefs.lean, SM/Crossings.lean (IsCrossing, remote).

DISCLOSED READINGS (recorded in NOTES_FINAL.md and the AUTHOR_NOTES entries "R lane" of 2026-09-14 — you MAY read those entries):
the bundle's four fields: canonical_branch renders (1) "in the generic orbit the selected pair is ac iff all three determinant signs
agree" (with the generic orbit as ¬ExtremeLocal); empty_row renders T_P(∅) = T_E(∅) for every exterior independent support Q with
full availability (FullAvail read on side t, as in the accepted rows); endpoint_rows_canonical renders T_P(a) = T_E(a), T_P(c) = T_E(c)
in the canonical branch (all three signs equal; the endpoint rows are Q ∪ {xPair hef} and Q ∪ {xPair hfg} — check which crossings are
"a" and "c" under the relabelling e f g); endpoint_rows_relabelled renders "every generic branch can be put in this form by relabelling"
as the endpoint rows of the other selected pairs (SelectedAB → rows a, b; SelectedBC → rows b, c); the identities are symmetric in the
two sides so no side is named P (both t, t' opposite punctured parameters); hs (the crossing-set identification) is a universally
quantified hypothesis as in every accepted R row; hn : 3 ≤ n explicit; δ ≤ E.radius shape; rowTerm = the complete X₁ term of Q ∪ J
(CV.X1Summand: wind × ∏ Ω₁ on present rows, 0 on absent rows). Proof-side only (not statement): the RIII-wall invariance G11 was proved
by an explicit polygonal RIII move (decision D-G11), irrelevant to the statement.

YOUR TASK: compare the specification's Statement paragraph and displays (1)-(2) with the four fields of GenericTransportData, expanding
every definition to primitives (transportSupport, rowTerm, FullAvail, outsideSupports, strandSign, ExtremeLocal, SelectedAC …); is every
specified clause a field and every field a specified clause or a disclosed extra? Check the relabelling reading (the six generic
branches: does endpoint_rows_relabelled cover the four non-canonical branches with the right endpoint rows?), the availability
hypothesis (full availability is specified), the exterior independent support Q (outsideSupports), the sides (opposite punctured
parameters), and that the row theorem's shape matches the accepted sibling rows. Say where the Lean is STRONGER or WEAKER; label
non-blocking notes. Default to "not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite specification and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
