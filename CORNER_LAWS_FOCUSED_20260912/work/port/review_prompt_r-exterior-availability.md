You are an independent AI reviewer (Claude Code subagent) for a Lean 4 formalization. You did
not write the statements you are reviewing and you must not read their proofs. Your job is a
statement-fidelity review of ONE R-lane row against its frozen specification text. The row is named in your task:
either R:exterior (checklist row 168, Lean `RProof.exterior`, bundle `ExteriorData`) or R:availability_0_1 (row 170, Lean
`RProof.availability_zero_one`, bundle `AvailabilityZeroOneData`).

WORKING DIRECTORY (absolute): /workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912

BACKGROUND: the R rows have no printed theorem statement; their content is specified by frozen texts (reference/R/RA/*.md,
R_ASSEMBLY_SPEC.md — `find . -name R_ASSEMBLY_SPEC.md`) and rendered as Prop bundles with one field per specified clause. The accepted
R rows (localization, parity, fibre_partition, generic_table in work/lean/RProof/Cores.lean; generic_selector and the nine bundles in
work/lean/RProof/X1Rows.lean — accepted 2026-09-14) set the pattern; you MAY read their review files work/reviews/r-*.json and the
statement design record work/drafts/rlane2/NOTES_FINAL.md (§2 "Row 168", §3 "Row 170": clause maps with citations, readings, the
downgrade path recorded for row 170's summand_transport).

WHAT YOU MAY READ (nothing else under work/ ):
1. The frozen specification, verbatim: R:exterior → work/reviews/r-exterior-source-excerpt-R_ATTACHMENT_WARRANTS-R-EXTERIOR-1-lines-154-287.md.txt
   (= reference/R/RA/R_ATTACHMENT_WARRANTS.md "R-EXTERIOR-1 — the triangle-disjoint factor"); R:availability_0_1 →
   work/reviews/r-availability-source-excerpt-R_ATTACHMENT_WARRANTS-R-PAR-v6-lines-107-153.md.txt (= "R-PAR-v6 — parity and
   availability"); both: R_ASSEMBLY_SPEC.md (the fibre-sum assembly (1)-(4), the availability set, the exterior factor), the preamble
   reference/R/RA/R_ATTACHMENT_WARRANTS.md 1-30, reference/R/RA/R_GENERIC_ORBIT_ACTUAL_TABLE.md and R_GENERIC_COMMON_TRANSPORT_PROOF.md
   where the specification cites them, reference/R/CV/d1_setup.tex 908-930 (def:X1), 487-530 (def:wind, def:pieces).
2. The Lean statements with the row proofs replaced by `sorry`: work/reviews/r-exterior-availability-reviewer-input-statement.lean.txt
   (module RProof/X1Rows2.lean: imports RProof.X1Rows where the bundles ExteriorData / AvailabilityZeroOneData and every definition
   (rowTerm, fibreTerm, exteriorFactor, touchingFactor, outsideSupports, FullAvail, Punctured, OppositeSides, transportSupport,
   SummandTransport …) live — read work/lean/RProof/X1Rows.lean for those definitions and bundles (statements and docstrings only);
   the theorems RProof.exterior and RProof.availability_zero_one (proofs withheld) are the declarations under review; the EXT_/AV_
   sections are proof material, not under review). Do NOT open work/lean/RProof/X1Rows2.lean.
3. Lean definition modules (definitions and docstrings; proofs not under review): work/lean/RProof/Cores.lean, CV/X1.lean, CV/Carriers.lean,
   CV/Events.lean, CV/TripleEvents.lean, SM/FlatCarriersDefs.lean, SM/GeoCarrierCrossings.lean, CV/PieceCurve.lean (statements),
   CV/PieceHomflyTransport.lean (statement of PieceHomflyTransported), SM/GeoMarkTransport.lean (definitions), Bridge/B1.lean.

YOUR TASK: for YOUR row, compare the specification's Statement paragraph(s) with the bundle's fields (ExteriorData: independent_of_A,
wall_invariant, factorization — the exterior factor C_{Q,σ}(A) of the rows outside the triangle: independent of the local support A,
invariant across the wall, and the row term factors as exterior × touching; AvailabilityZeroOneData: fibre_zero, fibre_one,
fibre_correspond, summand_transport, summands_agree, fibre_identity — the availability-≤1 fibres and their transport across the wall).
Is every specified clause a field and every field a specified clause (presupposition fields labelled)? Is row 170's summand_transport
(a carrier bijection with matched weight / carrierR / groupedWrithe / groupedPoly / Omega1) faithful to "carrier/record, selector,
rotation and coefficient transport" or stronger than the bare fibre identity (the design record disclosed a downgrade path)? Is the
exterior factor's representation by the base row (equal to every representative by independent_of_A + wall_invariant) faithful; is the
printed full-availability binder kept (not a narrowing)? Binders: the accepted CV-event locus, ∃ δ punctured neighbourhood, Q ∈
outsideSupports, hn. Expand definitions to primitives; say where the Lean is STRONGER or WEAKER; label non-blocking notes. Default to
"not faithful" if in doubt.

OUTPUT: return ONLY a JSON object with keys: "verdict" ("faithful" | "not faithful"), "reason"
(clause-by-clause, cite specification and statement-file line numbers), "discrepancies",
"stronger_than_source", "weaker_than_source" (arrays of strings), "supporting_definitions_inspected"
(Lean names), "reviewer_files_read" (relative paths).
