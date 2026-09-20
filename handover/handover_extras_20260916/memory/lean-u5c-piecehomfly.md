---
name: lean-u5c-piecehomfly
description: "CV-DOM unit U5c DONE 2026-09-14 06:45Z: PieceHomflyTransported + row 147 CV.chamberinv; files, route, kernel-timeout gotchas"
metadata:
  node_type: memory
  type: project
---

U5c finished 06:45 UTC 09-14. Files (work/drafts/cvdom/U5c/): PieceHomflyTransport.lean (100 lines, imports CV.ChamberInvII +
CV.PieceIntrinsic; `CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq` via `exists_recordIso_of_geoCarrierCrossings_eq` +
`gausscode_polynomial`; `CV.pieceHomflyTransported`), CVChamberInv.lean (88 lines; `CV.ChamberInvData`, `CV.chamberinv_ii`,
`CV.chamberinv`; intended home CV/ChamberInvRow.lean; compiled via /tmp/u5c_olean overlay), PieceHomflyTransport_selfcontained.lean
(955 lines, 82 decls, same two theorems without PieceIntrinsic: block coordinate markCoord + TracedSuccessor orbit + RecordIso),
REPORT.md. All exit 0, no sorry. Axioms: standard + SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness (via gausscode_polynomial).
GOTCHAS: never reuse `hw : w.1 ∈ H` at type `(visitTwin w).1 ∈ H` (rw breaks) → mem_twin; type Visit-equivs on
`(geoPositiveLift ..).Γ.Visit` not the abbrev shadow; kernel deterministic timeout when several record clauses in one theorem
need `(Equiv.subtypeEquivRight _ a).1 ≡ a.1` inside real terms → one declaration per clause + rewrite with
Equiv.subtypeEquivRight_apply. Bisect kernel timeouts with /tmp copies + sorry, compiled in parallel.
