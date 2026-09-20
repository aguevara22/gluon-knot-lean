# CS7_STATE — row 110 thm:C-S7 after corner wave 3 (2026-09-15 22:35 UTC / 6:35pm ET) — NOT PORTED

**Row 110: both leaves open, 5 named Props remaining.**  Source: `work/drafts/corner/W3_Assembled.lean` (8,958 lines, sha256
`109050d918ecd5371c8a79f699aaa52bbb6100425925ffbcb5a163e56883736f`; 0 errors; 12 sorried bodies).  `SM.thm_C_S7 : CS7Data`
compiles (`thm_C_S7_of_floor thm_floor`) but carries `sorryAx` through `s7_sliding_law_at` and `s7_bigon_law_at`.

Sorry-free reductions of the leaves to named Props (all statements verbatim the units' black boxes):
* `w3_s7_sliding_law_at_of₂ : w3_SlidingRet → w3_SlidingCarriers → s7_sliding_law_at-statement` (line 4829)
  — S1 `w3_SlidingRet` (= ROT's `s7q_box_ret`) is FALSE as stated on the leg-`M` side (W3_RET_REPORT §2); it must be restated
  with RET's proved `s7r_SlidingTransport'` there (500-700 lines incl. ROT's transport section on the corrected structure);
  S3 1,300-2,050 (same restatement).  S2 (`w3_SlidingOrder` = `s7q_box_order`) PROVED at assembly from RET.  Sliding total
  ≈ 1,800-2,750 lines.
* `w3_s7_bigon_law_at_of : w3_BigonFSector → w3_BigonReturnedRows → w3_BigonOneNewborn → s7_bigon_law_at-statement` (line 8854)
  — B1 2,300-3,600 (F's three geometric boxes + shape bridge, or K's F-aligned route), B2 3,500-5,400 (SITE 1,600-2,600 inside),
  B3 400-700.  Bigon total ≈ 6,200-9,700 lines.

Closed in wave 3: `s7q_box_split` (by SPLIT's `s7p_exists_pivotSplit`), `s7q_box_order` (by RET's `s7r_first_order`/`s7r_second_order`); RET's first-return law on both sides (corrected form on
the leg-`M` side); ROT's angle/merge/algebra/transport; F's residual identity; SITE's bigon site + wall fields; BLOCK's rows;
J's floor entries; K's row algebra.  Axioms on `thm_C_S7`: standard + six registered literature axioms + `sorryAx`.
Details: `work/drafts/corner/W3_ASSEMBLY_REPORT.md`.
