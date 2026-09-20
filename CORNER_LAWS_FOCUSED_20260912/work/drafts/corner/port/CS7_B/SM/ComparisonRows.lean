-- Ported <HH:MM>Z 2026-09-19 from work/drafts/corner/W6_Assembled_B.lean by the pod executor (files prepared by the W6-GLUE assembler): the row theorems of rows 127 thm:comparison and 128 cor:C-inherits — signatures verbatim from work/drafts/comparison/Comparison_Assembled.lean lines 1009-1011 and 1016 (the placeholder bodies' trailing ` by` dropped), bodies the one-liners work/drafts/comparison/port/PORT_REPORT.md §5 prescribes once `SM.thm_C_S7` lands (SM/CS7.lean); import block, module docstring and docstrings new (pattern of SM/AnchorValuesRow.lean).
import SM.CS7
import SM.CSoft
import SM.Comparison
import SM.CInherits

/-! # Rows 127 thm:comparison (sm-6:299-311) and 128 cor:C-inherits (sm-6:313-372) — FIXED names `SM.thm_comparison`,
`SM.cor_C_inherits`

The two row theorems on the accepted rows 110 (`SM.thm_C_S7`, SM/CS7.lean) and 112 (`SM.thm_C_soft`, SM/CSoft.lean), through
the conditional theorems `thm_comparison_of` (SM/Comparison.lean) and `cor_C_inherits_of` (SM/CInherits.lean); hyp:R is an
explicit parameter (policy mode `explicit_parameter`, `SM.hyp_R`). -/

namespace SM

/-- Row 127 thm:comparison (FIXED name; hyp:R explicit).  "Assume Hypothesis R.  Then C(P) = A(P) for
every generic polygon P." -/
theorem thm_comparison (hR : hyp_R) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
      cornerStateSum hn hP = amplitude P hP.1 hn :=
  thm_comparison_of hR thm_C_S7 thm_C_soft

/-- Row 128 cor:C-inherits (FIXED name; hyp:R explicit). -/
theorem cor_C_inherits (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft

end SM
