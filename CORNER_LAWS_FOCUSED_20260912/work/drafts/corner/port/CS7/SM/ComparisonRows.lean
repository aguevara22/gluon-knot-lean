-- Ported <HH:MM>Z 2026-09-19 from work/drafts/corner/W6_Assembled.lean by the pod executor (files prepared by the W6-GLUE assembler)
-- SM/ComparisonRows.lean — rows 127 thm:comparison and 128 cor:C-inherits (FIXED names SM.thm_comparison, SM.cor_C_inherits):
-- the comparison lane's `thm_comparison_of` / `cor_C_inherits_of` (SM/Comparison.lean, SM/CInherits.lean) at rows 110
-- (`thm_C_S7`, SM/CS7.lean) and 112 (`thm_C_soft`, SM/CSoft.lean); statements as in work/drafts/comparison/Statements_FINAL.lean §5.
import SM.CS7
import SM.CSoft
import SM.Comparison
import SM.CInherits

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
