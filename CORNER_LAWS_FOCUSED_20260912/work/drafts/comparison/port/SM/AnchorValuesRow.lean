-- Ported <HH:MM>Z 2026-09-15 from work/drafts/comparison/Comparison_Assembled.lean lines 1003-1005 (comparison lane §5, row 122 prop:anchor-values: the row theorem `SM.prop_anchor_values : AnchorValuesData` (proposed name), body `anchor_values_of thm_C_soft` as the frozen docstring (line 1003) prescribes once row 112 lands — it has, SM/CSoft.lean) by the pod executor; statement line 1004 verbatim (the trailing ` by` of the draft's placeholder body dropped); the docstring rewritten for the accepted state; import block and module docstring new (pattern of SM/CSoft.lean); wrappers `namespace SM` / `end SM` repeated.
import SM.AnchorValues
import SM.CSoft

/-! # Row 122 prop:anchor-values (sm-5:461-476) — proposed name `SM.prop_anchor_values` -/

namespace SM

/-- **Row 122 prop:anchor-values** (sm-5:461-476; proposed name `SM.prop_anchor_values`): `AnchorValuesData`
(SM/AnchorValues.lean §2) from thm:C-soft (`SM.thm_C_soft`, SM/CSoft.lean) through `anchor_values_of` — the body the
frozen docstring prescribed for the moment row 112 lands. -/
theorem prop_anchor_values : AnchorValuesData := anchor_values_of thm_C_soft

end SM
