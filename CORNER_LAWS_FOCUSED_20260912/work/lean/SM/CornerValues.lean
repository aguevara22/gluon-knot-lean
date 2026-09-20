-- Ported 20:00Z 2026-09-15 from work/drafts/corner/Wave2a_Assembled.lean lines 12208-12211 (corner chain lane, row 105 lem:corner-values: the row theorem `SM.corner_values : CornerValuesData`, body `corner_values_of_floor thm_floor` as the frozen docstring prescribes once row 100 lands — it has, SM/CarrierFloorRows.lean) by the pod executor; statement line verbatim (the trailing ` by` of the draft's placeholder body dropped); the docstring rewritten for the accepted state; import block and module docstring new (pattern of SM/CarrierFloorRows.lean).
import SM.CornerChainUnits
import SM.CarrierFloorRows

/-! # Row 105 lem:corner-values (sm-3:4801-4809) -/

namespace SM

/-- **Row 105 lem:corner-values** (sm-3:4801-4809; proof 4810-4820; proposed name): `CornerValuesData`
(SM/CornerChainStatements.lean §3) from thm:floor through `corner_values_of_floor` (SM/CornerChainUnits.lean §3;
clause (i) is the unconditional `corner_values_i`, clause (ii) is cb:singleton at `(Q, y)`). -/
theorem corner_values : CornerValuesData := corner_values_of_floor thm_floor

end SM
