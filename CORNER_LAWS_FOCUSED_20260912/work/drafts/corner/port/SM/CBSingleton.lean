-- Ported <HH:MM>Z 2026-09-15 from work/drafts/corner/Wave2a_Assembled.lean lines 12204-12206 (corner chain lane, row 103 cb:singleton: the row theorem `SM.cb_singleton : CbSingletonData`, body `cb_singleton_of_floor thm_floor` as the frozen docstring prescribes once row 100 lands — it has, SM/CarrierFloorRows.lean) by the pod executor; statement line verbatim (the trailing ` by` of the draft's placeholder body dropped); the docstring rewritten for the accepted state; import block and module docstring new (pattern of SM/CarrierFloorRows.lean).
import SM.CornerChainUnits
import SM.CarrierFloorRows

/-! # Row 103 cb:singleton (sm-3:4697-4702) -/

namespace SM

/-- **Row 103 cb:singleton** (sm-3:4697-4702; proof 4703-4759; proposed name): `CbSingletonData`
(SM/CornerChainStatements.lean §2) from thm:floor (`SM.thm_floor`, SM/CarrierFloorRows.lean) through the
conditional assembly `cb_singleton_of_floor` (SM/CornerChainUnits.lean §2). -/
theorem cb_singleton : CbSingletonData := cb_singleton_of_floor thm_floor

end SM
