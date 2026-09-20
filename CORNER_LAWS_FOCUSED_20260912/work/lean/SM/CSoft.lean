-- Ported 20:00Z 2026-09-15 from work/drafts/corner/Wave2a_Assembled.lean lines 12218-12221 and 12223-12229 (corner chain lane, row 112 thm:C-soft: the row theorem `SM.thm_C_soft : CSoftData` (FIXED target name), body `thm_C_soft_of_floor thm_floor` as the frozen docstring prescribes once row 100 lands — it has, SM/CarrierFloorRows.lean; and the §7 consumer shape check) by the pod executor; statement line verbatim (the trailing ` by` of the draft's placeholder body dropped); the docstring rewritten for the accepted state; the §7 `example` REDUCED to the three ported rows `⟨cb_singleton, corner_values, thm_C_soft⟩` (the draft's `thm_C_S7_of_floor hF` conjunct dropped with row 110, its docstring kept verbatim); import block (plus SM.CBSingleton, SM.CornerValues for the example) and module docstring new (pattern of SM/CarrierFloorRows.lean).
import SM.CornerChainUnits
import SM.CarrierFloorRows
import SM.CBSingleton
import SM.CornerValues

/-! # Row 112 thm:C-soft (sm-4:984-991) — fixed target name `SM.thm_C_soft` -/

namespace SM

/-- **Theorem thm:C-soft** (sm-4:984-991; proof 993-1147; FIXED target name, axiom-policy.json): `CSoftData`
(SM/CornerChainStatements.lean §5) from thm:floor through `thm_C_soft_of_floor` (SM/CornerChainUnits.lean §5:
row 112 ← lem:corner-values ← cb:singleton ← thm:floor). -/
theorem thm_C_soft : CSoftData := thm_C_soft_of_floor thm_floor

/-! ## §7 Consumer shape check (thm:comparison, thm:uniqueness (c), (e)).
`UniquenessHypotheses.vertex_edge` / `.soft` (SM/Uniqueness.lean:57-76) have literally the shapes of
`CS7Data.vertex_edge_law` / `CSoftData.soft_theorem` with `F n Q := C` read on the polygon quotient
`GenericPolygon n`; the descent of `cornerStateSum` to the quotient is the accepted
`cornerStateSum_genericShift` (SM/CChamber.lean) — thm:comparison's business (FR-CC-13). -/
example : CbSingletonData ∧ CornerValuesData ∧ CSoftData :=
  ⟨cb_singleton, corner_values, thm_C_soft⟩

end SM
