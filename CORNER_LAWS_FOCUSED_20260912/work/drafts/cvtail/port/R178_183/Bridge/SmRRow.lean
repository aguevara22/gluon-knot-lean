-- Ported <HH:MM>Z 2026-09-16 from work/drafts/cvtail/Wave1_Assembled.lean lines 4231-4237 (the row block, verbatim) by the pod executor: the row theorem Bridge.sm_R (row 183, Bridge:theorem; FIXED name and statement `SM.hyp_R`), the displayed bridge theorem (19)-(21) of reference/BRIDGE/BRIDGE.md section 3 at the proved RProof.cv_R through the accepted library theorem SM.sm_R_of_cv_R (Bridge/SmR.lean; B1-B4).
import RProof.CvR
import Bridge.SmR

/-! # Row 183 Bridge:theorem — `Bridge.sm_R : SM.hyp_R`

BRIDGE.md section 3, the displayed theorem (19)-(21): the frozen RA result in the CV `ax:R` form implies SM11's Hypothesis R
(`C(P₊) = C(P₋)` at every simple triple wall germ) through the identification lemmas B1-B4. The accepted library theorem
`SM.sm_R_of_cv_R` is that implication; the row applies it to the proved `RProof.cv_R`. No new mathematics (FR-B-183). -/

namespace Bridge

/-- **Row 183, Bridge:theorem.** The displayed bridge theorem (19)-(21): the proved CV R theorem gives SM's
Hypothesis R through B1-B4 — the accepted library theorem `SM.sm_R_of_cv_R` (Bridge/SmR.lean) at the
proved `RProof.cv_R`; no new mathematics (FR-B-183). -/
theorem sm_R : SM.hyp_R := SM.sm_R_of_cv_R RProof.cv_R

end Bridge
