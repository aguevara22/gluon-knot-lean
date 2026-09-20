-- Ported 15:05Z 2026-09-15 from work/drafts/contact/Statements_FINAL.lean (the theorem CV.ax_etnyre of §6, proved from the axiom src_contact alone) by the pod executor; body verbatim; row 161 CV:ax:etnyre.
import SM.FdContactStatements

/-! # Row 161 CV:ax:etnyre (reference/R/CV/d10_axioms.tex 387-397) -/

namespace CV

open SM

/-- **Row 161 CV:ax:etnyre** — from the transverse clause of the literature interface `SM.src_contact`
(the statement `CV.AxEtnyreData`, SM/FdContactStatements.lean). -/
theorem ax_etnyre : AxEtnyreData :=
  ⟨fun D K hD _ => by subst hD; exact SM.src_contact_spec.transverse_front_writhe K⟩

end CV
