-- Ported <HH:MM>Z 2026-09-16 from work/drafts/cvtail/Wave1_Assembled.lean lines 4220-4226 (the row block, verbatim) by the pod executor: the row theorem RProof.cv_R (row 178, R:cv_theorem; FIXED name and statement `CV.hyp_R`, the R6 all-parameters form of CV ax:R) assembled by the accepted library theorem cv_R_of_rows (RProof/RALedgers.lean) from the four accepted R rows 174/175/176/177.
import RProof.RALedgers
import RProof.GenericSelected
import RProof.ExtremePairZero
import RProof.ExtremeTransport
import RProof.ExtremeSelected

/-! # Row 178 R:cv_theorem — `RProof.cv_R : CV.hyp_R`

The CV R theorem in its `ax:R` form (reference/R/CV/d10_axioms.tex, Axiom "Hypothesis R for X₁"; R_ASSEMBLY_SPEC.md): the
X₁ state sum takes equal values on the two sides of every simple RIII wall, for all parameters. Assembled from the four R
rows 174 (`generic_selected`), 175 (`extreme_pair_zero`), 176 (`extreme_transport`), 177 (`extreme_selected`) by the
accepted `cv_R_of_rows` (which itself uses the accepted rows 170/172/173 and chamber invariance). -/

namespace RProof

/-- **Row 178, R:cv_theorem** (FIXED: `RProof.cv_R : CV.hyp_R`, the R6 all-parameters form of CV:ax:R). -/
theorem cv_R : CV.hyp_R :=
  cv_R_of_rows
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => generic_selected hn E e f g h3 h4e h4f h4g hE)
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => extreme_pair_zero hn E e f g h3 h4e h4f h4g hE)
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => extreme_transport hn E e f g h3 h4e h4f h4g hE)
    (fun _ _ hn E e f g h3 h4e h4f h4g hE => extreme_selected hn E e f g h3 h4e h4f h4g hE)

end RProof
