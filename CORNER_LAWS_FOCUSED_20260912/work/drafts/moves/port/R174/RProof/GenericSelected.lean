-- Ported <HH:MM>Z 2026-09-16 from work/drafts/moves/R174W2_Assembled.lean lines 7328-7369 (the RProof row block, verbatim) by
-- the row-174 wave-2 assembler: the row theorem RProof.generic_selected (row 174, R:generic_selected; FIXED name; statement
-- byte-identical to work/drafts/cvtail/Wave1_Assembled.lean lines 2543-2549) := SM.Link.r174_generic_selected_of_arc_rec
-- SM.Link.r174v_arc_rec_moves_proof (RProof/GenericSelectedUnits.lean).  Axioms: propext, Classical.choice, Quot.sound,
-- SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact; no placeholder.
import RProof.GenericSelectedUnits

/-! ## Row 174 (ORDER 182) — R:generic_selected: the row theorem

The FIXED name `RProof.generic_selected` with the FIXED statement (work/drafts/cvtail/Wave1_Assembled.lean
lines 2543-2549, byte-identical), proved as `r174_generic_selected_of_arc_rec r174v_arc_rec_moves_proof`. -/

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 174 (ORDER 182), R:generic_selected** (FIXED name and statement;
R_GENERIC_SELECTED_COUPLE_PROOF.md, Statement).  Printed obligation:
"Fix a full-availability fiber at a simple RIII wall in the generic graph orbit and an exterior
independent support `Q`. Relabel the three local crossings so the exact local words are
`P = a b A a c B b c C` (edges ab,bc), `E = b a A c a B c b C` (edge ac). Thus `b` is the degree-two
vertex of the path, and `ac` is its complementary independent pair on `P`. If `T_nu(J)` denotes the
complete X1 term of `Q union J` on side `nu`, absent rows being zero, then `T_E(b) = T_P(b) + T_P(ac)`
(GSC). This is exactly the selected `b/ac` complementary-couple identity, with the opposite
coorientation obtained by multiplying the equation by `-1`."
The side `P` is the two-edge side (`EdgeAB ∧ EdgeBC`, centre `b`), `E` the other side; the three
branches are the fields of `GenericSelectedData` (RProof/X1Rows.lean).

Proof: the RA ledger `gsc_generic_selected_of_moves` (RProof/RALedgers.lean) at the carrier floor
`CV.carrierSlotFloor`, with the interface Prop `gsc_moves` realised by
`SM.Link.r174_gsc_moves_of_arc_rec` from the arc-record identification
`SM.Link.r174v_arc_rec_moves_proof : SM.Link.r174_arc_rec_moves` (RProof/GenericSelectedUnits.lean:
site I-174, units HREC, CARRIERS, SITEIN, WALL, SMOOTH, the composition, and Route V — the visit data
`ψ_A`, `ψ_B` of the two arcs of `x'`).  Axioms: the standard three and the six literature interfaces
(`SM.lit_homfly`, `SM.lit_homfly_descent`, `SM.lp_lm`, `SM.lp_lm_uniqueness`, `SM.ng_finite_word`,
`SM.src_contact`); no placeholder. -/
theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ :=
  SM.Link.r174_generic_selected_of_arc_rec SM.Link.r174v_arc_rec_moves_proof hn E e f g h3 h4e h4f h4g hE

end RProof
