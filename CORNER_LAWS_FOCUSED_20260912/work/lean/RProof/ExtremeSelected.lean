-- Ported 08:06Z 2026-09-19 by the pod executor (file prepared by the row-177 wave-3d assembler, W3D_ASSEMBLY_REPORT.md):
-- the row theorem RProof.extreme_selected (row 177, R:extreme_selected; FIXED name; statement byte-identical to
-- work/drafts/cvtail/Statements_FINAL.lean lines 803-809 and to RProof/ExtremeTransport.lean lines 39-45 with
-- ExtremeTransportData replaced by ExtremeSelectedData, = RowShape @ExtremeSelectedData instantiated)
-- := SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE (RProof/ExtremeSelectedUnits.lean).
-- Axioms: propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness,
-- SM.ng_finite_word, SM.src_contact; no placeholder.
import RProof.ExtremeSelectedUnits

/-! ## Row 177 (ORDER 174) — R:extreme_selected: the row theorem

The FIXED name `RProof.extreme_selected` with the FIXED statement (work/drafts/cvtail/Statements_FINAL.lean lines 803–809,
byte-identical; the binder form of the accepted siblings `generic_transport`, `generic_selected`, `extreme_pair_zero`,
`extreme_transport`, of which `RowShape @ExtremeSelectedData` (RProof/RALedgers.lean) is the fixed shape), proved as
`SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE`. -/

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 177 (ORDER 174), R:extreme_selected** (FIXED name and statement; R_EXTREME_SELECTED_COUPLE_PROOF.md,
Statement).  Printed obligation (RProof/X1Rows.lean, row 177): "Fix a full-availability fiber at a simple RIII wall in
the extreme graph orbit. Let `H` denote the side whose local graph is `K3`, let `L` denote the side whose local graph is
empty, and fix the outside support `Q`. … Full availability is a hypothesis of the statement, not merely scene-setting: it
says every member of `T={x,y,z}` is nonadjacent to `Q`, and therefore makes `Q union T` an independent support on `L`.
On `H`, `T` is not independent because its induced graph is `K3`. … Write `T_nu(J)` for the complete X1 term of
`Q union J` on side `nu`, with an absent row read as zero. Then `T_H(empty) - T_L(empty) = T_L(xyz)` (2). Since `xyz` is
absent on the `K3` side, (2) is exactly the extreme selected empty/full complementary-couple identity. Equation (2),
whose sides are named by their graphs, is independent of coorientation."  Formal content: for every simple RIII wall `E`
at `e f g`, some `0 < δ ≤ E.radius` with `ExtremeSelectedData hn E e f g δ` (X1Rows: `full_present_on_empty`,
`full_absent_on_complete`, `couple`).  Proof: the RA ledger `esc_ledger` replayed on the extended, record-clause interface
(`w3ck_esc_ledger`), the floor `CV.carrierSlotFloor` (row 155), the switched G11 core (`G11_core_sw`, row 177 (4):
`w3bi_switch_riii`), the value form of the site data (6) (`w3dk_rii_value_sites_data`: the two `j = 2` bigons and the RII
deletion, kink case by a flat subdivision), the carrier split of `Q ∪ T` on the empty side (SPLITA/SPLITB/SPLITC, the sign
table, `esc_FullSplitData`), and the two outer clauses with the residue closed (KNOT + RESPAR's parity + RESID's
identification) — `w3ck_extreme_selected : RowShape @ExtremeSelectedData` (RProof/ExtremeSelectedUnits.lean). -/
theorem extreme_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ :=
  SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE

end RProof
