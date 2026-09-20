-- Ported <HH:MM>Z 2026-09-16 from work/drafts/moves/R176W2_Assembled.lean lines 8973-9013 (the RProof row block, verbatim)
-- by the row-176 wave-2 assembler: the row theorem RProof.extreme_transport (row 176, R:extreme_transport; FIXED name;
-- statement byte-identical to work/drafts/cvtail/Wave1_Assembled.lean lines 3476-3482 and to the siblings' binder form,
-- = RowShape @ExtremeTransportData instantiated) := r176a_extreme_transport_rowShape n hn E e f g h3 h4e h4f h4g hE
-- (RProof/ExtremeTransportUnits.lean).  Axioms: propext, Classical.choice, Quot.sound, SM.lit_homfly,
-- SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact; no placeholder.
import RProof.ExtremeTransportUnits

/-! ## Row 176 (ORDER 175) — R:extreme_transport: the row theorem

The FIXED name `RProof.extreme_transport` with the FIXED statement (work/drafts/cvtail/Wave1_Assembled.lean
lines 3476–3482, byte-identical; the binder form of the accepted siblings `generic_transport`, `generic_selected`,
`extreme_pair_zero`, of which `RowShape @ExtremeTransportData` (RProof/RALedgers.lean) is the fixed shape), proved as
`r176a_extreme_transport_rowShape n hn E e f g h3 h4e h4f h4g hE`. -/

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-- **Row 176 (ORDER 175), R:extreme_transport** (FIXED name and statement; R_EXTREME_SINGLETON_TRANSPORT_PROOF.md,
"Statement and canonical data").  Printed obligation (RProof/X1Rows.lean, row 176): "Fix a full-availability fiber at a
simple RIII wall in the extreme graph orbit, an outside support `Q`, and the canonical words `H = x y A z x B y z C`
(local graph K3), `L = y x A x z B z y C` (local graph empty) (1). Full availability is part of the statement: every
member of `T={x,y,z}` is nonadjacent to `Q`, so every `Q union {j}` is independent on both sides. R-LOC-2 clause 4
identifies the two extreme local graphs in (1): `H[T]=K3` if and only if `L[T]` is empty. … Write `T_nu(J)` for the
complete X1 term of `Q union J`, with an absent row read as zero. Then, separately and without a symmetry assumption,
`T_H(x)=T_L(x)`, `T_H(y)=T_L(y)`, `T_H(z)=T_L(z)` (2). Let the oriented strand directions be `u1,u2,u3`, with
`x=(u1,u2)`, `y=(u1,u3)`, and `z=(u2,u3)`. The exact line-order calculation for the extreme orbit gives
`s_x = sgn det(u1,u2) = sigma`, `s_y = sgn det(u1,u3) = -sigma`, `s_z = sgn det(u2,u3) = sigma` (3)."  Formal
content: for every simple RIII wall `E` at `e f g`, some `0 < δ ≤ E.radius` with `ExtremeTransportData hn E e f g δ`
(X1Rows: `singleton_rows_present`, `graphs_complementary`, `sign_branch`, the three transports (2)).  Proof: the RA
ledger `est_ledger` re-based on the weak port relation (Site 176), the floor `CV.carrierSlotFloor`, the RII port
`r176h_hrec_wall_proof` (HSUCC), the LEDGER's `wind(S)`-uniform rotation ledger, the smoothing `r176s_DA` (SMOOTH)
with the record-level R-I `r176c_curl_removal_proof` (CURL), the outer carriers `r176o_outer_carriers_L_corrected_proof`
(OUTER) and the two (14)-bridges `r176m_mixed_bridge_proof` (MIXED) / `r176a_mixed_bridge'_proof` —
`r176a_extreme_transport_rowShape : RowShape @ExtremeTransportData` (RProof/ExtremeTransportUnits.lean). -/
theorem extreme_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ :=
  r176a_extreme_transport_rowShape n hn E e f g h3 h4e h4f h4g hE

end RProof
