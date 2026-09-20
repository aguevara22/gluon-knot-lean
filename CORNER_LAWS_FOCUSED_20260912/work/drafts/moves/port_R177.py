#!/usr/bin/env python3
"""Lay out the row-177 port from W3D_Assembled.lean (W3C_ASSEMBLY_REPORT.md §7):
  port/R177/RProof/GenericTransportSw.lean   = assembled header + the original 7 imports + everything up to (not incl.)
                                               the `## 5. Row 177 (6)` header (the trans-free copy over `G11_ConfigSw`,
                                               W3Switch, W3E, `esc_switch_riii_of_chain`), closed with `end / end SM.Link`
  port/R177/RProof/ExtremeSelectedUnits.lean = header + imports + module docstring + `namespace SM.Link / open SM /
                                               noncomputable section` + the rest of the assembled file verbatim
  port/R177/RProof/ExtremeSelected.lean      = the row theorem `RProof.extreme_selected` (FIXED name, FIXED statement)
  port/R177/RProof/R177Probe.lean            = the probe (NOT for landing: `#print axioms`, `#check`)
Run in work/drafts/moves:  python3 port_R177.py"""
import os, re, hashlib
A = open('W3D_Assembled.lean', encoding='utf-8').read().split('\n')
assert A[:7] == ['import SM.Smoothing', 'import SM.MarkedProducts', 'import SM.SingleCrossing', 'import CV.FullTwist',
                 'import RProof.GenericTransport', 'import SM.BigonDeletion', 'import RProof.RALedgers']
assert A[7:11] == ['import RProof.ExtremeTransportUnits', 'import SM.CBProducts', 'import CV.SingletonDi', 'import SM.ZeroRotationSeed']
split = [i for i, l in enumerate(A) if l.startswith('/-! ## 5. Row 177 (6): the two `j = 2` bigon sites on smoothing outputs')]
assert len(split) == 1; split = split[0]
assert A[-4:] == ['end', '', 'end SM.Link', '']
assert A[37] == 'namespace SM.Link' and A[39] == 'open SM' and A[41] == 'noncomputable section' and A[11] == ''
os.makedirs('port/R177/RProof', exist_ok=True)
def md5(s): return hashlib.md5(s.encode()).hexdigest()
def write(path, text):
    assert 'sorry' not in text and '#print' not in text and '#eval' not in text or path.endswith('R177Probe.lean'), path
    open(path, 'w', encoding='utf-8').write(text)
    print(f'{path}: {text.count(chr(10))} lines, md5 {md5(text)}')

# ---- 1. RProof/GenericTransportSw.lean -------------------------------------------------------------------------------
body1 = A[:7] + A[11:split]
while body1[-1] == '': body1.pop()
last1 = 11 + len(body1) - 7            # 1-based number of the last assembled line kept (trailing blank lines dropped)
h1 = f"""-- Ported <HH:MM>Z 2026-09-19 from work/drafts/moves/W3D_Assembled.lean lines 1-7, 12-{last1} (the G11 core on a
-- SWITCHED positive diagram: the trans-free copy `G11_ConfigSw` / `G11_ParamsSw` over the accepted `RProof.G11_Params`
-- proofs, the switch transport `w3b_`, D8′/E′ `w3c_`/`w3d_`, the row-level assembly `w3e_strong_case_sw`, and the row 177 (4)
-- realiser `esc_switch_riii_of_chain`) by the pod executor (files prepared by the row-177 wave-3d assembler,
-- W3D_ASSEMBLY_REPORT.md).  Body verbatim except this header and the closing `end` / `end SM.Link` (the assembled file's
-- `## 5`-onward material is RProof/ExtremeSelectedUnits.lean).  The five FROZEN blocks (`G11_ConfigSw`, its namespace,
-- `G11_core_sw_statement`, the statement of `G11_core_sw`, `esc_switch_riii_of_chain`) are byte-identical to
-- work/drafts/moves/Port_GenericTransportSw_draft.lean (check_W3_identity.py).  No placeholder; no unproved declaration.
-- Axioms of `G11_core_sw`, `w3e_strong_case_sw`, `esc_switch_riii_of_chain`: propext, Classical.choice, Quot.sound,
-- SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness (W3D_AXIOMS.log)."""
m1 = h1 + '\n' + '\n'.join(body1) + '\n\nend\n\nend SM.Link\n'
write('port/R177/RProof/GenericTransportSw.lean', m1)

# ---- 2. RProof/ExtremeSelectedUnits.lean -----------------------------------------------------------------------------
h2 = f"""-- Ported <HH:MM>Z 2026-09-19 from work/drafts/moves/W3D_Assembled.lean lines {split + 1}-{len(A) - 1} (row 177 (6) and the
-- realisers: units E/G/H (`w3g_`, `w3h_`, `w3bg_`, `w3bh_`), REAL (`w3bi_`: `w3bi_switch_riii`, the site data β1′, the wall
-- data β2, `w3bi_hrec_general`), SPLITA (`w3ca_`), SPLITC (`w3cc_`), BIGON (`w3cz_`), SITE (`w3cs_`), SPLITB (`w3cb_`),
-- NONKINK (`w3dk_`: the flat subdivision and the value form of the site data), KNOT (`w3ck_`: the record-clause chain),
-- RESPAR (`w3dp_`: the parity clause), RESID (`w3di_`: the identification clause), the assembler's `w3cx_` (the sign table,
-- the OUTER residue) and the terminal `w3ck_extreme_selected : RowShape @ExtremeSelectedData`) by the pod executor (files
-- prepared by the row-177 wave-3d assembler, W3D_ASSEMBLY_REPORT.md).  Body verbatim except this header, the import block
-- and the opening `namespace SM.Link / open SM / noncomputable section` (the assembled file's lines 1-{split} are
-- RProof/GenericTransportSw.lean).  No placeholder; no unproved declaration; no interface Prop asserted.
-- Axioms of `w3ck_extreme_selected`: propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent,
-- SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact (W3D_AXIOMS.log; the registered nine, no placeholder axiom)."""
doc2 = """/-! # Row 177 (R:extreme_selected): the units and the row in the fixed shape

Everything below is the row-177 material of `work/drafts/moves/W3D_Assembled.lean` from its `## 5` header on, verbatim
(prefixes by unit: `w3g_`/`w3h_`/`w3bg_`/`w3bh_` the `j = 2` bigon sites and the reduced-smoothed-record lemma, `w3bi_` the
realisers and the site/wall data, `w3ca_` SPLITA, `w3cc_` SPLITC, `w3cz_` BIGON, `w3cs_` SITE, `w3cb_` SPLITB, `w3dk_`
NONKINK, `w3ck_` KNOT, `w3dp_` RESPAR, `w3di_` RESID, `w3cx_` the assembler).  The terminal theorem is
`w3ck_extreme_selected : RowShape @ExtremeSelectedData`, instantiated as `RProof.extreme_selected` in
RProof/ExtremeSelected.lean.  The switched G11 core it consumes is RProof/GenericTransportSw.lean. -/"""
m2 = h2 + '\n' + '\n'.join(['import RProof.GenericTransportSw', 'import RProof.ExtremeTransportUnits', 'import SM.CBProducts',
      'import CV.SingletonDi', 'import SM.ZeroRotationSeed', '', doc2, '', 'namespace SM.Link', '', 'open SM', '',
      'noncomputable section', '', '']) + '\n'.join(A[split:])
write('port/R177/RProof/ExtremeSelectedUnits.lean', m2)
m1l = m1.split('\n'); m2l = m2.split('\n')
print(f'  module 1: header 1-10, imports 11-17 (= assembled 1-7), body 18-{10 + len(body1)} (= assembled 12-{last1}), closing {11 + len(body1)}-{len(m1l) - 1}')
i2 = m2l.index('noncomputable section') + 2
assert m2l[i2:] == A[split:]
print(f'  module 2: header 1-11, imports 12-16, docstring 18-{i2 - 7}, frame {i2 - 5}/{i2 - 3}/{i2 - 1}, body {i2 + 1}-{len(m2l) - 1} (= assembled {split + 1}-{len(A) - 1}, {len(A) - 1 - split} lines)')

# ---- 3. RProof/ExtremeSelected.lean ----------------------------------------------------------------------------------
sib = open('../../lean/RProof/ExtremeTransport.lean', encoding='utf-8').read().split('\n')[38:45]
assert sib[0].startswith('theorem extreme_transport (hn : 3 ≤ n)') and sib[-1].endswith('ExtremeTransportData hn E e f g δ :=')
stmt = [l.replace('extreme_transport', 'extreme_selected').replace('ExtremeTransportData', 'ExtremeSelectedData') for l in sib]
fixed = open('../cvtail/Statements_FINAL.lean', encoding='utf-8').read().split('\n')[802:809]
assert fixed[-1].endswith(':= by'); fixed[-1] = fixed[-1][:-3]
assert stmt == fixed, ('fixed statement mismatch', stmt, fixed)
h3 = """-- Ported <HH:MM>Z 2026-09-19 by the pod executor (file prepared by the row-177 wave-3d assembler, W3D_ASSEMBLY_REPORT.md):
-- the row theorem RProof.extreme_selected (row 177, R:extreme_selected; FIXED name; statement byte-identical to
-- work/drafts/cvtail/Statements_FINAL.lean lines 803-809 and to RProof/ExtremeTransport.lean lines 39-45 with
-- ExtremeTransportData replaced by ExtremeSelectedData, = RowShape @ExtremeSelectedData instantiated)
-- := SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE (RProof/ExtremeSelectedUnits.lean).
-- Axioms: propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness,
-- SM.ng_finite_word, SM.src_contact; no placeholder."""
doc3 = """/-! ## Row 177 (ORDER 174) — R:extreme_selected: the row theorem

The FIXED name `RProof.extreme_selected` with the FIXED statement (work/drafts/cvtail/Statements_FINAL.lean lines 803–809,
byte-identical; the binder form of the accepted siblings `generic_transport`, `generic_selected`, `extreme_pair_zero`,
`extreme_transport`, of which `RowShape @ExtremeSelectedData` (RProof/RALedgers.lean) is the fixed shape), proved as
`SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE`. -/"""
row_doc = """/-- **Row 177 (ORDER 174), R:extreme_selected** (FIXED name and statement; R_EXTREME_SELECTED_COUPLE_PROOF.md,
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
identification) — `w3ck_extreme_selected : RowShape @ExtremeSelectedData` (RProof/ExtremeSelectedUnits.lean). -/"""
m3 = '\n'.join([h3, 'import RProof.ExtremeSelectedUnits', '', doc3, '', 'namespace RProof', '', 'open SM SM.GeoCarrier', '',
      'variable {n : ℕ} [NeZero n]', '', row_doc] + stmt + ['  SM.Link.w3ck_extreme_selected n hn E e f g h3 h4e h4f h4g hE', '', 'end RProof', ''])
write('port/R177/RProof/ExtremeSelected.lean', m3)
open('/workspace/scratch/claude-0/-workspace-repos-lean/d4284a43-f199-4eff-82e0-1573731546fc/scratchpad/w3d/R177Probe.lean', 'w', encoding='utf-8').write('\n'.join(['import RProof.ExtremeSelected', '',
  '#print axioms RProof.extreme_selected', '#print axioms SM.Link.w3ck_extreme_selected', '#print axioms SM.Link.w3cx_outer_residue_data',
  '#print axioms SM.Link.w3dp_parity_at_proof', '#print axioms SM.Link.w3di_ident_at', '#print axioms SM.Link.w3dk_rii_value_sites_data',
  '#print axioms SM.Link.G11_core_sw', '#check @RProof.extreme_selected', '']))
print('probe written (not for landing)')
