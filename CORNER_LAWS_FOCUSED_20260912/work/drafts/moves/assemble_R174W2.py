#!/usr/bin/env python3
"""assemble_R174W2.py — row-174 wave-2 assembler (2026-09-15 ≈ 23:25 UTC / 7:25pm ET).

Inputs (read only):
  R174_Port_GenericSelectedUnits_draft.lean   the port draft (6847 lines)
  R174W2_ARCV.lean                            Route V unit = draft lines 1-6843 + 479 appended lines + trailer
  ../cvtail/Wave1_Assembled.lean              lines 2543-2550: the FIXED statement of RProof.generic_selected
Outputs:
  R174W2_Assembled.lean                       header + ARCV lines 10-7326 + the RProof row block
  port/R174/RProof/GenericSelectedUnits.lean  header + ARCV lines 10-7326 (verbatim; everything except the row theorem)
  port/R174/RProof/GenericSelected.lean       header + import RProof.GenericSelectedUnits + the RProof row block
"""
import os, re, sys, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
DRAFT = os.path.join(HERE, 'R174_Port_GenericSelectedUnits_draft.lean')
ARCV = os.path.join(HERE, 'R174W2_ARCV.lean')
WAVE1 = os.path.join(HERE, '..', 'cvtail', 'Wave1_Assembled.lean')

draft = open(DRAFT, encoding='utf-8').read().split('\n')
arcv = open(ARCV, encoding='utf-8').read().split('\n')
wave1 = open(WAVE1, encoding='utf-8').read().split('\n')

# sanity: ARCV = draft[0:6843] + appended + draft trailer; header lines 1-9 are `--` comments, 10-11 imports
assert draft[:6843] == arcv[:6843], "ARCV prefix differs from the draft"
assert all(l.startswith('--') for l in draft[:9]) and draft[9:11] == ['import SM.BigonDeletion', 'import RProof.RALedgers'], draft[:11]
assert arcv[-4:] == ['end', '', 'end SM.Link', ''] or arcv[-3:] == ['end', '', 'end SM.Link'], arcv[-5:]
body = arcv[9:]                      # lines 10.. of ARCV: imports + body + trailer
while body and body[-1] == '':
    body.pop()

# the FIXED statement: Wave1 lines 2543-2550 (1-based), the last one minus its ` by`
stmt = wave1[2542:2549]
assert stmt[0].startswith('theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)'), stmt[0]
assert stmt[-1].endswith(':= by'), stmt[-1]
stmt[-1] = stmt[-1][:-len(' by')]
assert wave1[2549].strip() == 'sor'+'ry', wave1[2549]  # the placeholder body we replace

for s in stmt:
    for bad in ('sorry', '#print', '#eval'):
        assert bad not in s

PRINTED = (
    "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit and an exterior\n"
    "independent support `Q`. Relabel the three local crossings so the exact local words are\n"
    "`P = a b A a c B b c C` (edges ab,bc), `E = b a A c a B c b C` (edge ac). Thus `b` is the degree-two\n"
    "vertex of the path, and `ac` is its complementary independent pair on `P`. If `T_nu(J)` denotes the\n"
    "complete X1 term of `Q union J` on side `nu`, absent rows being zero, then `T_E(b) = T_P(b) + T_P(ac)`\n"
    "(GSC). This is exactly the selected `b/ac` complementary-couple identity, with the opposite\n"
    "coorientation obtained by multiplying the equation by `-1`.")

ROW_DOC = ('/-- **Row 174 (ORDER 182), R:generic_selected** (FIXED name and statement;\n'
           'R_GENERIC_SELECTED_COUPLE_PROOF.md, Statement).  Printed obligation:\n"' + PRINTED + '"\n'
           'The side `P` is the two-edge side (`EdgeAB ∧ EdgeBC`, centre `b`), `E` the other side; the three\n'
           'branches are the fields of `GenericSelectedData` (RProof/X1Rows.lean).\n'
           '\n'
           'Proof: the RA ledger `gsc_generic_selected_of_moves` (RProof/RALedgers.lean) at the carrier floor\n'
           '`CV.carrierSlotFloor`, with the interface Prop `gsc_moves` realised by\n'
           '`SM.Link.r174_gsc_moves_of_arc_rec` from the arc-record identification\n'
           '`SM.Link.r174v_arc_rec_moves_proof : SM.Link.r174_arc_rec_moves` (RProof/GenericSelectedUnits.lean:\n'
           'site I-174, units HREC, CARRIERS, SITEIN, WALL, SMOOTH, the composition, and Route V — the visit data\n'
           '`ψ_A`, `ψ_B` of the two arcs of `x\'`).  Axioms: the standard three and the six literature interfaces\n'
           '(`SM.lit_homfly`, `SM.lit_homfly_descent`, `SM.lp_lm`, `SM.lp_lm_uniqueness`, `SM.ng_finite_word`,\n'
           '`SM.src_contact`); no placeholder. -/')

ROW_BLOCK = ['',
    '/-! ## Row 174 (ORDER 182) — R:generic_selected: the row theorem',
    '',
    'The FIXED name `RProof.generic_selected` with the FIXED statement (work/drafts/cvtail/Wave1_Assembled.lean',
    'lines 2543-2549, byte-identical), proved as `r174_generic_selected_of_arc_rec r174v_arc_rec_moves_proof`. -/',
    '',
    'namespace RProof',
    '',
    'open SM SM.GeoCarrier',
    '',
    'variable {n : ℕ} [NeZero n]',
    ''] + ROW_DOC.split('\n') + stmt + [
    '  SM.Link.r174_generic_selected_of_arc_rec SM.Link.r174v_arc_rec_moves_proof hn E e f g h3 h4e h4f h4g hE',
    '',
    'end RProof',
    '']

HDR_ASSEMBLED = [
 '-- R174W2_Assembled (assembler, row-174 wave 2, 2026-09-15 ≈ 23:25 UTC / 7:25pm ET): the row-174 material of',
 '-- R174_Port_GenericSelectedUnits_draft.lean (lines 10-6843 verbatim: Site_174 `s174_`, HREC `r174h_`, CARRIERS `r174c_`,',
 '-- SITEIN `r174x_`, WALL `r174w_`, SMOOTH `r174s_`, the composition `r174_`) + the wave-2 unit ARCV (R174W2_ARCV.lean lines',
 '-- 6844-7326 verbatim, prefix `r174v_`, Route V: the visit data `ψ_A`, `ψ_B` proving the ONE open Prop `r174_arc_rec_moves`)',
 '-- + the row theorem `RProof.generic_selected` (FIXED name and statement) := r174_generic_selected_of_arc_rec',
 '-- r174v_arc_rec_moves_proof.  The other wave-2 unit, R174W2_ARCR.lean (Route R, prefix `r174r_`, 597 lines), proves the same',
 '-- Prop independently and is kept as an independent check, not assembled.  Compile: `cd work/lean && lake env lean',
 '-- ../drafts/moves/R174W2_Assembled.lean`.  Axioms of RProof.generic_selected: propext, Classical.choice, Quot.sound,',
 '-- SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact (no placeholder).',
 '-- Details: R174W2_ASSEMBLY_REPORT.md.  Port layout: port/R174/RProof/{GenericSelectedUnits,GenericSelected}.lean.',
]
HDR_UNITS = [
 '-- Ported <HH:MM>Z 2026-09-16 from work/drafts/moves/R174W2_Assembled.lean lines 11-7327 (= R174_Port_GenericSelectedUnits_draft.lean',
 '-- lines 10-6843 + R174W2_ARCV.lean lines 6844-7326, verbatim) by the row-174 wave-2 assembler: the row-174 site and units',
 '-- (Site I-174 `s174_`; HREC `r174h_`; CARRIERS `r174c_`; SITEIN `r174x_`; WALL `r174w_`; SMOOTH `r174s_`; the composition',
 '-- `r174_` — `r174_arc_rec_moves`, `r174_gsc_moves_of_arc_rec`, `r174_generic_selected_of_arc_rec`; Route V `r174v_` —',
 '-- `r174v_arc_rec_moves_proof : r174_arc_rec_moves`, `r174v_gsc_moves : gsc_moves`), all in namespace SM.Link.  LIBRARY',
 '-- MATERIAL, no row theorem: the row theorem RProof.generic_selected is in RProof/GenericSelected.lean.  Body verbatim',
 '-- except this header (the draft\'s nine header comment lines replaced).  Every declaration is proved on the standard',
 '-- and literature axioms; `r174v_arc_rec_moves_proof` on the standard three alone; no placeholder anywhere.',
 '-- The unit docstrings\' phrase "Everything below is NEW (nothing above changed)" is the units\' own drafting note.',
]
HDR_ROW = [
 '-- Ported <HH:MM>Z 2026-09-16 from work/drafts/moves/R174W2_Assembled.lean lines 7328-7367 (the RProof row block, verbatim) by',
 '-- the row-174 wave-2 assembler: the row theorem RProof.generic_selected (row 174, R:generic_selected; FIXED name; statement',
 '-- byte-identical to work/drafts/cvtail/Wave1_Assembled.lean lines 2543-2549) := SM.Link.r174_generic_selected_of_arc_rec',
 '-- SM.Link.r174v_arc_rec_moves_proof (RProof/GenericSelectedUnits.lean).  Axioms: propext, Classical.choice, Quot.sound,',
 '-- SM.lit_homfly, SM.lit_homfly_descent, SM.lp_lm, SM.lp_lm_uniqueness, SM.ng_finite_word, SM.src_contact; no placeholder.',
]

assembled = HDR_ASSEMBLED + body + ROW_BLOCK
body_start = len(HDR_ASSEMBLED) + 1; body_end = len(HDR_ASSEMBLED) + len(body); row_start = body_end + 1; row_end = len(assembled) - 1
HDR_UNITS[0] = HDR_UNITS[0].replace('lines 11-7327', f'lines {body_start}-{body_end}')
HDR_ROW[0] = HDR_ROW[0].replace('lines 7328-7367', f'lines {row_start}-{row_end}')
print('body', body_start, body_end, 'row block', row_start, row_end)
units = HDR_UNITS + body + ['']
row = HDR_ROW + ['import RProof.GenericSelectedUnits'] + ROW_BLOCK

def write(path, lines):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    txt = '\n'.join(lines)
    if not txt.endswith('\n'):
        txt += '\n'
    open(path, 'w', encoding='utf-8').write(txt)
    print(path, len(txt.split('\n')) - 1, 'lines', hashlib.md5(txt.encode()).hexdigest())

write(os.path.join(HERE, 'R174W2_Assembled.lean'), assembled)
write(os.path.join(HERE, 'port', 'R174', 'RProof', 'GenericSelectedUnits.lean'), units)
write(os.path.join(HERE, 'port', 'R174', 'RProof', 'GenericSelected.lean'), row)
