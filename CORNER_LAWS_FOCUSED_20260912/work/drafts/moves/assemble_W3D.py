#!/usr/bin/env python3
"""Assemble W3D_Assembled.lean (row 177, wave 3d) = W3C_Assembled.lean + the three W3D unit blocks (RESPAR, RESID,
NONKINK) in dependency order, the assembler's connections (the residue closed, the operative chain rewired to the value
form of the site data), and the port-time statement edits of OPEN_ITEMS §A-18 (the superseded Wave-3b chain and every
remaining `sorry` deleted, the prose rewordings, the library copies dropped by importing) — all as exact, asserted
string operations.  Run in work/drafts/moves:   python3 assemble_W3D.py
Each unit file is first RECONSTRUCTED from the base and the extracted block (byte-identity asserted), so the blocks
are exactly the units' insertions and nothing else of the units is lost or invented."""
import re, sys, hashlib
DROP_LIB_COPIES = True   # (2)(d): import SM.CBProducts / CV.SingletonDi / SM.ZeroRotationSeed and drop the copies
def L(p): return open(p, encoding='utf-8').read().split('\n')
base, respar, resid, nonkink = L('W3C_Assembled.lean'), L('W3D_RESPAR.lean'), L('W3D_RESID.lean'), L('W3D_NONKINK.lean')

# ---- 1. the units' blocks, verified by reconstructing each unit file from the base ------------------------------
respar_block = respar[16427:17821]                    # RESPAR lines 16428..17821 (inserted after base 16427)
assert base[:16427] + respar_block + base[16427:] == respar, 'RESPAR is not base + one insertion after 16427'
assert respar_block[0].startswith('/-! ## RESPAR (unit W3D, `w3dp_`)')
assert resid[7] == 'import RProof.ExtremeTransportUnits'
resid_block = resid[16424:18974]                      # RESID lines 16425..18974 (replaces base 16424..16426)
assert base[:7] + [resid[7]] + base[7:16423] + resid_block + base[16426:] == resid, 'RESID is not base + import + block'
assert resid_block[1].startswith('/-! ## W3D unit RESID (`w3di_`)')
assert resid_block[-1] == 'theorem w3cx_outer_residue_data : w3cx_outer_residue := w3di_outer_residue_proof'
nonkink1 = nonkink[15508:17090]                       # NONKINK lines 15509..17090 (after base 15508, before `end W3BI_REAL`)
nonkink2 = nonkink[18517:18579]                       # NONKINK lines 18518..18579 (after base 16935, before `end W3CK_Chain`)
assert base[:15508] + nonkink1 + base[15508:16935] + nonkink2 + base[16935:] == nonkink, 'NONKINK is not base + two insertions'
assert nonkink1[0] == '' and nonkink1[1].startswith('/-! ## UNIT NONKINK (W3D, prefix `w3dk_`)')
nk_copies = nonkink[18524:18570]                      # the two value-form copies of block 2 (lines 18525..18570)
assert nk_copies[0].startswith('/-- (W3D NONKINK) copy of `w3ck_rii_after_smoothing_weak_occ`')
assert nk_copies[-1] == '      three_components := h3c }⟩'
assert base[16423] == '/-- the residue asserted (OPEN body; W3C_ASSEMBLY_REPORT.md §3) -/'
assert base[16425] == '  sorry' and base[15507] == '' and base[15508] == 'end W3BI_REAL'

# ---- 2. the mechanical merge, in base coordinates, bottom-up ----------------------------------------------------
out = base[:]
out[16423:16426] = respar_block + resid_block[1:]      # W3CK_Outer: RESPAR (parity) then RESID (identification + leaf); RESID's leading blank dropped (RESPAR ends with two)
out[15508:15508] = nonkink1                            # W3BI_REAL: NONKINK steps 1-7 before `end W3BI_REAL`
imports = ['import RProof.ExtremeTransportUnits'] + (['import SM.CBProducts', 'import CV.SingletonDi', 'import SM.ZeroRotationSeed'] if DROP_LIB_COPIES else [])
out[7:7] = imports
text = '\n'.join(out)
print(f'merged: {len(out)} lines (base {len(base)}, RESPAR +{len(respar_block)}, RESID +{len(resid_block)} -3, NONKINK +{len(nonkink1)}, imports +{len(imports)})')

# ---- helpers ------------------------------------------------------------------------------------------------------
def replace_once(t, old, new, note):
    n = t.count(old); assert n == 1, (note, n); print(f'  connected: {note}'); return t.replace(old, new)
deleted_names = []
def cut(t, start, end, expect, note):
    """remove [start, end) — both markers unique; the region must declare exactly `expect`"""
    assert t.count(start) == 1, (note, 'start marker count', t.count(start))
    assert t.count(end) == 1, (note, 'end marker count', t.count(end))
    i = t.index(start); j = t.index(end); assert i < j, note
    region = t[i:j]
    decls = re.findall(r'^(?:theorem|def|structure|lemma|abbrev|instance) ([^\s(:{\[]+)', region, re.M)
    assert decls == expect, (note, decls)
    deleted_names.extend(decls)
    print(f'  deleted: {note} ({region.count(chr(10))} lines: {", ".join(decls)})')
    return t[:i] + t[j:]

# ---- 3. the assembler's connections --------------------------------------------------------------------------------
# (a) the PARITY clause: RESID's black box `w3di_parity_data : w3di_parity` := RESPAR's proof (the two Props are the
#     residue's binders with the parity conclusion, alpha-equivalent: `_hQi'`/`_hS'` vs `hQi'`/`hS'`)
text = replace_once(text,
"""/-- the parity black box asserted (OPEN body — unit RESPAR) -/
theorem w3di_parity_data : w3di_parity := by
  sorry""",
"""/-- **the parity clause, PROVED** (W3D assembler): unit RESPAR's `w3dp_parity_at_proof` — `w3di_parity` and
`w3dp_parity_at` are the residue's binders with the parity conclusion `#w3cb_mixedSet Q' (Q' ∪ T') q₀' = 2Λ`, identical
up to binder names, so the proof term is accepted as is. -/
theorem w3di_parity_data : w3di_parity := w3dp_parity_at_proof""", 'parity: w3di_parity_data := w3dp_parity_at_proof')
# (b) the residue leaf's docstring (body already `w3di_outer_residue_proof`, RESID)
text = replace_once(text,
"""/-- the residue asserted (body: unit RESID's `w3di_outer_residue_proof`, which carries RESPAR's parity black box
`w3di_parity_data`; W3C_ASSEMBLY_REPORT.md §3, W3D_RESID_REPORT.md) -/
theorem w3cx_outer_residue_data : w3cx_outer_residue := w3di_outer_residue_proof""",
"""/-- **the OUTER residue, PROVED** (W3D assembler): unit RESID's `w3di_outer_residue_proof` — the identification clause
`w3di_ident_at` at the parity's `Λ` — with unit RESPAR's parity clause `w3dp_parity_at_proof` wired in through
`w3di_parity_data` (W3D_RESPAR_REPORT.md, W3D_RESID_REPORT.md, W3D_ASSEMBLY_REPORT.md §1). -/
theorem w3cx_outer_residue_data : w3cx_outer_residue := w3di_outer_residue_proof""", 'residue leaf docstring')
# (c) the operative chain: the two `w3ck_` conditionals on the false Prop `w3bi_rii_sites` are replaced by NONKINK's
#     value-form copies, and `w3ck_esc_interface_ext_occ_holds` is rewired to `w3dk_rii_value_sites_data`
start = '/-- **(b) the realiser of (6) in the weak form WITH occurrence-compatible record clauses**'
endl = '  w3ck_esc_interface_ext_of w3ck_esc_outer_occ_holds w3bi_rii_sites_data'
assert text.count(start) == 1 and text.count(endl) == 1
i = text.index(start); j = text.index(endl) + len(endl)
region = text[i:j]
assert re.findall(r'^theorem ([^\s(:{\[]+)', region, re.M) == ['w3ck_rii_after_smoothing_weak_occ', 'w3ck_esc_interface_ext_of', 'w3ck_esc_interface_ext_occ_holds']
deleted_names += ['w3ck_rii_after_smoothing_weak_occ', 'w3ck_esc_interface_ext_of']
new_chain = """/-! ### (W3D assembler) the operative chain through the VALUE form of the site data (unit NONKINK, step 8).  The site
input of the record-clause interface is `w3dk_rii_value_sites_data` — the HOMFLY equality of the two switched smoothings
at every configuration, kink case included (W3D_NONKINK_REPORT.md) — in place of the Wave-3c site box
`w3bi_rii_sites_data`, whose non-kink leaf was false as stated; that box and the superseded Wave-3b chain were removed
(W3D_ASSEMBLY_REPORT.md §2). -/

""" + '\n'.join(nk_copies) + """

/-- the record-clause interface, both inputs PROVED: the OUTER data `w3ck_esc_outer_occ_holds` (SPLITA / SPLITB / SPLITC /
KNOT, with the residue closed by RESPAR + RESID) and the value form of the site data `w3dk_rii_value_sites_data` (NONKINK) -/
theorem w3ck_esc_interface_ext_occ_holds : w3ck_esc_interface_ext_occ :=
  w3dk_esc_interface_ext_of w3ck_esc_outer_occ_holds w3dk_rii_value_sites_data"""
text = text[:i] + new_chain + text[j:]
print('  connected: W3CK_Chain rewired to the value form (w3dk_ copies in, w3ck_ conditionals on w3bi_rii_sites out)')
# (d) the terminal theorem's docstring
text = replace_once(text,
"""/-- **Row 177 (R:extreme_selected) in the fixed row shape, through the record-clause chain**: the placeholder
axiom only through `w3ck_split_ident_data` (SPLITB's split + this unit's open identification) and
`w3bi_rii_sites_data` (the site data). -/
theorem w3ck_extreme_selected : RowShape @ExtremeSelectedData :=""",
"""/-- **Row 177 (R:extreme_selected) in the fixed row shape, through the record-clause chain** (W3D assembler): every
input PROVED — the OUTER data with its residue closed by units RESPAR + RESID, the value form of the site data by unit
NONKINK, the replayed ledger and `CV.carrierSlotFloor` (row 155); registered axioms only (W3D_ASSEMBLY_REPORT.md §3). -/
theorem w3ck_extreme_selected : RowShape @ExtremeSelectedData :=""", 'w3ck_extreme_selected docstring')

# ---- 4. §A-18 item 3: the two prose mentions of the word (base lines 7856, 14706) ----------------------------------
text = replace_once(text,
"frozen sub-leaves are reduced to it (their remaining `sorry` is the hypothesis `hk5` alone).  Tools: the affine",
"frozen sub-leaves are reduced to it (their remaining obligation is the hypothesis `hk5` alone).  Tools: the affine", 'prose reword (unit G header)')
text = replace_once(text,
"  (one `sorry`, `w3cb_split_core_data`; `w3cb_split_geometry_data` is then a theorem).",
"  (`w3cb_split_core_data`, left open by this unit and since proved from the residue; `w3cb_split_geometry_data` is then a theorem).", 'prose reword (SPLITB header)')
# the W3BI_REAL header describes the chain as it now stands
text = replace_once(text,
"""(a) `w3bi_switch_riii` realises `esc_MoveData.switch_riii` from `w3e_strong_case_sw` (PROVED modulo unit E);
(b) `w3bi_rii_after_smoothing_weak` realises (6) in the weak form `esc_rii_after_smoothing_weak` from the library
smoothings and the site box `w3bi_rii_sites`, itself reduced to the site data `w3bi_site_data` (β1′, OPEN: units G +
D4/D5, consuming `w3g_*` and the corrected `w3bi_*_switch_z` forms by name) and the wall data `w3bi_wall_data` (β2,
PROVED: `w3bi_wallEquiv`, `w3bi_wall_data_lift`, `w3bi_adjacent_lift_proof`), glued by `w3bi_hrec_general` (the
`ST/ST` case is `w3h_hrec`); (c) `w3bi_esc_interface_ext` (the interface with `GenericTableData`, `AV_EventRadius`
and the weak move data `w3bi_esc_MoveDataWeak`), the replayed `w3bi_esc_contact_identity` / `w3bi_esc_couple` /
`w3bi_esc_ledger`, and `w3bi_extreme_selected : RowShape @ExtremeSelectedData`.  Black boxes: `w3bi_esc_outer_data`
(the outer interface data, not 177-(4)/(6)), `w3bi_site_data_data`, the three non-`ST/ST` cases of `w3bi_hrec_general`,
the two `switch_z` statements.  Report: `W3B_REAL_REPORT.md`. -/""",
"""(a) `w3bi_switch_riii` realises `esc_MoveData.switch_riii` from `w3e_strong_case_sw` (PROVED); (b) the site data β1′
`w3bi_site_data` (PROVED by unit SITE, `w3bi_site_data_data`) and the wall data β2 `w3bi_wall_data` (PROVED:
`w3bi_wallEquiv`, `w3bi_wall_data_lift`, `w3bi_adjacent_lift_proof`), glued by `w3bi_hrec_general` (the `ST/ST` case is
`w3h_hrec`) — consumed, in the value form of unit NONKINK (`w3dk_rii_value_sites_data`), by the record-clause chain of
unit KNOT (`w3ck_esc_interface_ext_occ`, `w3ck_esc_outer_occ`, `w3ck_esc_ledger`, `w3ck_extreme_selected`).
(W3D assembler) The Wave-3b interface Props of this unit (`w3bi_esc_interface_ext`, `w3bi_esc_outer`, `w3bi_rii_sites`,
`w3bi_bigon_pair`, the weak move data `w3bi_esc_MoveDataWeak` with `w3bi_knot_after_two` / `w3bi_three_components`), its
replayed ledger and its terminal `w3bi_extreme_selected` were superseded by that chain and removed here
(OPEN_ITEMS §A-18 item 2, W3D_ASSEMBLY_REPORT.md §2).  Report: `W3B_REAL_REPORT.md`. -/""", 'W3BI_REAL header')

# ---- 5. §A-18 item 2 + the task's (2)(b): delete the superseded Wave-3b chain and every remaining `sorry` -----------
text = cut(text, '/-- **(b) sub-leaf (OPTIONAL — not on the assembly\'s path):**', 'end W3Switch',
           ['w3b_reparam_switch'], 'w3b_reparam_switch (optional, unused, sorry)')
text = cut(text, '/-! ### The weak move data, the extended interface (F-177-2 as a replay, decision D2 / D-RM-5) and the two\nblack boxes of this unit -/',
           '/-! ### W3C SPLITA — `esc_FullSplitData` fields `touching_iff`, `distinct`, `central_no_piece`, `central_rot` (prefix `w3ca_`)',
           ['w3bi_knot_after_two', 'w3bi_three_components', 'w3bi_esc_MoveDataWeak', 'w3bi_esc_interface_ext', 'w3bi_esc_outer'],
           'Wave-3b interface Props (superseded by w3ck_esc_MoveDataOcc / w3ck_esc_interface_ext_occ / w3ck_esc_outer_occ)')
text = cut(text, '/-- the black box asserted (open body): NOT this unit\'s content (units E/G/H realise (4) and (6) only). -/',
           '/-! ### W3CC — unit SPLITC: `esc_FullSplitData.outer_alternative` and `.uniform` from the corner ledger',
           ['w3bi_esc_outer_data'], 'w3bi_esc_outer_data (frozen OUTER leaf, not provable as stated, sorry)')
text = cut(text, '/-- **BLACK BOX (units G + H at the 177 site, D4–D6): the two `j = 2` bigon sites on the switched',
           '/-! ### Unit BIGON (`w3cz_`): the switch-at-`z₀` bigon forms.',
           ['w3bi_rii_sites', 'w3bi_bigon_pair'], 'w3bi_rii_sites / w3bi_bigon_pair (false as stated in the kink configuration)')
text = cut(text, '/-- **BLACK BOX (SITE, OPEN — rule (4), reported)**: at every 177 configuration the lift crossing over `x_ef` is',
           'section W3BI_Lift',
           ['w3cs_not_kink_site', 'w3cs_not_kink_site_data', 'w3bi_bigon_pair_of', 'w3bi_bigon_pair_data'],
           'w3cs_not_kink_site(_data) (false as stated, sorry) and its two consumers')
text = cut(text, '/-- **The (6) site black box from β1 + β2 + the generalised record lemma** (PROVED glue): distinctness of',
           '/-! ### W3C unit SPLITB — `esc_FullSplitData.writhe` (17) and `.mixed` (ESC §4), the SPLITB half of the',
           ['w3bi_rii_sites_of', 'w3bi_rii_sites_data', 'w3bi_rii_after_smoothing_weak', 'w3bi_esc_interface_ext_of',
            'w3bi_esc_interface_ext_holds', 'w3bi_esc_contact_identity', 'w3bi_esc_couple', 'w3bi_esc_ledger',
            'w3bi_extreme_selected', 'w3bi_extreme_selected_leaf'],
           'the Wave-3b site chain, the replayed Wave-3b ledger and w3bi_extreme_selected(_leaf)')

# ---- 6. §A-18 (c) of §7: the library copies, dropped by importing --------------------------------------------------
renames = []
if DROP_LIB_COPIES:
    text = cut(text, '/-- `w3bh_` copy of `w3bh_restrictCrossings_iso_of_recordIso` (SM/CBProducts.lean:1358; that module is not',
               '/-- `w3bh_` helper: `ρ.pair u ≠ a ↔ u ≠ b` when `ρ.pair a = b` (and symmetrically). -/',
               ['w3bh_restrictCrossings_iso_of_recordIso'], 'copy of SM.CB.restrictCrossings_iso_of_recordIso')
    text = cut(text, 'omit [NeZero n] in\n/-- `insert` does not depend on the `DecidableEq` instance (the bridge between the file\'s global instance and',
               'theorem w3cb_union_triangle_eq {e f g : ZMod n}', ['w3cb_insert_eq'], 'copy of CV.cvt165s_insert_eq')
    text = cut(text, '/-- `principalAngle (-u) (-v) = principalAngle u v` (SM/ZeroRotationSeed.lean\'s `principalAngle_neg_neg`,',
               '/-! #### C1. Corner marks, mark turns, corner sets (U-SPLIT\'s `cvt165s_` rotation lane, copied) -/',
               ['w3cc_principalAngle_neg_neg', 'w3cc_principalAngle_swap'], 'copies of SM.principalAngle_neg_neg / principalAngle_swap')
    text = cut(text, '/-- lem:uniformrot at a signed pattern: the rotation lies on the ray of `τ` (U-SPLIT\'s `cvt165s_rot_ray`). -/',
               '/-- `τ · rot(L) ≥ 1` at a signed pattern of sign `τ ≠ 0`. -/',
               ['w3cc_rot_ray', 'w3cc_uniformOrOneDissent_of_pattern'], 'copies of CV.cvt165s_rot_ray / cvt165s_uniformOrOneDissent_of_pattern')
    renames = [('w3bh_restrictCrossings_iso_of_recordIso', 'CB.restrictCrossings_iso_of_recordIso'),
               ('w3cb_insert_eq', 'CV.cvt165s_insert_eq'),
               ('w3cc_principalAngle_swap', 'principalAngle_swap'),
               ('w3cc_rot_ray', 'CV.cvt165s_rot_ray'),
               ('w3cc_uniformOrOneDissent_of_pattern', 'CV.cvt165s_uniformOrOneDissent_of_pattern')]
    for old, new in renames:
        n = len(re.findall(r'\b' + old + r'\b', text))
        text = re.sub(r'\b' + old + r'\b', new, text)
        print(f'  renamed: {old} -> {new} ({n} occurrences)')
        deleted_names.remove(old) if old in deleted_names else None

# ---- 7. tidy and checks -----------------------------------------------------------------------------------------------
# (no global blank-line normalisation: the file stays byte-identical to the base outside the listed edits)
code = re.sub(r'/-[-!]?.*?-/', '', text, flags=re.S)          # strip block comments / docstrings
code = re.sub(r'--[^\n]*', '', code)                           # and line comments
for nm in deleted_names:
    hits = [m.start() for m in re.finditer(r'\b' + re.escape(nm) + r'\b', code)]
    assert not hits, f'deleted name {nm} still referenced in code ({len(hits)}x)'
sorries = re.findall(r'\bsorry\b', text)
print(f'checks: word `sorry` {len(sorries)}x; `#print` {text.count("#print")}x; `#eval` {text.count("#eval")}x; `axiom ` decls {len(re.findall(r"^axiom ", text, re.M))}')
lines = text.split('\n')
decls = re.findall(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*(?:theorem|lemma|def|abbrev|structure|instance|inductive|class|opaque)\s+([^\s:({\[]+)', text, re.M)
open('W3D_Assembled.lean', 'w', encoding='utf-8').write(text)
print(f'W3D_Assembled.lean: {len(lines) - (1 if lines[-1] == "" else 0)} lines, {len(decls)} declarations, sha256 {hashlib.sha256(text.encode()).hexdigest()[:16]}…')
