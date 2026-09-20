#!/usr/bin/env python3
"""port_build_w6.py — build SM/CS7Units.lean, SM/CS7.lean, SM/ComparisonRows.lean from a PRUNED assembled corner file
(prune.py output: the dead sorried declarations already removed).  Rewordings are exact-text replacements (each asserted
to occur exactly once); the leaves and the tail are located by their frozen docstring/statement text.
Usage: python3 port_build_w6.py SRC OUTDIR [--time HH:MM] [--allow-sorry]"""
import argparse, pathlib, re, json, sys
ap = argparse.ArgumentParser(); ap.add_argument('src'); ap.add_argument('out'); ap.add_argument('--time', default='<HH:MM>')
ap.add_argument('--allow-sorry', action='store_true'); ap.add_argument('--srcname', default='work/drafts/corner/W6_Assembled.lean')
A = ap.parse_args(); T = A.time
txt = pathlib.Path(A.src).read_text()
HDR = f"-- Ported {T}Z 2026-09-19 from {A.srcname} by the pod executor (files prepared by the W6-GLUE assembler)"

# ---- 1. rewordings (exact text → text); every `sorry` prose mention and every BLACK-BOX docstring of a proved theorem ----
REW = [
 ("and the direction data) are stated as `s7q_`-prefixed black boxes with `sorry` (§S7QBoxes). -/",
  "and the direction data) were stated as `s7q_`-prefixed black boxes in wave 3 (§S7QBoxes); in wave 4 they are proved\n(`s7q_box_split`, `s7q_box_order`, `s7q_box_carriers`) or superseded by unit S1P's restatements. -/"),
 ("visits under `s7b_firstVisitQ`/`s7b_secondVisitQ`); its proof `w3_SlidingOrder_of_box := s7q_box_order` is sorry-free:",
  "visits under `s7b_firstVisitQ`/`s7b_secondVisitQ`); its proof `w3_SlidingOrder_of_box := s7q_box_order` is complete:"),
 ("/-- **Prop S2 PROVED**: `s7q_box_order` is discharged in the ROT block above (sorry-free). -/",
  "/-- **Prop S2 PROVED**: `s7q_box_order` is discharged in the ROT block above. -/"),
 ("**Black boxes** (`sorry`, geometric; stated exactly as consumed — see W3_F_REPORT.md §2):",
  "**Black boxes** (geometric; stated exactly as consumed — see W3_F_REPORT.md §2 — and PROVED in wave 4 by units FB1, FB2, FB3):"),
 ("/-! #### E. The black boxes (rule (3)): the three per-unit existence statements, `sorry` -/",
  "/-! #### E. The per-unit existence statements (rule (3)): B1 and B2 are superseded by the wave-4 F-aligned route (dropped at\nport); B3 `s7z_oneNewborn_exists` is proved by unit B3 -/"),
 ("closed, so F's residual identity `s7f_exists_law_residual` and B3's `s7z_oneNewborn_exists` are sorry-free.  Following",
  "closed, so F's residual identity `s7f_exists_law_residual` and B3's `s7z_oneNewborn_exists` are proved.  Following"),
 ("off every proved path.  The leaf keeps its `sorry` (merge rule); it closes as\n`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` once wave 5 lands. -/",
  "off every proved path (dropped at port).  The leaf closes as\n`w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)` (waves 5-7 prove `w4_box_returnedRows`). -/"),
 # BLACK BOX docstrings of proved theorems
 ("/-- **BLACK BOX (ROT (a)-(c) geometry, given RET + SPLIT)**: below a radius, for every row and every",
  "/-- **Prop S3 (ROT (a)-(c) geometry, given RET + SPLIT; PROVED in wave 4 through S1P's `s7u_box_carriers'`)**: below a radius, for every row and every"),
 ("/-- **Prop S3' (the restated carriers box; BLACK BOX for unit S3G)** = ROT's `s7q_box_carriers` with the transport",
  "/-- **Prop S3' (the restated carriers box, DISCHARGED by unit S3G)** = ROT's `s7q_box_carriers` with the transport"),
 ("/-- **BLACK BOX 1 (geometric; U110-B §2.2 in its bigon form, U_S7B_REPORT §2.2/§2.4).**  Below a radius,",
  "/-- **Box 1 (geometric; U110-B §2.2 in its bigon form, U_S7B_REPORT §2.2/§2.4; PROVED by unit FB1).**  Below a radius,"),
 ("/-- **BLACK BOX 2 (geometric; sm-4:434-447, the `ε = 0` two-newborn row).**  Below a radius, for",
  "/-- **Box 2 (geometric; sm-4:434-447, the `ε = 0` two-newborn row; PROVED by unit FB2).**  Below a radius, for"),
 ("/-- **BLACK BOX 3 (geometric; sm-4:418-421 \"Deleting their four visits identifies the complete smoothing",
  "/-- **Box 3 (geometric, PROVED by unit FB3; sm-4:418-421 \"Deleting their four visits identifies the complete smoothing"),
 ("/-- **BLACK BOX (this unit's own remaining content; NOT proved).**  Clearance of the carrier edges that lie",
  "/-- **Clearance of the local edges (PROVED by unit SITEC).**  Clearance of the carrier edges that lie"),
 ("(4) or containing them (then `h = j_s` by `geo_block_mark_eq`).  Estimate 300-450 lines (the `a`-edge case is\nthe long one). -/",
  "(4) or containing them (then `h = j_s` by `geo_block_mark_eq`). -/"),
 ("/-- **BLACK BOX (U110-A/B wall data; NOT proved here).**  At a bigon wall (`g.BigonAt M a`), below some",
  "/-- **The wall triangle data at a bigon wall (U110-A/B wall data; PROVED by unit SITEC).**  At a bigon wall (`g.BigonAt M a`), below some"),
 ("`VertexLocalData.visit_windows` / `InContactVisitWindow` (U_S7A_REPORT §1.7 `s7a_exists_sideLocal`).\nEstimate 300-500 lines on the accepted `vertex_sides`. -/",
  "`VertexLocalData.visit_windows` / `InContactVisitWindow` (U_S7A_REPORT §1.7 `s7a_exists_sideLocal`). -/"),
 ("/-- **BLACK BOX — unit J (cb:singleton) with unit C (the one-newborn selectors)** (sm-4:693-723,",
  "/-- **Prop B3 (PROVED by unit B3) — unit J (cb:singleton) with unit C (the one-newborn selectors)** (sm-4:693-723,"),
 ("/-- **BLACK BOX (unit W5-RT — the returned transport)**: below a radius, every eligible decomposition has",
  "/-- **The returned transport (ROW's Prop, PROVED at the wave-5 assembly from unit RT)**: below a radius, every eligible decomposition has"),
 ("`lift T₀` ↔ spectator carriers of `T₁ ⊕ T₂` with equal weights and coefficients).  Nothing below depends on\nthe body. -/",
  "`lift T₀` ↔ spectator carriers of `T₁ ⊕ T₂` with equal weights and coefficients). -/"),
 ("/-- **BLACK BOX (unit W5-RT or W5-BR — the contact-corner correspondence)**: below a radius, every eligible",
  "/-- **The contact-corner correspondence (ROW's Prop, PROVED by unit W6-COR)**: below a radius, every eligible"),
 ("/-- **BLACK BOX (unit W5-SITE — the contact carrier pair)**: below a radius, every eligible decomposition has",
  "/-- **The contact carrier pair (ROW's Prop, PROVED at the wave-5 assembly from unit SITE)**: below a radius, every eligible decomposition has"),
 ("/-- **BLACK BOX (wave 5: the per-eligible-decomposition instantiation of SITE + SITEH + BLOCK + J on the carriers\nof `lift T₀` / `T₀`, with FB3's transport off the contact carrier)**: Prop B2'.  `hF` is the floor of the two\nhalf contact carriers (`s7j_*_entry_at_halves`).  Nothing below depends on the body. -/",
  "/-- **Prop B2' (PROVED, waves 5-7: the per-eligible-decomposition instantiation of SITE + SITEH + BLOCK + J on the carriers\nof `lift T₀` / `T₀`, with FB3's transport off the contact carrier)**.  `hF` is the floor of the two\nhalf contact carriers (`s7j_*_entry_at_halves`). -/"),
]
CC_REW = ("/-- **BLACK BOX (consumed, rule 2 — wave-6 corner unit W6-COR / GLUE): the centre corner data below a radius**, for every\neligible decomposition (the same shape as `w5r_box_corners`; expected to be delivered by the same construction, read on\nthe centre with `s7a2_point_eq_evaluation` and `principalAngle_smul` at the two corners adjacent to the contact on `E_a`).\nNothing below depends on the body. -/",
  "/-- **The centre corner data below a radius (W6-ROT's consumed Prop, PROVED by unit W6-CC)**, for every\neligible decomposition (the same shape as `w5r_box_corners`, read on the centre). -/")
applied = []
for old, new in REW + ([CC_REW] if not A.allow_sorry else []):
    c = txt.count(old); assert c == 1, (c, old[:70]); txt = txt.replace(old, new); applied.append(old[:60])
L = txt.split('\n')
def find1(pred, start=0):
    hits = [i for i in range(start, len(L)) if pred(L[i])]; assert len(hits) == 1, (len(hits), pred); return hits[0]
# ---- 2. landmarks ----
i_imp = find1(lambda l: l == 'import SM.CornerChainUnits')
PRE = ['import SM.CornerChainUnits','import SM.CS7Sliding','import SM.BigonDeletion','import SM.CarrierFloorRows','','namespace SM','',
       'open Link Carrier','','attribute [local instance] Classical.propDecidable','','noncomputable section','','section VertexEdge','',
       'variable {n : ℕ} [NeZero n]','']
assert L[i_imp:i_imp+len(PRE)] == PRE, L[i_imp:i_imp+len(PRE)]
body0 = i_imp + len(PRE)
i_sd = find1(lambda l: l.startswith('/-- The sliding branch (sm-4:300-406)'))
i_st = find1(lambda l: l.startswith('theorem s7_sliding_law_at '))
assert i_st == i_sd + 3
i_se = i_st; 
while L[i_se] != '': i_se += 1          # first blank after the sliding leaf
assert L[i_se-1].startswith('  exact s7u_sliding_law_at_of'), L[i_se-1]
assert L[i_se+1] == '' , L[i_se+1]
i_bd = find1(lambda l: l.startswith('/-- The bigon branch (sm-4:407-874)'))
i_bt = find1(lambda l: l.startswith('theorem s7_bigon_law_at '))
i_bb = i_bt
while not L[i_bb].startswith('  sorry') and not L[i_bb].startswith('  exact w4_s7_bigon_law_at_of'): i_bb += 1
assert L[i_bb+1] == '' and L[i_bb+2] == '' and L[i_bb+3] == 'end VertexEdge', L[i_bb:i_bb+4]
assert L[i_bd-1] == '' and L[i_bd-2] == 'end W4Bigon', L[i_bd-2:i_bd]
i_ev = i_bb + 3
tail = L[i_ev:]                        # 'end VertexEdge' … 'end SM' (+ trailing '')
assert tail[-1] == '' and tail[-2] == 'end SM' and any(l == 'theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor' for l in tail)
CLOSURE = '  exact w4_s7_bigon_law_at_of hn g h h₁ h₂ hsing (w4_box_returnedRows hn g h h₁ h₂ hF)'
# ---- 3. modules ----
units = [HDR,
 "-- SM/CS7Units.lean — row 110 thm:C-S7, ALL unit material (waves 3-7: SPLIT, RET, ROT, S1P, S3G, F, FB1-FB3, SITE, SITEC, SITEH,",
 "-- BLOCK, J, K, B3, the w4_ bigon glue, RT, SITE, BR, ROW, the w5_ glue, CURL, COR, ROT, the w6_ glue, CC) VERBATIM from the",
 "-- assembled draft, minus the two branch leaves and the row theorems (SM/CS7.lean) and minus the superseded sorried",
 "-- declarations (dropped; see work/drafts/corner/port/CS7/PORT_REPORT.md).  Library material; no row theorem here."]
units += PRE + L[body0:i_sd] + L[i_se+2:i_bd] + ['end VertexEdge','','end','','end SM','']
cs7 = [HDR,
 "-- SM/CS7.lean — row 110 thm:C-S7: the two branch leaves `s7_sliding_law_at` (unit S1P's closure) and `s7_bigon_law_at`",
 "-- (the wave-4 glue on Prop B2' `w4_box_returnedRows`, proved in waves 5-7), `thm_C_S7_of`, `thm_C_S7_of_floor` and the",
 "-- row theorem `SM.thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` (FIXED name, axiom-policy.json).  Statements",
 "-- byte-identical to work/drafts/corner/W3_Skeleton.lean.",
 'import SM.CS7Units', ''] + PRE[5:] + L[i_sd:i_se] + [''] + L[i_bd:i_bb] + [CLOSURE] + ['',''] + tail
rows = [HDR,
 "-- SM/ComparisonRows.lean — rows 127 thm:comparison and 128 cor:C-inherits (FIXED names SM.thm_comparison, SM.cor_C_inherits):",
 "-- the comparison lane's `thm_comparison_of` / `cor_C_inherits_of` (SM/Comparison.lean, SM/CInherits.lean) at rows 110",
 "-- (`thm_C_S7`, SM/CS7.lean) and 112 (`thm_C_soft`, SM/CSoft.lean); statements as in work/drafts/comparison/Statements_FINAL.lean §5.",
 'import SM.CS7','import SM.CSoft','import SM.Comparison','import SM.CInherits','','namespace SM','',
 '/-- Row 127 thm:comparison (FIXED name; hyp:R explicit).  "Assume Hypothesis R.  Then C(P) = A(P) for',
 'every generic polygon P." -/',
 'theorem thm_comparison (hR : hyp_R) :',
 '    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),',
 '      cornerStateSum hn hP = amplitude P hP.1 hn :=',
 '  thm_comparison_of hR thm_C_S7 thm_C_soft','',
 '/-- Row 128 cor:C-inherits (FIXED name; hyp:R explicit). -/',
 'theorem cor_C_inherits (hR : hyp_R) : CInheritsData := cor_C_inherits_of hR thm_C_S7 thm_C_soft','',
 'end SM','']
out = pathlib.Path(A.out) / 'SM'; out.mkdir(parents=True, exist_ok=True)
man = {}
for name, lines in [('CS7Units', units), ('CS7', cs7), ('ComparisonRows', rows)]:
    t = '\n'.join(lines); (out / f'{name}.lean').write_text(t)
    bad = [k for k in ('sorry', '#print', '#eval', '#check', 'admit') if k in t]
    if bad and not A.allow_sorry: assert False, (name, bad)
    man[name] = {'lines': len(lines) - 1, 'forbidden_strings': bad}
man['rewordings'] = len(applied)
print(json.dumps(man, indent=1))
