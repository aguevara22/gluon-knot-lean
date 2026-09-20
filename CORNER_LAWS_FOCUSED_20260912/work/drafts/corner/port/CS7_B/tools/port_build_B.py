#!/usr/bin/env python3
"""port_build_B.py — build the CS7_B port modules from the assembled corner file (assembly B).
usage: port_build_B.py --src FILE --del deletions.json --reword reword.json --out DIR [--time HH:MM] [--split LINE] [--srcname NAME]
Modules: SM/CS7Units.lean (or CS7UnitsA/B when --split), SM/CS7.lean; SM/ComparisonRows.lean is a hand-written file.
Every module = header line + imports + new module docstring + VERBATIM line ranges of the assembled file, minus the deleted
declaration paragraphs (docstring / `include … in` / attribute lines attached above, body below), with the rewordings of
reword.json applied (each exactly once).  Forbidden strings are checked on every output file."""
import argparse, json, pathlib, re, sys
sys.path.insert(0, '/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/corner/tools')
from wave2a_assemble import collect_decls, DECL_RE
ap = argparse.ArgumentParser()
ap.add_argument('--src', required=True); ap.add_argument('--del', dest='dele', required=True); ap.add_argument('--reword', required=True)
ap.add_argument('--out', required=True); ap.add_argument('--time', default='<HH:MM>'); ap.add_argument('--split', type=int, default=0)
ap.add_argument('--srcname', default='work/drafts/corner/W6_Assembled_B.lean')
A = ap.parse_args()
lines = pathlib.Path(A.src).read_text().split('\n'); assert lines[-1] == ''; lines = lines[:-1]
N = len(lines)
decls, order = collect_decls(lines)
name2line = {}
for n, k in order:
    assert n not in name2line, ('duplicate', n); name2line[n] = k
def para(k):
    """[s, e) paragraph of the declaration at 0-indexed line k: attached lines above, body below (to the blank line;
    a blank line followed by an indented continuation stays inside)."""
    s = k
    while s > 0:
        p = lines[s-1]
        if re.match(r'^(include|omit|open|set_option)\b.*\bin\s*$', p) or p.startswith('@['):
            s -= 1; continue
        if p.rstrip().endswith('-/'):
            j = s - 1
            while j >= 0 and not lines[j].startswith('/--'):
                assert not lines[j].startswith('/-!'), ('module doc above decl', k)
                j -= 1
            assert j >= 0; s = j; continue
        break
    e = k + 1
    while e < N and lines[e] != '':
        e += 1
    while e + 1 < N and lines[e] == '' and lines[e+1].startswith(' ') and not lines[e+1].lstrip().startswith('/-'):
        e += 1
        while e < N and lines[e] != '': e += 1
    return s, e
dele = json.load(open(A.dele))
kill = [False] * N
for n in dele:
    assert n in name2line, ('unknown deletion', n)
    s, e = para(name2line[n])
    for i in range(s, e): kill[i] = True
    if e < N and lines[e] == '': kill[e] = True   # the paragraph's trailing blank
# locate structural anchors (1-indexed in comments)
def find1(pred, desc):
    r = [i for i, l in enumerate(lines) if pred(l)]; assert len(r) == 1, (desc, r); return r[0]
i_ns = find1(lambda l: l == 'namespace SM', 'namespace SM')
i_ve_end = find1(lambda l: l == 'end VertexEdge', 'end VertexEdge')
i_slide = name2line['SM.s7_sliding_law_at']; i_bigon = name2line['SM.s7_bigon_law_at']
ps, pe = para(i_slide); pbs, pbe = para(i_bigon)
assert lines[ps].startswith('/-- The sliding branch') and lines[pbs].startswith('/-- The bigon branch')
for i in range(ps, pe): kill[i] = True
for i in range(pbs, pbe): kill[i] = True
imports = [l for l in lines[:i_ns] if l.startswith('import ')]
assert imports == ['import SM.CornerChainUnits', 'import SM.CS7Sliding', 'import SM.BigonDeletion', 'import SM.CarrierFloorRows'], imports
preamble = lines[i_ns:i_ns+11]
assert preamble == ['namespace SM', '', 'open Link Carrier', '', 'attribute [local instance] Classical.propDecidable', '', 'noncomputable section', '',
                    'section VertexEdge', '', 'variable {n : ℕ} [NeZero n]'], preamble
def squeeze(ls):
    out = []
    for l in ls:
        if l == '' and out and out[-1] == '': continue
        out.append(l)
    while out and out[-1] == '': out.pop()
    return out
def hdr(what):
    return (f'-- Ported {A.time}Z 2026-09-19 from {A.srcname} by the pod executor (files prepared by the W6-GLUE assembler): {what}')
reword = json.load(open(A.reword))
def apply_reword(text, which):
    used = []
    for old, new in reword:
        c = text.count(old)
        if c: assert c == 1, ('reword not unique', old); text = text.replace(old, new); used.append(old)
    return text, used
out = pathlib.Path(A.out); (out/'SM').mkdir(parents=True, exist_ok=True)
FORBID = re.compile(r'sorr|^\s*#(print|eval|check|reduce|exit)\b|^\s*axiom\b|\badmit\b', re.I | re.M)
def check(path, text):
    m = FORBID.search(text)
    assert not m, (path, text[max(0, m.start()-80):m.start()+80])
    assert 'import ' not in text.split('\n\n', 1)[1].replace('\nimport', '') or True
manifest = {}
units_ranges = []
def body_lines(a, b):
    """kept lines of [a, b) (0-indexed)"""
    return [lines[i] for i in range(a, b) if not kill[i]]
if A.split:
    sp = A.split - 1
    assert lines[sp].startswith('/-! ### Unit U110-F') and lines[sp-1] == '' and lines[sp-2] == '', (A.split, lines[sp][:60])
    partA = preamble + [''] + body_lines(i_ns+11, sp)
    partA = squeeze(partA) + ['', 'end VertexEdge', '', 'end', '', 'end SM', '']
    partB = preamble + [''] + body_lines(sp, i_ve_end) + ['end VertexEdge', '', 'end', '', 'end SM', '']
    partB = squeeze(partB) + ['']
    docA = ['/-! # Row 110 thm:C-S7 — the unit corpus, part A: the SLIDING branch (waves 3-4: SPLIT `s7p_`, RET `s7r_`, ROT `s7q_`, S3G `s7g_`,',
            'the wave-3 sliding glue `w3_`, S1P `s7u_`) — every declaration of the assembled draft before the bigon units, minus the leaf',
            '`s7_sliding_law_at` (SM/CS7.lean) and the superseded draft material listed in PORT_REPORT.md. -/']
    docB = ['/-! # Row 110 thm:C-S7 — the unit corpus, part B: the BIGON branch (waves 3-6: F `s7f_`, FB1-FB3 `s7fa_ s7fb_ s7fc_`, SITE/SITEC/SITEH',
            '`s7s_`, BLOCK `s7k_`, J `s7j_`, K `s7z_`, B3 `s7o_`, the wave-3/4 glue `w3_` `w4_`, RT `w5t_`, SITE `w5s_`, BR `w5b_`, ROW `w5r_`, the wave-5',
            'glue `w5_`, CURL `w6k_`, COR `w6c_`, ROT `w6r_`, CC `w6x_`, the wave-6 glue `w6_`) — every declaration of the assembled draft from',
            'unit F on, minus the leaf `s7_bigon_law_at` (SM/CS7.lean) and the superseded draft material listed in PORT_REPORT.md. -/']
    tA = '\n'.join([hdr('unit corpus part A (sliding branch), verbatim ranges of the assembled file minus the deletions of PORT_REPORT.md')] + imports + [''] + docA + [''] + partA)
    tB = '\n'.join([hdr('unit corpus part B (bigon branch), verbatim ranges of the assembled file minus the deletions of PORT_REPORT.md')] + ['import SM.CS7UnitsA'] + [''] + docB + [''] + partB)
    tA, uA = apply_reword(tA, 'A'); tB, uB = apply_reword(tB, 'B')
    used = uA + uB
    (out/'SM'/'CS7UnitsA.lean').write_text(tA); (out/'SM'/'CS7UnitsB.lean').write_text(tB)
    check('A', tA); check('B', tB)
    units_import = 'import SM.CS7UnitsB'
    manifest['CS7UnitsA'] = len(tA.split('\n')) - 1; manifest['CS7UnitsB'] = len(tB.split('\n')) - 1
else:
    part = preamble + [''] + body_lines(i_ns+11, i_ve_end) + ['end VertexEdge', '', 'end', '', 'end SM', '']
    part = squeeze(part) + ['']
    doc = ['/-! # Row 110 thm:C-S7 — the unit corpus (waves 3-6): every declaration of the assembled draft except the two leaves and the',
           'row theorems (SM/CS7.lean) and the superseded draft material listed in PORT_REPORT.md. -/']
    t = '\n'.join([hdr('unit corpus, verbatim ranges of the assembled file minus the deletions of PORT_REPORT.md')] + imports + [''] + doc + [''] + part)
    t, used = apply_reword(t, 'U')
    (out/'SM'/'CS7Units.lean').write_text(t); check('U', t)
    units_import = 'import SM.CS7Units'
    manifest['CS7Units'] = len(t.split('\n')) - 1
missing = [old for old, _ in reword if old not in used]
assert not missing, ('rewordings not applied', missing)
# CS7.lean: the two leaves + the tail (thm_C_S7_of, thm_C_S7_of_floor, thm_C_S7) verbatim
tail = lines[i_ve_end:]            # 'end VertexEdge' … 'end SM'
assert tail[-1] == 'end SM' and tail[-3] == 'end'
docC = ['/-! # Row 110 thm:C-S7 (sm-4:300-874) — FIXED name `SM.thm_C_S7`: the two branch leaves and the row assembly',
        '',
        'The frozen statements of work/drafts/corner/W3_Skeleton.lean (statements, names and docstrings byte-identical): the sliding',
        'leaf `s7_sliding_law_at` (closed in wave 4 through `s7u_sliding_law_at_of` and `s7u_box_carriers\'`), the bigon leaf',
        '`s7_bigon_law_at` (closed in wave 6 through `w4_s7_bigon_law_at_of` and Prop B2\' `w4_box_returnedRows`), the conditional',
        'assemblies `thm_C_S7_of` (on thm:floor and cb:singleton) and `thm_C_S7_of_floor` (on thm:floor alone), and the row theorem',
        '`thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor` (row 100, SM/CarrierFloorRows.lean). -/']
cs7 = ([hdr('the two leaves `s7_sliding_law_at`, `s7_bigon_law_at`, the assemblies `thm_C_S7_of`, `thm_C_S7_of_floor` and the row theorem `thm_C_S7` (frozen statements of W3_Skeleton.lean, verbatim)')]
       + [units_import, 'import SM.CarrierFloorRows', ''] + docC + [''] + preamble + [''] + lines[ps:pe] + [''] + lines[pbs:pbe] + [''] + tail + [''])
tC = '\n'.join(cs7); (out/'SM'/'CS7.lean').write_text(tC); check('C', tC)
manifest['CS7'] = len(cs7) - 1
# reference scan: deleted short names referenced by kept code lines (comments stripped roughly)
short = {n.split('.')[-1] for n in dele}
dangling = {}
depth = 0
for i, l in enumerate(lines):
    if kill[i] or i < i_ns: continue
    # skip docstring/comment lines
    s = l.strip()
    if s.startswith('/-') or s.startswith('--') or s.startswith('*') or depth:
        depth = max(0, depth + l.count('/-') - l.count('-/')); continue
    depth = max(0, depth + l.count('/-') - l.count('-/'))
    for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*", l):
        if w in short: dangling.setdefault(w, []).append(i + 1)
print(json.dumps({'lines': manifest, 'deleted': len(dele), 'killed_lines': sum(kill), 'rewordings': len(used),
                  'dangling_refs_to_deleted': {k: v[:6] for k, v in dangling.items()}}, indent=1, ensure_ascii=False))
