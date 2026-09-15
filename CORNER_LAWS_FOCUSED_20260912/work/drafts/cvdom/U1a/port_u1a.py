#!/usr/bin/env python3
"""U1a driver: extended port_lane.py (work/drafts/cvdom/port_lane.py) applied to the U1a source files in
dependency order, emitting one module body.  Run from work/ (paths relative to work/)."""
import re, sys, os
DEFMAP = {
 'smoothingSuccessor':'geoSmoothingSuccessor','markSuccessor':'geoMarkSuccessor','owner':'geoOwner',
 'Component':'GeoComponent','componentMarkList':'geoComponentMarkList','componentPlaneCycle':'geoComponentPlaneCycle',
 'smoothingSegment':'geoSmoothingSegment','ccpCornerPolygon':'geoCornerPolygon','ccpCornerList':'geoComponentCornerList',
 'ccpCornerCount':'geoCornerCount','ccpCornerMark':'geoCornerMark','ccpOutSlot':'geoOutSlot','ccpInEdge':'geoInEdge',
 'carrierCrossings':'geoCarrierCrossings','markList':'geoMarkList','markCycle':'geoMarkCycle','nextMark':'geoNextMark',
 'prevMark':'geoPrevMark','markKey':'geoMarkKey','markLinearOrder':'geoMarkLinearOrder','componentFintype':'geoComponentFintype',
 # U1a extensions (DECISION_FINAL §5: DEFMAP extended with componentCycle, InheritsMarkOrder, ...)
 'componentCycle':'geoComponentCycle','InheritsMarkOrder':'GeoInheritsMarkOrder',
 'componentForgetSwitch':'geoComponentForgetSwitch','PendingPairsTogether':'GeoPendingPairsTogether',
 'componentCornerCycle':'geoComponentCornerCycle','component':'geoComponent','markPosition':'geoMarkPosition',
 'inheritsMarkOrder':'geoInheritsMarkOrder','pendingPairsTogether':'geoPendingPairsTogether','independent':'geoIndependent',
}
# names whose accepted geo counterpart is spelled differently from the prefix rule
SPECIAL = {'prevMark_nextMark':'geoPrevMark_geoNextMark','nextMark_prevMark':'geoNextMark_geoPrevMark',
           'selectedMarkPerm_evaluation':'geoSelectedMarkPerm_evaluation'}
FILES = sys.argv[1:]
GEO = set()
for f in ['lean/SM/FlatCarriersDefs.lean', 'lean/SM/FlatCarriers.lean', 'lean/SM/GeoCarrierGeometry.lean']:
    for m in re.finditer(r'^(?:noncomputable )?(?:def|abbrev|structure|instance|theorem)\s+([A-Za-z_][A-Za-z0-9_.\'₀-₉]*)', open(f).read(), re.M):
        GEO.add(m.group(1))
names = sorted(DEFMAP, key=len, reverse=True)
def newname(d):
    if d in SPECIAL: return SPECIAL[d]
    if d.startswith('mem_'):
        r = newname(d[4:])
        return 'mem_' + r if not r.startswith('geo_') else 'geo_' + d
    for old in names:
        if d == old or d.startswith(old + '_'):
            return DEFMAP[old] + d[len(old):]
    return 'geo_' + d
DECL_RE = r'^(?:noncomputable )?(?:def|abbrev|structure|instance|theorem)\s+([A-Za-z_][A-Za-z0-9_\'₀-₉]*)'
# pass 0: classify every declaration of every file: hypothesis-free (kept, referenced under its accepted name),
# geo-existing (dropped, referenced under the accepted geo name), or ported (renamed).
srcs = {f: open(f).read() for f in FILES}
def blocks_of(s):
    return re.split(r'(?=^(?:theorem|def|noncomputable def|abbrev|instance|/--|@\[))', s, flags=re.M)
def pre_subst(s):
    s = re.sub(r'\(hn : 3 ≤ n\)\s+\{P : LabelledTuple n\}\s+\(hP : (?:Generic|G1) P\)', '{P : LabelledTuple n} (hP : CrossingGeometry P)', s)
    s = re.sub(r'\(hn : 3 ≤ n\) \(hP : (?:Generic|G1) P\)', '(hP : CrossingGeometry P)', s)
    s = re.sub(r'markPosition hn hP(?:\.1)?\b', 'geoMarkPosition hP', s)
    s = re.sub(r'visitPosition hn hP(?:\.1)?\b', 'geometricVisitPosition hP', s)
    s = re.sub(r'visitKey hn hP(?:\.1)?\b', 'geometricVisitKey hP', s)
    s = re.sub(r'crossingVisitBetween hn hP(?:\.1)?\b', 'geometricCrossingVisitBetween hP', s)
    s = re.sub(r'crossingVisitBetween_complement hn hP\b', 'geo_crossingVisitBetween_complement hP', s)
    s = re.sub(r'interlaces_iff_unique hn hP\b', 'geo_interlaces_iff_unique hP', s)
    s = re.sub(r'\bInterlaces hn hP\b', 'GeometricInterlaces hP', s)
    s = re.sub(r'\(hS : S ∈ independentSupports hn hP\)', '(hS : GeoIndependent hP S)', s)
    s = re.sub(r'\(mem_independentSupports_iff hn hP S\)\.mp hS\b', 'hS', s)
    return s
kind = {}   # decl -> 'free' | 'geo' | 'port'
for f in FILES:
    s = pre_subst(srcs[f])
    for b in blocks_of(s):
        m = re.match(r'^(?:theorem|def|noncomputable def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_\'₀-₉]*)(.*)', b, re.S)
        if not m: continue
        d, rest = m.group(1), m.group(2)
        sig = rest.split(':=')[0]
        free = 'hP' not in sig and not any(re.search(r'\b'+re.escape(v)+r'\b', sig) for v in DEFMAP.values())
        if free: kind[d] = 'free'
        elif newname(d) in GEO: kind[d] = 'geo'
        else: kind[d] = 'port'
nsub = 0
out_all = []
for f in FILES:
    s = pre_subst(srcs[f])
    # declared-in-lane names (any of the FILES): drop `hn ` after them and rename
    for d, k in sorted(kind.items(), key=lambda kv: -len(kv[0])):
        if k == 'free': continue
        new = newname(d)
        s = re.sub(r'\b' + re.escape(d) + r' hn hP\b', new + ' hP', s)
        s = re.sub(r'\b' + re.escape(d) + r'\b', new, s)
    # X_suffix hn hP -> geoX_suffix hP for mapped prefixes (names of other lane modules)
    for old in names:
        new = DEFMAP[old]
        s = re.sub(r'\b' + re.escape(old) + r'(_[A-Za-z0-9_\'₀-₉]*)? hn hP\b', lambda m: new + (m.group(1) or '') + ' hP', s)
    s = s.replace('letI := ', 'let _ := ')
    # drop hypothesis-free and geo-existing declarations
    out = []
    for b in blocks_of(s):
        m = re.match(r'^(?:theorem|def|noncomputable def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_\'₀-₉]*)(.*)', b, re.S)
        if not m: out.append(b); continue
        d = m.group(1)
        # d may already be renamed; find original
        orig = None
        for o, k in kind.items():
            if (k == 'free' and o == d) or (k != 'free' and newname(o) == d): orig = o; break
        k = kind.get(orig)
        if k in ('free', 'geo'):
            while out and (out[-1].startswith('/--') or out[-1].startswith('@[')): out.pop()
            tag = 'accepted `Carrier.' + orig + '` (hypothesis-free, shared)' if k == 'free' else 'accepted `' + d + '` (SM/FlatCarriers*.lean)'
            out.append('-- [port] `' + orig + '` -> ' + tag + '; not re-declared\n\n'); continue
        out.append(b)
    s = ''.join(out)
    # strip module header/footer
    s = re.sub(r'^import .*\n', '', s, flags=re.M)
    s = re.sub(r'/-! Ported verbatim.*?-/\n', '', s, flags=re.S)
    s = re.sub(r'namespace SM\.Carrier\n', '', s)
    s = re.sub(r'noncomputable section\n', '', s)
    s = re.sub(r'attribute \[local instance\] Classical\.propDecidable\n', '', s)
    s = re.sub(r'variable \{n : ℕ\} \[NeZero n\]\n', '', s)
    wrap = 'variable {n : ℕ} {P : LabelledTuple n}\n' in s
    s = re.sub(r'variable \{n : ℕ\} \{P : LabelledTuple n\}\n', 'section SameArc\n\nvariable {P : LabelledTuple n}\n', s)
    s = re.sub(r'\nend\nend SM\.Carrier\n', '\n', s)
    s = re.sub(r'\n{3,}', '\n\n', s).strip('\n')
    if wrap: s = s + '\n\nend SameArc'
    out_all.append('/-! ### Port of SM/' + os.path.basename(f) + ' -/\n\n' + s + '\n')
sys.stdout.write('\n\n'.join(out_all))
print('-- kinds:', {k: sum(1 for v in kind.values() if v == k) for k in ('free','geo','port')}, file=sys.stderr)
for d, k in kind.items():
    print(f'{k:5} {d} -> {newname(d) if k != "free" else d}', file=sys.stderr)
