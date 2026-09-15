#!/usr/bin/env python3
"""Mechanical port of a Carrier-lane module from `hP : Generic P` to the accepted geometric layer
`SM.GeoCarrier` (`hP : CrossingGeometry P`).  Prototype transformer for the CV-DOM cost analysis;
prints the number of textual substitutions so the manual residue can be measured."""
import re, sys
DEFMAP = {  # SM.Carrier name -> SM.GeoCarrier name (accepted, SM/FlatCarriersDefs.lean / FlatCarriers.lean)
 'smoothingSuccessor':'geoSmoothingSuccessor','markSuccessor':'geoMarkSuccessor','owner':'geoOwner',
 'Component':'GeoComponent','componentMarkList':'geoComponentMarkList','componentPlaneCycle':'geoComponentPlaneCycle',
 'smoothingSegment':'geoSmoothingSegment','ccpCornerPolygon':'geoCornerPolygon','ccpCornerList':'geoComponentCornerList',
 'ccpCornerCount':'geoCornerCount','ccpCornerMark':'geoCornerMark','ccpOutSlot':'geoOutSlot','ccpInEdge':'geoInEdge',
 'carrierCrossings':'geoCarrierCrossings','markList':'geoMarkList','markCycle':'geoMarkCycle','nextMark':'geoNextMark',
 'prevMark':'geoPrevMark','markKey':'geoMarkKey','markLinearOrder':'geoMarkLinearOrder','componentFintype':'geoComponentFintype',
}
src = open(sys.argv[1]).read()
n = 0
def sub(pat, rep, s, flags=0):
    global n
    s2, k = re.subn(pat, rep, s, flags=flags); n += k; return s2
s = src
s = sub(r'\(hn : 3 ≤ n\) \{P : LabelledTuple n\}\s*\n?\s*\(hP : Generic P\)', '{P : LabelledTuple n} (hP : CrossingGeometry P)', s)
s = sub(r'markPosition hn hP\.1', 'geoMarkPosition hP', s)
s = sub(r'visitPosition hn hP\.1', 'geometricVisitPosition hP', s)
# definitions and lemmas about them: `X hn hP` -> `geoX hP` when X (or X_suffix) starts with a mapped def name
names = sorted(DEFMAP, key=len, reverse=True)
for old in names:
    new = DEFMAP[old]
    s = sub(r'\b' + re.escape(old) + r'(_[A-Za-z0-9_\'₀-₉]*)? hn hP\b', lambda m: new + (m.group(1) or '') + ' hP', s)
# theorem/def names declared in this file: same prefix rule, else geo_ prefix
GEO = set()
for f in ['lean/SM/FlatCarriersDefs.lean', 'lean/SM/FlatCarriers.lean']:
    for m in re.finditer(r'^(?:noncomputable )?(?:def|abbrev|structure|instance|theorem)\s+([A-Za-z_][A-Za-z0-9_.\'₀-₉]*)', open(f).read(), re.M):
        GEO.add(m.group(1))
blocks = re.split(r'(?=^(?:theorem|def|noncomputable def|abbrev|instance|/--|@\[))', s, flags=re.M)
out = []
for b in blocks:
    m = re.match(r'^(?:theorem|def|noncomputable def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_\'₀-₉]*)(.*)', b, re.S)
    if not m: out.append(b); continue
    d, rest = m.group(1), m.group(2)
    sig = rest.split(':=')[0]
    if 'hP' not in sig and not any(re.search(r'\b'+re.escape(v)+r'\b', sig) for v in DEFMAP.values()):
        out.append(b); continue          # hypothesis-free: keep as is (it is shared with the accepted lane)
    new = None
    for old in names:
        if d == old or d.startswith(old + '_'):
            new = DEFMAP[old] + d[len(old):]; break
    if new is None: new = 'geo_' + d
    if new in GEO:                        # already in the accepted geo layer: drop, references resolve there
        while out and (out[-1].startswith('/--') or out[-1].startswith('@[')): out.pop()   # its docstring / attribute
        out.append('-- [port] `' + d + '` -> accepted `' + new + '` (SM/FlatCarriers*.lean); not re-declared\n\n'); continue
    out.append(b)
s = ''.join(out)
decl = re.findall(r'^(?:theorem|def|noncomputable def|abbrev|instance)\s+([A-Za-z_][A-Za-z0-9_\'₀-₉]*)', src, re.M)
for d in decl:
    new = None
    for old in names:
        if d == old or d.startswith(old + '_'):
            new = DEFMAP[old] + d[len(old):]; break
    if new is None: new = 'geo_' + d
    if re.search(r'^(?:theorem|def|noncomputable def|abbrev|instance)\s+' + re.escape(d) + r'\b', s, re.M) or new in GEO:
        s = sub(r'\b' + re.escape(d) + r'\b', new, s)
s = sub(r'namespace SM\.Carrier', 'namespace SM.GeoCarrier\nopen Carrier', s)
s = sub(r'end SM\.Carrier', 'end SM.GeoCarrier', s)
s = sub(r'^import SM\.Carrier[A-Za-z]*\n', '', s, re.M)
s = s.replace('import SM.GaussWord', 'import SM.FlatCarriers', 1)
sys.stdout.write(s)
print(f'-- substitutions: {n}', file=sys.stderr)
