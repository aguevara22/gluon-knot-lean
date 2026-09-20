"""prune.py — delete the DEAD (sorryAx-carrying, off-path) declarations from an assembled corner file, each with its
attached docstring and `include … in` / `omit … in` lines.  Assert-guarded.  Usage: python3 prune.py SRC OUT name1 name2 …"""
import sys, pathlib, re
src, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]); names = sys.argv[3:]
L = src.read_text().split('\n')
KW = re.compile(r'^(theorem|def|abbrev|structure|instance|lemma|noncomputable def) ')
cut = []   # (start, end) 0-indexed inclusive
for nm in names:
    hits = [i for i,l in enumerate(L) if re.match(r'^(theorem|def|abbrev|lemma) ' + re.escape(nm) + r'\b', l)]
    assert len(hits) == 1, (nm, hits)
    i = hits[0]
    # walk back over docstring
    s = i
    if L[s-1].rstrip().endswith('-/'):
        j = s-1
        while not L[j].lstrip().startswith('/--'):
            j -= 1
            assert j > 0 and not L[j].startswith('theorem'), (nm, 'docstring scan')
        s = j
    # walk back over include/omit … in lines
    while L[s-1].startswith('include ') or L[s-1].startswith('omit '):
        assert L[s-1].rstrip().endswith(' in'), (nm, L[s-1])
        s -= 1
    # walk forward to the end of the body: first blank line followed by a non-indented line (or EOF)
    e = i
    while True:
        e += 1
        assert e < len(L), nm
        if L[e] == '' and (e+1 >= len(L) or not L[e+1].startswith(' ')):
            break
    # e is the blank line after the declaration; delete s..e (keeping one blank separation: the blank before s remains)
    assert L[s-1] == '', (nm, 'no blank before', L[s-1][:60])
    cut.append((s, e, nm))
cut.sort()
for a,b in zip(cut, cut[1:]):
    assert a[1] < b[0], ('overlap', a, b)
keep = []
pos = 0
for s,e,nm in cut:
    keep += L[pos:s]
    pos = e+1
keep += L[pos:]
out.write_text('\n'.join(keep))
print('deleted', len(cut), 'declarations,', len(L)-len(keep), 'lines;', 'result', len(keep)-1, 'lines')
for s,e,nm in cut: print(f'  {nm}: lines {s+1}-{e+1} ({e-s+1})')
