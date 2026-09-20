#!/usr/bin/env python3
"""Regenerate / verify R174_Assembled.lean (row-174 consumer wave, assembler 2026-09-15).

R174_Assembled.lean = Site_174.lean (2941 lines, verbatim)
  + R174_HREC.lean     [2942:3390]   (unit HREC,     prefix r174h_)
  + R174_CARRIERS.lean [2942:4439]   (unit CARRIERS, prefix r174c_)
  + R174_SITEIN.lean   [4440:4630]   (unit SITEIN,   prefix r174x_; its lines 1-4439 are R174_CARRIERS.lean)
  + R174_WALL.lean     [2942:5399]   (unit WALL,     prefix r174w_)
  + R174_SMOOTH.lean   [2942:3947]   (unit SMOOTH,   prefix r174s_)
  (one blank line between blocks)
  - de-duplication: the three WALL one-liners r174w_{x,w,m}_not_mem_Q (statement- and binder-identical to
    CARRIERS' r174c_{x,w,m}_not_mem_Q, all uses `… D`) are dropped and their uses renamed
  + the composition block (from `/-! ## R174 ASSEMBLY` to the end), kept in the assembled file itself.

Usage:  python3 assemble_R174.py <dir>           verify: rebuild from the inputs and compare byte-for-byte
        python3 assemble_R174.py <dir> --write   rebuild and overwrite R174_Assembled.lean (composition block
                                                 taken from the existing assembled file)
"""
import sys, os, re
D = sys.argv[1]; write = '--write' in sys.argv
def lines(f): return open(os.path.join(D, f), encoding='utf-8').read().splitlines()
site = lines('Site_174.lean'); assert len(site) == 2941, len(site)
units = [('R174_HREC.lean', 2942, 3390), ('R174_CARRIERS.lean', 2942, 4439), ('R174_SITEIN.lean', 4440, 4630),
         ('R174_WALL.lean', 2942, 5399), ('R174_SMOOTH.lean', 2942, 3947)]
out = list(site)
for f, a, b in units:
    L = lines(f)
    assert L[:2941] == site, f'{f}: lines 1-2941 differ from Site_174.lean'   # APPEND-ONLY check
    if f == 'R174_SITEIN.lean':
        assert L[:4439] == lines('R174_CARRIERS.lean'), 'SITEIN: lines 1-4439 differ from R174_CARRIERS.lean'
    assert len(L) == b, (f, len(L))
    out.append(''); out.extend(L[a-1:b])
# de-duplication
DROP = [('r174w_x_not_mem_Q', 'r174c_x_not_mem_Q'), ('r174w_w_not_mem_Q', 'r174c_w_not_mem_Q'), ('r174w_m_not_mem_Q', 'r174c_m_not_mem_Q')]
for drop, keep in DROP:
    idx = [i for i, l in enumerate(out) if re.match(rf'^theorem {re.escape(drop)}\b', l)]
    assert len(idx) == 1, (drop, idx)
    del out[idx[0]]
    pat = re.compile(rf'\b{re.escape(drop)}\b'); n = 0
    for k, l in enumerate(out):
        if pat.search(l): out[k] = pat.sub(keep, l); n += 1
    print(f'dedup: dropped {drop}, kept {keep}, {n} use lines renamed')
# the composition block from the existing assembled file
asm = lines('R174_Assembled.lean')
hdr = [i for i, l in enumerate(asm) if l.startswith('/-! ## R174 ASSEMBLY')]
assert len(hdr) == 1, hdr
comp = asm[hdr[0]-2:]          # two blank lines precede the header
out.extend(comp)
same = out == asm
print(f'regenerated {len(out)} lines; byte-identical to R174_Assembled.lean: {same}')
if write and not same:
    open(os.path.join(D, 'R174_Assembled.lean'), 'w', encoding='utf-8').write('\n'.join(out) + '\n'); print('written')
sys.exit(0 if same or write else 1)
