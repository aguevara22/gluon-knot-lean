#!/usr/bin/env python3
"""Assemble W3C_Assembled.lean = W3B_Assembled.lean + the six Wave-3c unit files (W3C_SPLITA, W3C_SPLITC,
W3C_BIGON, W3C_SITE, W3C_SPLITB, W3C_KNOT), each of which is the base with `sorry` bodies replaced and prefixed material inserted.  Every unit's
edit is taken as the exact `diff --normal` command list against the base (no fuzzy context); the edited base
ranges of the four units must be pairwise disjoint (asserted), and are applied bottom-up.  Then the assembler's
own connections (`CONNECT` below) are applied by exact string replacement.  Run in work/drafts/moves:
    python3 assemble_W3C.py"""
import re, subprocess, sys
BASE = 'W3B_Assembled.lean'
UNITS = ['W3C_SPLITA.lean', 'W3C_SPLITC.lean', 'W3C_BIGON.lean', 'W3C_SITE.lean', 'W3C_SPLITB.lean', 'W3C_KNOT.lean']
base = open(BASE, encoding='utf-8').read().split('\n')
cmd_re = re.compile(r'^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$')
edits = []   # (b_lo, b_hi, replacement_lines, unit)  -- base lines b_lo..b_hi (1-based, inclusive; hi<lo means pure insert after b_lo)
for u in UNITS:
    unit = open(u, encoding='utf-8').read().split('\n')
    out = subprocess.run(['diff', '--normal', BASE, u], capture_output=True, text=True).stdout.split('\n')
    for l in out:
        m = cmd_re.match(l)
        if not m: continue
        b1 = int(m.group(1)); b2 = int(m.group(2) or b1); op = m.group(3); u1 = int(m.group(4)); u2 = int(m.group(5) or u1)
        if op == 'a':      # append unit lines u1..u2 after base line b1
            edits.append((b1 + 1, b1, unit[u1 - 1:u2], u))
        elif op == 'c':    # change base b1..b2 into unit u1..u2
            edits.append((b1, b2, unit[u1 - 1:u2], u))
        else:              # delete base b1..b2
            edits.append((b1, b2, [], u))
# disjointness of edited base ranges (a pure insert after b occupies the "gap" b+0.5)
def span(e):
    lo, hi = e[0], e[1]
    return (lo - 0.5, lo - 0.5) if hi < lo else (lo, hi)
edits.sort(key=lambda e: span(e)[0])
for a, b in zip(edits, edits[1:]):
    sa, sb = span(a), span(b)
    assert sa[1] < sb[0], f"overlap: {a[3]} {a[:2]} vs {b[3]} {b[:2]}"
print(f"{len(edits)} edits from {len(UNITS)} units, pairwise disjoint in base coordinates:")
for e in edits:
    kind = 'insert after' if e[1] < e[0] else 'replace'
    print(f"  {e[3]:14s} {kind} base {e[0] if e[1] >= e[0] else e[0]-1}{'' if e[1] < e[0] else '-'+str(e[1])}: +{len(e[2])} lines"
          + (f" (removed: {[base[i-1].strip() for i in range(e[0], e[1]+1)]})" if e[1] >= e[0] else ''))
out = list(base)
for lo, hi, rep, u in reversed(edits):
    if hi < lo: out[lo - 1:lo - 1] = rep        # insert after base line lo-1  (index lo-1)
    else:       out[lo - 1:hi] = rep
text = '\n'.join(out)
# --- the assembler's own connections (exact, unique string replacements)
CONNECT = []; POST = None
try:
    from assemble_W3C_connect import CONNECT, POST   # optional: list of (old, new, note) + a post-processing function
except ImportError:
    pass
for old, new, note in CONNECT:
    n = text.count(old)
    assert n == 1, (note, n)
    text = text.replace(old, new)
    print(f"connected: {note}")
if POST is not None:
    text = POST(text)
open('W3C_Assembled.lean', 'w', encoding='utf-8').write(text)
print(f"W3C_Assembled.lean: {len(out)} lines (base {len(base)})")
