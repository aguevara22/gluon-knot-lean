#!/usr/bin/env python3
"""Refresh the sha256 lines of the given package-root files in the root MANIFEST.sha256 (files the executor maintains: FINAL_REVIEW.md, lean/axiom-policy.json)."""
import hashlib, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
man = ROOT / 'MANIFEST.sha256'
lines = man.read_text().splitlines()
for name in sys.argv[1:]:
    h = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    out = []
    hit = False
    for ln in lines:
        if ln.endswith('  ' + name):
            out.append(h + '  ' + name); hit = True
        else:
            out.append(ln)
    if not hit:
        sys.exit('not in manifest: ' + name)
    lines = out
    print('refreshed', name, h[:16])
man.write_text('\n'.join(lines) + '\n')
