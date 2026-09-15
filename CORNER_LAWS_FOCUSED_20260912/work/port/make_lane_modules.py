#!/usr/bin/env python3
"""Port a kernel-checked candidate prototype of the previous executor (work/checks) into
canonical modules under work/lean/SM, one module per candidate body, byte-for-byte.

Rule: bodies are taken in the exact concatenation order of the passing prototype
<Stem>.prototype.lean (receipt <Stem>-prototype-result.json). A body whose module
work/lean/SM/<Body>.lean already exists (ported by an earlier lane) is reused. A new
module imports the prototype's own import header plus every module of the bodies
preceding it in this prototype, so it sees exactly what it saw inside the prototype.
Usage: python3 make_lane_modules.py <Stem> [--write]
"""
import json, sys, hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / 'work/checks'
SM = ROOT / 'work/lean/SM'
stem = sys.argv[1]
write = '--write' in sys.argv
receipt = json.loads((CHECKS / f'{stem}-prototype-result.json').read_text())
assert receipt.get('exit_code') == 0, 'receipt did not pass'
proto = (CHECKS / f'{stem}.prototype.lean').read_text()
bodies = [k for k in receipt['files_sha256'] if k.endswith('.body.lean')]
order = []
for b in bodies:
    p = ROOT / b
    assert hashlib.sha256(p.read_bytes()).hexdigest() == receipt['files_sha256'][b], 'hash mismatch ' + b
    txt = p.read_text().strip()
    pos = proto.find(txt)
    assert pos >= 0, 'body not contained in prototype: ' + b
    order.append((pos, b, txt))
order.sort()
header_imports = [l for l in proto.splitlines() if l.startswith('import ')]
for imp in header_imports:
    name = imp.split()[1]
    if name.startswith('SM.'):
        assert (SM / (name[3:] + '.lean')).exists(), 'missing canonical import ' + name
preceding = []
plan = []
for _, b, txt in order:
    body = Path(b).name.replace('.body.lean', '')
    target = SM / (body + '.lean')
    if target.exists():
        existing = target.read_text()
        assert txt in existing, 'existing module differs from candidate body: ' + body
        plan.append(('REUSE', target, None))
    else:
        imports = header_imports + ['import SM.' + m for m in preceding]
        doc = ("/-! Ported verbatim from the previous executor's kernel-checked candidate\n"
               "work/checks/%s (prototype %s, kernel session %s, receipt\n"
               "%s-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/\n"
               % (Path(b).name, stem, receipt['kernel_session'], stem))
        plan.append(('WRITE', target, '\n'.join(imports) + '\n\n' + doc + '\n' + txt + '\n'))
    preceding.append(body)
for action, target, content in plan:
    rel = target.relative_to(ROOT)
    if action == 'WRITE':
        print(('WRITE ' if write else 'PLAN  ') + str(rel), len(content.splitlines()), 'lines')
        if write:
            target.write_text(content)
    else:
        print('REUSE ' + str(rel))
print('last module: SM.' + preceding[-1], '| new:', sum(1 for a, _, _ in plan if a == 'WRITE'),
      '| reused:', sum(1 for a, _, _ in plan if a == 'REUSE'))
