#!/usr/bin/env python3
"""port_deviation.py — the COMPLETE list of non-blank lines of the port modules that do not occur verbatim in
Comparison_Assembled.lean (i.e. every deviation from verbatim: headers, imports, module docstrings, reduced `open` lines,
the row-122 one-liner).  Usage: python3 port_deviation.py"""
import pathlib
HERE = pathlib.Path(__file__).resolve().parent; PORT = HERE.parent
asm = set(l for l in (PORT.parent / "Comparison_Assembled.lean").read_text(encoding="utf-8").split("\n"))
tot = 0
for p in sorted((PORT / "SM").glob("*.lean")):
    dev = [(i + 1, l) for i, l in enumerate(p.read_text(encoding="utf-8").split("\n")) if l.strip() and l not in asm]
    tot += len(dev)
    print(f"## {p.name}: {len(dev)} lines not in the assembled file")
    for i, l in dev:
        print(f"  {i:4}: {l[:150]}{'…' if len(l) > 150 else ''}")
print(f"TOTAL {tot}")
