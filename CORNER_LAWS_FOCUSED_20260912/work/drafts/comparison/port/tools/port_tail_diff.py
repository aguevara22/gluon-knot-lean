#!/usr/bin/env python3
"""port_tail_diff.py — byte-identity of the CV/R tail's row-184 draft (work/drafts/cvtail/Wave1_Assembled.lean §5) against
what THIS lane ports: `CuspLawC`, `ReversalLawC`, `TrianglesC` (must be identical: the tail deletes its copies and imports),
`CInheritsData` (the tail's 11-field draft is REPLACED by this lane's 12-field bundle — the diff is printed), and the three
field reads of `corner_laws_and_soft_of` (`hinh.cusp_law`, `hinh.reversal_law`, `hinh.triangles`).  Declaration blocks
(declaration line through end of paragraph); docstrings compared separately."""
import pathlib, re, difflib
HERE = pathlib.Path(__file__).resolve().parent; PORT = HERE.parent; DRAFTS = PORT.parent.parent
W1 = DRAFTS / "cvtail/Wave1_Assembled.lean"
SRC = {"CuspLawC": PORT / "SM/CInherits.lean", "ReversalLawC": PORT / "SM/CInherits.lean",
       "TrianglesC": PORT / "SM/Comparison.lean", "CInheritsData": PORT / "SM/CInherits.lean"}
KIND = {"CuspLawC": "def", "ReversalLawC": "def", "TrianglesC": "def", "CInheritsData": "structure"}
def block(path, kind, name):
    lines = path.read_text(encoding="utf-8").split("\n")
    idx = [i for i, l in enumerate(lines) if re.match(r"^%s %s\b" % (kind, re.escape(name)), l)]
    assert len(idx) == 1, (path, name, idx); k = idx[0]; e = k
    while e < len(lines) and lines[e].strip() != "": e += 1
    d = k - 1; doc = None
    if d >= 0 and lines[d].rstrip().endswith("-/"):
        s = d
        while s >= 0 and not lines[s].startswith("/--"): s -= 1
        doc = "\n".join(lines[s:k])
    return k + 1, "\n".join(lines[k:e]), doc
for name, kind in KIND.items():
    lw, bw, dw = block(W1, kind, name); lp, bp, dp = block(SRC[name], kind, name)
    print(f"{name:14} Wave1:{lw:<5} port {SRC[name].name}:{lp:<4} declaration block {'IDENTICAL' if bw == bp else 'DIFFERS'}; docstring {'identical' if dw == dp else 'differs'}")
    if bw != bp:
        print("\n".join("    " + l for l in difflib.unified_diff(bw.split("\n"), bp.split("\n"), "cvtail/Wave1_Assembled.lean", "port/SM/CInherits.lean", lineterm="", n=1)))
w = W1.read_text(encoding="utf-8").split("\n")
i = next(k for k, l in enumerate(w) if l.startswith("theorem corner_laws_and_soft_of"))
reads = [l.strip() for l in w[i:i + 16] if "hinh." in l]
print("corner_laws_and_soft_of reads:", reads)
