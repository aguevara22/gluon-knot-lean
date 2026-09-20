#!/usr/bin/env python3
"""port_copy_diff.py — byte-identity of the DELETED §0 copies of Comparison_Assembled.lean (CS7Data, CSoftData,
cvl_embedded_of_no_crossings, corner_values_i) against the accepted declarations in work/lean
(SM/CornerChainStatements.lean, SM/CornerChainUnits.lean).  For each name the DECLARATION BLOCK (declaration line
through the end of its paragraph, i.e. statement + fields / proof) is compared byte-for-byte; the docstring
paragraphs are compared separately and reported (the copies carry the comparison lane's own annotations by
design).  Exit 0 iff all four declaration blocks are identical."""
import pathlib, re, sys, difflib
HERE = pathlib.Path(__file__).resolve().parent
LANE = HERE.parent.parent
ASM = LANE / "Comparison_Assembled.lean"
LIB = LANE.parent.parent / "lean"
SRC = {"CS7Data": LIB / "SM/CornerChainStatements.lean", "CSoftData": LIB / "SM/CornerChainStatements.lean",
       "cvl_embedded_of_no_crossings": LIB / "SM/CornerChainUnits.lean", "corner_values_i": LIB / "SM/CornerChainUnits.lean"}
KIND = {"CS7Data": "structure", "CSoftData": "structure", "cvl_embedded_of_no_crossings": "theorem", "corner_values_i": "theorem"}

def block(path, kind, name):
    lines = path.read_text(encoding="utf-8").split("\n")
    idx = [i for i, l in enumerate(lines) if re.match(r"^%s %s\b" % (kind, re.escape(name)), l)]
    assert len(idx) == 1, (path, name, idx)
    k = idx[0]
    e = k
    while e < len(lines) and lines[e].strip() != "":
        e += 1
    # docstring paragraph directly above (if any)
    d = k - 1
    doc = None
    if d >= 0 and lines[d].rstrip().endswith("-/"):
        s = d
        while s >= 0 and not lines[s].startswith("/--"):
            s -= 1
        doc = "\n".join(lines[s:k])
    return k + 1, "\n".join(lines[k:e]), doc

ok = True
for name, kind in KIND.items():
    la, ba, da = block(ASM, kind, name)
    ll, bl, dl = block(SRC[name], kind, name)
    same = ba == bl
    ok &= same
    print(f"{name:32} assembled:{la:<5} {SRC[name].relative_to(LIB)}:{ll:<6} declaration block {'IDENTICAL' if same else 'DIFFERS'} "
          f"({ba.count(chr(10))+1} lines); docstring {'identical' if da == dl else 'differs (expected: lane annotation)'}")
    if not same:
        sys.stdout.writelines(difflib.unified_diff(bl.split("\n"), ba.split("\n"), "work/lean", "assembled", lineterm=""))
        print()
# wrappers: both sides declare the section variable
for p in (ASM, SRC["corner_values_i"]):
    pass
print("ALL FOUR DECLARATION BLOCKS IDENTICAL" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
