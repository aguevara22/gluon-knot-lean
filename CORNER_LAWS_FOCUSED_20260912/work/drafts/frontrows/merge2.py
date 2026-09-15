#!/usr/bin/env python3
"""Merge wave-2 unit files into Skeleton_W2.lean.

Each unit file W2_Ux.lean is Skeleton_W1.lean plus (a) inserted helper blocks and (b) leaf sorry bodies
replaced.  We parse `diff Skeleton_W1.lean W2_Ux.lean` (normal format), collect the hunks as edits on W1
line ranges, check that the hunks of different units never overlap (so the merge is order-independent),
and apply all of them in one bottom-up pass.  Every hunk stays contiguous.
"""
import re, subprocess, sys, pathlib

HERE = pathlib.Path(__file__).resolve().parent
BASE = HERE / "Skeleton_W1.lean"
UNITS = ["W2_U3", "W2_U4", "W2_U8D", "W2_U8R"]
OUT = HERE / "Skeleton_W2.lean"

base = BASE.read_text().split("\n")
HDR = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")

def parse(unit):
    txt = (HERE / f"{unit}.lean").read_text().split("\n")
    p = subprocess.run(["diff", str(BASE), str(HERE / f"{unit}.lean")], capture_output=True, text=True)
    hunks = []
    for line in p.stdout.split("\n"):
        m = HDR.match(line)
        if not m:
            continue
        a1 = int(m.group(1)); a2 = int(m.group(2) or a1); op = m.group(3)
        b1 = int(m.group(4)); b2 = int(m.group(5) or b1)
        new = txt[b1 - 1:b2] if op in "ac" else []
        if op == "a":
            # insert AFTER base line a1: replace empty range (a1, a1]
            hunks.append((unit, a1 + 1, a1, new))
        else:
            hunks.append((unit, a1, a2, new))          # replace base lines a1..a2 (1-based, inclusive)
    return hunks

hunks = []
for u in UNITS:
    hs = parse(u)
    print(f"{u}: {len(hs)} hunks:", ", ".join(f"[{s},{e}]+{len(n)}" for _, s, e, n in hs))
    hunks += hs

# overlap check: two hunks overlap if their base ranges intersect; an insertion at position p (range [p, p-1])
# conflicts with a replacement covering p-1 or p only if that replacement is from another unit and touches p-1..p.
def span(h):
    _, s, e, _ = h
    return (s, e) if e >= s else (s - 0.5, s - 0.5)   # insertion sits strictly between lines s-1 and s
for i in range(len(hunks)):
    for j in range(i + 1, len(hunks)):
        (s1, e1), (s2, e2) = span(hunks[i]), span(hunks[j])
        if hunks[i][0] != hunks[j][0] and not (e1 < s2 or e2 < s1):
            sys.exit(f"OVERLAP between {hunks[i][:3]} and {hunks[j][:3]}")
        if hunks[i][0] != hunks[j][0] and s1 == s2:
            sys.exit(f"CLASH: two units insert at the same position {hunks[i][:3]} / {hunks[j][:3]}")
print("no overlapping hunks")

# apply bottom-up (by base start position, descending)
hunks.sort(key=lambda h: (span(h)[0], h[0]), reverse=True)
out = list(base)
for unit, s, e, new in hunks:
    if e >= s:
        out[s - 1:e] = new
    else:
        out[s - 1:s - 1] = new
OUT.write_text("\n".join(out))
print(f"wrote {OUT} ({len(out)} lines)")

# verification: for every unit, every inserted/replacement block must occur verbatim and contiguously in OUT
big = "\n".join(out)
for unit, s, e, new in hunks:
    blk = "\n".join(new)
    if blk and big.count(blk) < 1:
        sys.exit(f"VERIFY FAIL: block of {unit} at base [{s},{e}] not found verbatim in output")
# and removing every unit's content must give back the base modulo the replaced leaf lines
print("verify: every hunk present verbatim and contiguous")
