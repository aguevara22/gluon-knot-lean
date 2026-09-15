#!/usr/bin/env python3
"""Merge wave-3a unit files into Skeleton_W3.lean.

Each unit file W3_Ux.lean is Skeleton_W2.lean plus (a) ONE inserted infrastructure block and (b) leaf sorry bodies
replaced.  We parse `diff Skeleton_W2.lean W3_Ux.lean` (normal format), collect the hunks as edits on W2 line
ranges, verify each hunk (no deletions; every `c` hunk replaces exactly one `:= sorry` line and keeps the statement
prefix verbatim; the inserted block is a single balanced `namespace … end` with no top-level directives), check
that the hunks of different units never overlap (so the merge is order-independent), and apply all of them in one
bottom-up pass.  Every hunk stays contiguous.  Rerunnable: python3 merge3.py
"""
import re, subprocess, sys, pathlib

HERE = pathlib.Path(__file__).resolve().parent
BASE = HERE / "Skeleton_W2.lean"
UNITS = ["W3_U5", "W3_U6"]
OUT = HERE / "Skeleton_W3.lean"

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
        if op == "d":
            sys.exit(f"VIOLATION {unit}: deletion hunk {line}")
        new = txt[b1 - 1:b2]
        if op == "a":
            hunks.append((unit, a1 + 1, a1, new))        # insert AFTER base line a1: empty range (a1+1, a1]
        else:
            hunks.append((unit, a1, a2, new))            # replace base lines a1..a2 (1-based, inclusive)
    return hunks

def check_block(unit, new):
    """the inserted block: balanced namespace/section nesting, closed at the end, no sorry, no top-level directives"""
    stack = []; ns = []
    for i, raw in enumerate(new):
        s = raw.strip()
        if "sorry" in raw:
            sys.exit(f"VIOLATION {unit}: sorry inside inserted block (block line {i+1})")
        m = re.match(r"^namespace\s+(\S+)", s)
        if m:
            stack.append(("ns", m.group(1))); ns.append(m.group(1)); continue
        if re.match(r"^(?:noncomputable\s+)?section(?:\s+\S+)?\s*$", s):
            stack.append(("sec", None)); continue
        if re.match(r"^end(?:\s+\S+)?\s*$", s):
            if not stack:
                sys.exit(f"VIOLATION {unit}: unbalanced `end` in inserted block (block line {i+1})")
            stack.pop(); continue
        if not stack and re.match(r"^(set_option|attribute|open|import|local |scoped |macro|notation|syntax|elab)\b", s):
            sys.exit(f"VIOLATION {unit}: top-level directive outside the block's namespace: {s[:80]}")
        if re.match(r"^\s*(set_option|attribute)\b", raw):
            sys.exit(f"VIOLATION {unit}: set_option/attribute inside block (block line {i+1}): {s[:80]}")
    if stack:
        sys.exit(f"VIOLATION {unit}: inserted block not closed, open scopes {stack}")
    top_ns = [n for n in ns]
    return top_ns

def check_leaf(unit, s, e, new):
    """a `c` hunk: exactly one base line, ending `:= sorry`; the replacement keeps the text before `:=` verbatim"""
    if e != s:
        sys.exit(f"VIOLATION {unit}: c-hunk spans several base lines [{s},{e}]")
    old = base[s - 1]
    if not old.rstrip().endswith(":= sorry"):
        sys.exit(f"VIOLATION {unit}: c-hunk at base L{s} does not replace a `:= sorry` line: {old.strip()[:80]}")
    if old.split(":=")[0] != new[0].split(":=")[0]:
        sys.exit(f"VIOLATION {unit}: statement prefix changed at base L{s}")
    if "sorry" in "\n".join(new):
        sys.exit(f"VIOLATION {unit}: replacement body at base L{s} still contains sorry")

hunks = []
for u in UNITS:
    hs = parse(u)
    ins = [h for h in hs if h[2] < h[1]]
    rep = [h for h in hs if h[2] >= h[1]]
    if len(ins) != 1:
        sys.exit(f"VIOLATION {u}: expected exactly ONE inserted block, found {len(ins)}")
    names = check_block(u, ins[0][3])
    for h in rep:
        check_leaf(u, h[1], h[2], h[3])
    print(f"{u}: {len(hs)} hunks:", ", ".join(f"[{s},{e}]+{len(n)}" for _, s, e, n in hs),
          f"| block namespaces {sorted(set(names))} | leaves replaced: {len(rep)} | checks OK")
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
print("verify: every hunk present verbatim and contiguous")
# and the residual: lines of the base not in the output must be exactly the replaced leaf lines
removed = sum(1 for _, s, e, _ in hunks if e >= s)
print(f"base lines replaced: {removed}; sorry count in output: {big.count('sorry')}")
