#!/usr/bin/env python3
"""Assemble RPC_Assembled.lean from RPC_Skeleton.lean + the unit files RPC_U_{A,B,C,D}.lean.

Each unit file must be the skeleton with (a) some `  sorry` lines replaced by proof bodies and
(b) helper declarations inserted.  We parse `diff skeleton unit` (normal format), refuse any hunk
that removes a non-`sorry` line, refuse overlapping hunks between units, then apply all hunks in
one pass over the skeleton.  Afterwards every unit's added block is checked to occur contiguously
in the result, and helper names are checked for duplicates / clashes.
"""
import re, subprocess, sys, collections

D = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/fd"
SKEL = f"{D}/RPC_Skeleton.lean"
UNITS = ["A", "B", "C", "D"]
OUT = f"{D}/RPC_Assembled.lean"

skel = open(SKEL).read().split("\n")
hunk_re = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")

def parse_hunks(unit_path):
    p = subprocess.run(["diff", SKEL, unit_path], capture_output=True, text=True)
    lines = p.stdout.split("\n")
    unit = open(unit_path).read().split("\n")
    hunks = []
    i = 0
    while i < len(lines):
        m = hunk_re.match(lines[i])
        if not m:
            i += 1; continue
        s1, s2, op, u1, u2 = m.groups()
        s1 = int(s1); s2 = int(s2) if s2 else s1
        u1 = int(u1); u2 = int(u2) if u2 else u1
        i += 1
        removed, added = [], []
        while i < len(lines) and lines[i].startswith("< "):
            removed.append(lines[i][2:]); i += 1
        if i < len(lines) and lines[i] == "---":
            i += 1
        while i < len(lines) and lines[i].startswith("> "):
            added.append(lines[i][2:]); i += 1
        # cross-check added against the unit file lines
        assert added == unit[u1-1:u2], f"{unit_path}: hunk {m.group(0)} added-lines mismatch"
        hunks.append(dict(op=op, s1=s1, s2=s2, removed=removed, added=added, hdr=m.group(0)))
    return hunks

all_hunks = {}
violations = []
for u in UNITS:
    path = f"{D}/RPC_U_{u}.lean"
    hs = parse_hunks(path)
    for h in hs:
        if h["op"] == "d":
            violations.append(f"unit {u} hunk {h['hdr']}: pure deletion")
        for r in h["removed"]:
            if r != "  sorry":
                violations.append(f"unit {u} hunk {h['hdr']}: removes non-sorry line {r!r}")
        if h["op"] == "c" and (h["s2"] != h["s1"]):
            violations.append(f"unit {u} hunk {h['hdr']}: replaces more than one skeleton line")
    all_hunks[u] = hs
    print(f"unit {u}: {len(hs)} hunks: " + ", ".join(h['hdr'] for h in hs))

# overlap check between units (skeleton coordinates)
touched = {}
for u, hs in all_hunks.items():
    for h in hs:
        key = (h["op"], h["s1"])
        for s in range(h["s1"], h["s2"] + 1):
            k = (h["op"], s)
            if k in touched:
                violations.append(f"overlap at skeleton line {s} ({h['op']}): units {touched[k]} and {u}")
            touched[k] = u

if violations:
    print("VIOLATIONS:"); [print("  " + v) for v in violations]
    sys.exit(1)

# helper names (top-level declarations added by units)
decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev|structure|instance|noncomputable def)\s+([^\s:({\[]+)")
helpers = collections.OrderedDict()
for u, hs in all_hunks.items():
    for h in hs:
        for ln in h["added"]:
            m = decl_re.match(ln)
            if m:
                helpers.setdefault(m.group(2), []).append(u)
dups = {n: us for n, us in helpers.items() if len(us) > 1}
print("helpers:", dict(helpers))
if dups:
    print("DUPLICATE helper names across units:", dups); sys.exit(2)

# apply: replacement at s1 for 'c', insertion after s1 for 'a'
repl = {}; ins = {}
for u, hs in all_hunks.items():
    for h in hs:
        if h["op"] == "c":
            assert skel[h["s1"]-1] == "  sorry"
            repl[h["s1"]] = (u, h["added"])
        else:
            ins.setdefault(h["s1"], []).append((u, h["added"]))
out = []
for i, ln in enumerate(skel, start=1):
    if i in repl:
        out.extend(repl[i][1])
    else:
        out.append(ln)
    for (u, block) in ins.get(i, []):
        out.extend(block)
text = "\n".join(out)
open(OUT, "w").write(text)
print(f"wrote {OUT}: {len(out)} lines (skeleton {len(skel)})")

# contiguity check: every added block appears verbatim and contiguously
outs = "\n" + text + "\n"
for u, hs in all_hunks.items():
    for h in hs:
        blk = "\n" + "\n".join(h["added"]) + "\n"
        c = outs.count(blk)
        if c != 1:
            print(f"CONTIGUITY FAIL unit {u} hunk {h['hdr']}: occurrences={c}"); sys.exit(3)
print("contiguity: every hunk block occurs exactly once, contiguously")
print("remaining sorry lines:", sum(1 for l in out if l.strip() == "sorry"))
