#!/usr/bin/env python3
"""Namespace-aware clash scan for the wave-3a merge (rerun: python3 clash_scan_w3a.py).
Indexes the two new infrastructure blocks (U5, U6) as they sit in Skeleton_W3.lean, plus the rest of the merged
file, and intersects (a) the new blocks' fully-qualified names with every .lean under work/lean (excluding .lake),
(b) the two new blocks against each other, (c) the new blocks against the pre-existing part of the skeleton."""
import re, os, sys, collections
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912"
MERGED = f"{ROOT}/work/drafts/frontrows/Skeleton_W3.lean"
WORK = f"{ROOT}/work/lean"

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|macro_rules|notation|syntax|elab|macro)\s+'
                  r'(?:\{[^}]*\}\s*)?([^\s:({\[⟨]+)')
NS = re.compile(r'^\s*namespace\s+([^\s]+)')
SEC = re.compile(r'^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$')
END = re.compile(r'^\s*end(?:\s+([^\s]+))?\s*$')

def index(path):
    out = []  # (fullname, line, kind)
    stack = []
    in_block_comment = 0
    try:
        lines = open(path, encoding="utf-8").read().split("\n")
    except Exception:
        return out
    for i, raw in enumerate(lines, 1):
        line = raw
        if in_block_comment:
            if "-/" in line:
                in_block_comment = max(0, in_block_comment - line.count("-/"))
                line = line.split("-/")[-1]
            else:
                continue
        if "/-" in line:
            opens = line.count("/-"); closes = line.count("-/")
            if opens > closes:
                in_block_comment += opens - closes
                line = line.split("/-")[0]
            else:
                line = re.sub(r'/-.*?-/', '', line)
        line = line.split("--")[0]
        if not line.strip():
            continue
        m = NS.match(line)
        if m:
            stack.append(('ns', m.group(1))); continue
        m = SEC.match(line)
        if m:
            stack.append(('sec', m.group(1))); continue
        m = END.match(line)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if m:
            kind, name = m.group(1), m.group(2)
            if kind == "instance" and (name.startswith(":") or name[0] == "["):
                continue
            if kind in ("macro_rules", "notation", "syntax", "elab", "macro"):
                continue
            ns = ".".join(n for k, n in stack if k == 'ns')
            full = f"{ns}.{name}" if ns and not name.startswith("_root_") else name.replace("_root_.", "")
            out.append((full, i, kind))
    return out

merged = index(MERGED)
lines = open(MERGED).read().split("\n")
# block ranges in Skeleton_W3.lean, located by their markers
def find(marker, start=0):
    for i in range(start, len(lines)):
        if lines[i].startswith(marker):
            return i + 1
    sys.exit(f"marker not found: {marker}")
u5a = find("/-! ### U5 infrastructure -/"); u5b = find("end U5", u5a)
u6a = find("/-! ### U6 infrastructure -/"); u6b = find("end U6", u6a)
print(f"U5 block: Skeleton_W3.lean L{u5a}-{u5b}; U6 block: L{u6a}-{u6b}")
u5 = [(f, l, k) for f, l, k in merged if u5a <= l <= u5b]
u6 = [(f, l, k) for f, l, k in merged if u6a <= l <= u6b]
rest = [(f, l, k) for f, l, k in merged if not (u5a <= l <= u5b or u6a <= l <= u6b)]
print(f"declarations: U5 {len(u5)}, U6 {len(u6)}, rest of skeleton {len(rest)}")
def names(lst):
    d = collections.OrderedDict()
    for f, l, k in lst:
        d.setdefault(f, []).append((l, k))
    return d
n5, n6, nr = names(u5), names(u6), names(rest)
for tag, d in (("U5", n5), ("U6", n6)):
    dups = {k: v for k, v in d.items() if len(v) > 1}
    print(f"  {tag}: {len(d)} distinct full names; duplicates inside the block: {dups if dups else 'none'}")
    bad = [k for k in d if not k.startswith(f"SM.FrontRows.{tag}.")]
    print(f"  {tag}: names outside namespace SM.FrontRows.{tag}: {bad if bad else 'none'}")
print("(b) U5 ∩ U6 full names:", sorted(set(n5) & set(n6)) or "none")
print("(c) U5 ∩ rest:", sorted(set(n5) & set(nr)) or "none", "| U6 ∩ rest:", sorted(set(n6) & set(nr)) or "none")

files = []
for dp, dn, fns in os.walk(WORK):
    if ".lake" in dp.split(os.sep):
        continue
    for fn in fns:
        if fn.endswith(".lean"):
            files.append(os.path.join(dp, fn))
print(f"work/lean: {len(files)} .lean files scanned (excluding .lake)")
work_index = collections.defaultdict(list)
for f in files:
    for full, ln, kind in index(f):
        work_index[full].append((os.path.relpath(f, WORK), ln, kind))
for tag, d in (("U5", n5), ("U6", n6)):
    clashes = [(n, work_index[n]) for n in d if n in work_index]
    print(f"(a) {tag} CLASHES (same fully-qualified name declared in work/lean): {len(clashes)}")
    for n, locs in clashes:
        print(f"    {n}  <-  {locs[:3]}")
# does work/lean already have anything in namespaces SM.FrontRows.U5 / U6 ?
for tag in ("U5", "U6"):
    hits = [n for n in work_index if n.startswith(f"SM.FrontRows.{tag}.")]
    print(f"    work/lean declarations already in namespace SM.FrontRows.{tag}: {len(hits)}")
# secondary: short-name occurrences in work/lean of the new blocks' short names (informational; different namespaces)
short_work = collections.defaultdict(list)
for full, locs in work_index.items():
    short_work[full.split(".")[-1]].extend([(full, l) for l in locs])
for tag, d in (("U5", n5), ("U6", n6)):
    sh = collections.Counter(n.split(".")[-1] for n in d)
    same = sorted(s for s in sh if s in short_work)
    print(f"secondary: {tag} short names that also exist (in another namespace) in work/lean: {len(same)} of {len(sh)}")
    print("    e.g.", same[:40])
os.makedirs("/tmp/lean_merge3", exist_ok=True)
with open("/tmp/lean_merge3/w3a_new_decls.txt", "w") as fh:
    for tag, d in (("U5", n5), ("U6", n6)):
        for full, v in d.items():
            for ln, kind in v:
                fh.write(f"{tag}\t{ln}\t{kind}\t{full}\n")
print("full declaration list of the new blocks: /tmp/lean_merge3/w3a_new_decls.txt")
