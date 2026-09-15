#!/usr/bin/env python3
"""Namespace-aware clash scan for the last frontrows delta (A) FrontRows_W3b_Delta.lean and (B) NgBound_Final.lean.
Usage: python3 clash_scan_w3b.py [A|B]   (default: both).  Index the module's fully-qualified top-level declaration names
and intersect them with every .lean under work/lean (excluding .lake), explicitly with the three ported modules
SM/FrontRowsW2.lean, SM/FrontRowsW2S.lean, SM/FrontRowsW3.lean, and for (B) also with (A) (which it imports); scan the
module's global (non-local, non-scoped) syntax extensions against work/lean.  Writes /tmp/w3b/<A|B>_decls.txt."""
import re, os, sys, collections
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912"
FR = f"{ROOT}/work/drafts/frontrows"
WORK = f"{ROOT}/work/lean"
MODS = {"A": f"{FR}/FrontRows_W3b_Delta.lean", "B": f"{FR}/NgBound_Final.lean"}

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|macro_rules|notation|syntax|elab|macro)\s+'
                  r'(?:\{[^}]*\}\s*)?([^\s:({\[⟨]+)')
NS = re.compile(r'^\s*namespace\s+([^\s]+)')
SEC = re.compile(r'^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$')
END = re.compile(r'^\s*end(?:\s+([^\s]+))?\s*$')

def index(path):
    out = []; stack = []; in_block_comment = 0
    try:
        lines = open(path, encoding="utf-8").read().split("\n")
    except Exception:
        return out
    for i, raw in enumerate(lines, 1):
        line = raw
        if in_block_comment:
            if "-/" in line:
                in_block_comment = max(0, in_block_comment - line.count("-/")); line = line.split("-/")[-1]
            else:
                continue
        if "/-" in line:
            opens = line.count("/-"); closes = line.count("-/")
            if opens > closes:
                in_block_comment += opens - closes; line = line.split("/-")[0]
            else:
                line = re.sub(r'/-.*?-/', '', line)
        line = line.split("--")[0]
        if not line.strip():
            continue
        m = NS.match(line)
        if m: stack.append(('ns', m.group(1))); continue
        m = SEC.match(line)
        if m: stack.append(('sec', m.group(1))); continue
        m = END.match(line)
        if m:
            if stack: stack.pop()
            continue
        m = DECL.match(line)
        if m:
            kind, name = m.group(1), m.group(2)
            if kind == "instance" and (name.startswith(":") or name[0] == "["): continue
            if kind in ("macro_rules", "notation", "syntax", "elab", "macro"): continue
            ns = ".".join(nm for k, nm in stack if k == 'ns')
            full = f"{ns}.{name}" if ns and not name.startswith("_root_") else name.replace("_root_.", "")
            out.append((full, i, kind))
    return out

MACRO = re.compile(r'^\s*(local\s+|scoped\s+)?(macro|syntax|notation|infix|infixl|infixr|prefix|postfix)\s+(?:\(.*?\)\s*)?"([^"]+)"')
def macros(path):
    out = []
    for i, l in enumerate(open(path, encoding="utf-8").read().split("\n"), 1):
        m = MACRO.match(l)
        if m and not m.group(1): out.append((m.group(3), i, m.group(2)))
    return out

files = []
for dp, dn, fns in os.walk(WORK):
    if ".lake" in dp.split(os.sep): continue
    for fn in fns:
        if fn.endswith(".lean"): files.append(os.path.join(dp, fn))
work_index = collections.defaultdict(list)
for f in files:
    for full, ln, kind in index(f):
        work_index[full].append((os.path.relpath(f, WORK), ln, kind))
print(f"work/lean: {len(files)} .lean files indexed (excluding .lake), {len(work_index)} distinct full names")

which = sys.argv[1:] or ["A", "B"]
total_clashes = 0
for tag in which:
    path = MODS[tag]
    decls = index(path)
    names = collections.OrderedDict()
    for full, ln, kind in decls: names.setdefault(full, []).append((ln, kind))
    print(f"\n===== ({tag}) {os.path.relpath(path, ROOT)}: {len(decls)} top-level declarations, {len(names)} distinct full names")
    dups = {k: v for k, v in names.items() if len(v) > 1}
    if dups: print("  duplicate full names inside the module:", dups)
    clashes = [(nm, work_index[nm]) for nm in names if nm in work_index]
    total_clashes += len(clashes)
    print(f"  CLASHES with work/lean (same fully-qualified name): {len(clashes)}")
    for nm, locs in clashes: print(f"    {nm}  <-  {locs[:3]}")
    for mod in ("SM/FrontRowsW2.lean", "SM/FrontRowsW2S.lean", "SM/FrontRowsW3.lean"):
        modnames = {full for full, ln, kind in index(os.path.join(WORK, mod))}
        inter = sorted(nm for nm in names if nm in modnames)
        print(f"  explicit intersection with {mod} ({len(modnames)} declarations): {len(inter)} {inter[:5]}")
    if tag == "B":
        anames = {full for full, ln, kind in index(MODS["A"])}
        inter = sorted(nm for nm in names if nm in anames)
        total_clashes += len(inter)
        print(f"  explicit intersection with (A) FrontRows_W3b_Delta.lean ({len(anames)} declarations): {len(inter)} {inter[:5]}")
    dm = macros(path)
    print(f"  global syntax extensions declared by the module: {[(t, ln) for t, ln, k in dm]}")
    tokens = {t for t, ln, k in dm}
    hits = [(t, os.path.relpath(f, WORK), ln) for f in files for t, ln, k in macros(f) if t in tokens]
    if tag == "B": hits += [(t, "(A)", ln) for t, ln, k in macros(MODS["A"]) if t in tokens]
    total_clashes += len(hits)
    print(f"  same token declared globally elsewhere (work/lean{' + (A)' if tag == 'B' else ''}): {len(hits)} {hits}")
    keys = ["typeII_move", "P_typeII", "ng_front_II", "certificate_laws", "word_bound", "ng_local_front_bound", "typeII_b", "typeII_d",
            "typeII_move_proof", "fd_ng_bound", "fd_ng_bound_of", "NgBoundClauses", "degAZ_P_isMaxDegA", "dOf_eq_degAZ", "defect_nonneg", "of_defect_nonneg"]
    short_index = collections.defaultdict(list)
    for full, locs in work_index.items(): short_index[full.split(".")[-1]].extend([(full, l) for l in locs])
    print("  secondary: short-name declarations in work/lean (any namespace) for the module's row-level names:")
    for k in keys:
        h = short_index.get(k, [])
        if any(nm.split(".")[-1] == k for nm in names):
            print(f"    {k}: {len(h)} -> {[(x[0], x[1][0], x[1][1]) for x in h[:4]]}")
    nss = collections.Counter(nm.rsplit(".", 1)[0] if "." in nm else "(root)" for nm in names)
    print("  namespaces (count of declarations): " + ", ".join(f"{ns}: {c}" for ns, c in sorted(nss.items(), key=lambda x: -x[1])[:12]))
    with open(f"/tmp/w3b/{tag}_decls.txt", "w") as fh:
        for full, v in names.items():
            for ln, kind in v: fh.write(f"{ln}\t{kind}\t{full}\n")
    print(f"  full declaration list: /tmp/w3b/{tag}_decls.txt")
print(f"\nTOTAL CLASHES: {total_clashes}")
