#!/usr/bin/env python3
"""Namespace-aware index (frontrows wave-2 clean module; rerun: python3 clash_scan_w2.py) of top-level declaration names; intersect the clean module's names with work/lean."""
import re, os, sys, collections
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912"
CLEAN = f"{ROOT}/work/drafts/frontrows/FrontRows_W2_Clean.lean"
WORK = f"{ROOT}/work/lean"

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|macro_rules|notation|syntax|elab|macro)\s+'
                  r'(?:\{[^}]*\}\s*)?([^\s:({\[⟨]+)')
NS = re.compile(r'^\s*namespace\s+([^\s]+)')
SEC = re.compile(r'^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$')
END = re.compile(r'^\s*end(?:\s+([^\s]+))?\s*$')

def index(path):
    out = []  # (fullname, line, kind)
    stack = []  # entries: ('ns', name) or ('sec', name or None)
    in_block_comment = 0
    try:
        lines = open(path, encoding="utf-8").read().split("\n")
    except Exception as e:
        return out
    for i, raw in enumerate(lines, 1):
        line = raw
        # crude block-comment tracking (/- ... -/), handles docstrings spanning lines
        if in_block_comment:
            if "-/" in line:
                in_block_comment = max(0, in_block_comment - line.count("-/"))
                line = line.split("-/")[-1]
            else:
                continue
        if "/-" in line:
            # strip from first /- if it is not closed on the same line
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
            if kind in ("instance",) and (name.startswith(":") or name[0] == "["):
                continue
            if kind in ("macro_rules", "notation", "syntax", "elab", "macro"):
                continue
            ns = ".".join(n for k, n in stack if k == 'ns')
            full = f"{ns}.{name}" if ns and not name.startswith("_root_") else name.replace("_root_.", "")
            out.append((full, i, kind))
    return out

clean = index(CLEAN)
clean_names = collections.OrderedDict()
for full, ln, kind in clean:
    clean_names.setdefault(full, []).append((ln, kind))
print(f"clean module: {len(clean)} top-level declarations, {len(clean_names)} distinct full names")
dups = {k: v for k, v in clean_names.items() if len(v) > 1}
if dups:
    print("  duplicate full names inside the clean module (overloads/instances?):", dups)

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
clashes = [(n, work_index[n]) for n in clean_names if n in work_index]
print(f"CLASHES (same fully-qualified name declared in work/lean): {len(clashes)}")
for n, locs in clashes:
    print(f"  {n}  <-  {locs[:3]}")

# secondary: short-name occurrences of the row-level names anywhere in work/lean
keys = ["ng_circle", "ng_cusp_skein", "ng_cusp_skein_both", "NgCircleClauses", "NgCuspSkeinClauses",
        "NonsingularDeformation", "SkeinSite", "skein_site", "skein_unique", "base_defect_nonneg",
        "P_circleDeletion", "P_comm", "P_zigzag", "delta_ne_zero", "degAZ_delta", "degAZ_delta_pow",
        "skein_ineq_forward", "skein_ineq_backward", "comm_counts", "skein_counts", "deform_P",
        "defect_eq_zero", "downCount_eq_c_general", "source_ne_nil"]
print("\nsecondary: short-name declarations in work/lean (any namespace) for row-level names:")
short_index = collections.defaultdict(list)
for full, locs in work_index.items():
    short_index[full.split(".")[-1]].extend([(full, l) for l in locs])
for k in keys:
    hits = short_index.get(k, [])
    print(f"  {k}: {len(hits)} -> {[(h[0], h[1][0], h[1][1]) for h in hits[:4]]}")

# also list the clean module's namespaces used
nss = collections.Counter(n.rsplit(".", 1)[0] if "." in n else "(root)" for n in clean_names)
print("\nnamespaces in the clean module (count of declarations):")
for ns, c in sorted(nss.items(), key=lambda x: -x[1])[:25]:
    print(f"  {ns}: {c}")
# dump the full list for the report
with open("/tmp/w2clean/clean_decls.txt", "w") as fh:
    for full, v in clean_names.items():
        for ln, kind in v:
            fh.write(f"{ln}\t{kind}\t{full}\n")
print("\nfull declaration list: /tmp/w2clean/clean_decls.txt")
