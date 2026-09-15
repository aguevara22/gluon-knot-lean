#!/usr/bin/env python3
"""Namespace-aware scan of work/lean for declarations whose fully-qualified name coincides with a
declaration of TN_Assembled.lean, or whose short name sits in an enclosing namespace (ambiguity
risk once co-imported).  Names of the assembled file are computed here, tracking namespace /
section / end, exactly as for work/lean."""
import re, os, collections
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/lean"
ASM = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/fd/TN_Assembled.lean"
decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)")
priv_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?private\b")
ns_re = re.compile(r"^namespace\s+(\S+)")
sec_re = re.compile(r"^(?:noncomputable\s+)?section\b(?:\s+(\S+))?")
end_re = re.compile(r"^end\b(?:\s+(\S+))?")


def index_file(path):
    out = []  # (fq, line, kind)
    stack = []
    in_block_comment = 0
    for i, ln in enumerate(open(path, encoding="utf-8", errors="replace"), start=1):
        # crude block-comment tracking so `section`/`end` inside docstrings are not counted
        opens = ln.count("/-"); closes = ln.count("-/")
        if in_block_comment:
            in_block_comment += opens - closes
            continue
        if opens > closes:
            in_block_comment = opens - closes
            continue
        m = ns_re.match(ln)
        if m: stack.append(("ns", m.group(1))); continue
        m = sec_re.match(ln)
        if m: stack.append(("sec", m.group(1))); continue
        m = end_re.match(ln)
        if m:
            if stack: stack.pop()
            continue
        m = decl_re.match(ln)
        if m and not priv_re.match(ln):
            kind, short = m.groups()
            if kind == "instance" and not re.match(r"[A-Za-z_]", short): continue
            ns = ".".join(n for k, n in stack if k == "ns")
            fq = short[len("_root_."):] if short.startswith("_root_.") else (f"{ns}.{short}" if ns else short)
            out.append((fq, i, kind))
    return out


asm = index_file(ASM)
names = [fq for fq, _, _ in asm]
print(f"TN_Assembled.lean: {len(names)} top-level declarations; "
      f"{sum(1 for n in names if n.startswith('SM.TransverseNeighborhood.'))} in SM.TransverseNeighborhood, "
      f"{sum(1 for n in names if not n.startswith('SM.TransverseNeighborhood.'))} directly in SM: "
      + ", ".join(n for n in names if not n.startswith('SM.TransverseNeighborhood.')))
dups = [n for n, c in collections.Counter(names).items() if c > 1]
print("duplicate names inside the assembled file:", dups)

index = collections.defaultdict(list)
nfiles = 0
for dp, dn, fn in os.walk(ROOT):
    if ".lake" in dp: continue
    for f in fn:
        if not f.endswith(".lean"): continue
        nfiles += 1
        path = os.path.join(dp, f)
        for fq, i, kind in index_file(path):
            index[fq].append((os.path.relpath(path, ROOT), i))
print(f"indexed {sum(len(v) for v in index.values())} declarations in {nfiles} files under work/lean")

exact = []; shadow = []; short_same = []
for n in names:
    if n in index: exact.append((n, index[n]))
    parts = n.split("."); short = parts[-1]
    for enc in [".".join(parts[:k] + [short]) for k in range(len(parts) - 1)]:
        if enc != n and enc in index: shadow.append((n, enc, index[enc]))
    # informational: same short name anywhere else (unrelated namespaces)
    for fq in index:
        if fq.split(".")[-1] == short and fq != n and fq not in [e for _, e, _ in shadow]:
            short_same.append((n, fq, index[fq][0]))
print("\nEXACT fully-qualified clashes:", len(exact))
for n, locs in exact: print("  ", n, locs[:3])
print("\nShort-name shadows in enclosing namespaces (SM.x or root x for SM.TransverseNeighborhood.x):", len(shadow))
for n, enc, locs in shadow: print("  ", n, "vs", enc, locs[:3])
tn = sorted(k for k in index if k.startswith("SM.TransverseNeighborhood"))
print("\nexisting SM.TransverseNeighborhood* declarations in work/lean:", len(tn), tn[:10])
print("\nInformational: same short name in an unrelated namespace (no ambiguity):", len(short_same))
for n, fq, loc in short_same[:40]: print("  ", n, "~", fq, loc)
# sanity: names this file relies on from work/lean
for probe in ["SM.ContactMotions.IsGlobalFlow", "SM.ContactMotions.contDiff_uncurry", "SM.ContactMotions.exists_isGlobalFlow",
              "SM.ContactMotions.globalFlow", "SM.ContactMotions.ODE_unique_global"]:
    print("  sanity", probe, "found" if probe in index else "ABSENT")
