#!/usr/bin/env python3
"""Namespace-aware scan of work/lean for declarations whose fully-qualified name (or whose short
name inside namespace SM) coincides with a declaration of RPC_Assembled.lean."""
import re, os, sys, collections
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/lean"
names = [l.strip() for l in open("/tmp/rpc_axioms/names.txt") if l.strip()]
decl_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)")
priv_re = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?private\b")
ns_re = re.compile(r"^namespace\s+(\S+)")
sec_re = re.compile(r"^(?:noncomputable\s+)?section\b(?:\s+(\S+))?")
end_re = re.compile(r"^end\b(?:\s+(\S+))?")
index = collections.defaultdict(list)  # fq name -> [(file, line)]
for dp, dn, fn in os.walk(ROOT):
    if ".lake" in dp: continue
    for f in fn:
        if not f.endswith(".lean"): continue
        path = os.path.join(dp, f)
        stack = []  # entries: ("ns", name) or ("sec", name|None)
        for i, ln in enumerate(open(path, encoding="utf-8", errors="replace"), start=1):
            m = ns_re.match(ln)
            if m: stack.append(("ns", m.group(1))); continue
            m = sec_re.match(ln)
            if m and not ln.lstrip().startswith("--"): stack.append(("sec", m.group(1))); continue
            m = end_re.match(ln)
            if m:
                if stack: stack.pop()
                continue
            m = decl_re.match(ln)
            if m and not priv_re.match(ln):
                kind, short = m.groups()
                if kind == "instance" and not re.match(r"[A-Za-z_]", short): continue
                ns = ".".join(n for k, n in stack if k == "ns")
                if short.startswith("_root_."):
                    fq = short[len("_root_."):]
                else:
                    fq = f"{ns}.{short}" if ns else short
                index[fq].append((os.path.relpath(path, ROOT), i))
print(f"indexed {sum(len(v) for v in index.values())} declarations in work/lean")
exact = []; shadow = []
for n in names:
    if n in index: exact.append((n, index[n]))
    parts = n.split(".")
    short = parts[-1]
    # shadows: same short name in an enclosing namespace (SM.x for SM.RPC.x) or in root
    for enc in [".".join(parts[:k] + [short]) for k in range(len(parts) - 1)]:
        if enc != n and enc in index: shadow.append((n, enc, index[enc]))
print("\nEXACT fully-qualified clashes:", len(exact))
for n, locs in exact: print("  ", n, locs[:3])
print("\nShort-name shadows in enclosing namespaces (ambiguity risk if co-imported):", len(shadow))
for n, enc, locs in shadow: print("  ", n, "vs", enc, locs[:3])
# also: existing declarations in namespace SM.RPC at all?
rpc = sorted(k for k in index if k.startswith("SM.RPC."))
print("\nexisting SM.RPC.* declarations in work/lean:", len(rpc), rpc[:10])
