#!/usr/bin/env python3
"""port_clash_scan.py — comparison lane: namespace-aware clash scan of EVERY declaration of the port modules against work/lean
(SM, CV, RProof, Bridge, Supplemental; `.lake` excluded), plus the task's raw word-grep over
work/lean/{SM,CV,RProof,Bridge} for the SM-level short names (declaration lines only are counted as clashes;
other hits are uses of same-named declarations in other namespaces or local binders and are listed as informational).
Usage: python3 port_clash_scan.py [--json]"""
import collections, json, pathlib, re, subprocess, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from port_stmt_check import scan, MODULES, PORT, DECL_RE

LIB = PORT.parent.parent.parent / "lean"
port = []
for m in MODULES:
    port.extend(scan(PORT / "SM" / f"{m}.lean"))
names = [d["name"] for d in port if d["kind"] != "example"]
lib = collections.defaultdict(list)
files = [p for p in LIB.rglob("*.lean") if ".lake" not in p.parts]
for p in files:
    for d in scan(p, warn=False):
        if d["kind"] != "example":
            lib[d["name"]].append(f"{p.relative_to(LIB)}:{d['line']}")
full = {n: lib[n] for n in names if n in lib}
short_lib = collections.defaultdict(set)
for n in lib:
    short_lib[n.split(".")[-1]].add(n)
short = {n: sorted(short_lib[n.split(".")[-1]]) for n in names if n.split(".")[-1] in short_lib}
# raw grep (task letter): SM-level short names, word-bounded, over work/lean/{SM,CV,RProof,Bridge}
sm_level = sorted({n[3:] for n in names if n.startswith("SM.") and n.count(".") == 1})
hits = collections.defaultdict(list)
CH = 60
for i in range(0, len(sm_level), CH):
    chunk = sm_level[i:i + CH]
    pat = r"\b(" + "|".join(re.escape(x) for x in chunk) + r")\b"
    p = subprocess.run(["grep", "-rnwoE", pat, "SM", "CV", "RProof", "Bridge", "--include=*.lean"],
                       cwd=LIB, capture_output=True, text=True)
    for line in p.stdout.splitlines():
        f, ln, word = line.split(":", 2)
        hits[word].append(f"{f}:{ln}")
decl_hits = {}
for word, locs in hits.items():
    dl = []
    for loc in locs:
        f, ln = loc.rsplit(":", 1)
        text = (LIB / f).read_text(encoding="utf-8").split("\n")[int(ln) - 1]
        m = DECL_RE.match(text)
        if m and m.group(2) == word:
            dl.append(loc)
    if dl:
        decl_hits[word] = dl
out = {"lib_files": len(files), "lib_decls": len(lib), "port_decls": len(names),
       "sm_level_names": len(sm_level), "full_name_clashes": full,
       "short_name_coincidences_count": len(short), "short_name_coincidences": short,
       "raw_grep_words_hit": len(hits), "raw_grep_hits_total": sum(len(v) for v in hits.values()),
       "raw_grep_declaration_line_hits": decl_hits,
       "raw_grep_hits": {w: locs[:6] + ([f"… +{len(locs) - 6}"] if len(locs) > 6 else []) for w, locs in sorted(hits.items())}}
print(json.dumps(out, indent=1, ensure_ascii=False))
