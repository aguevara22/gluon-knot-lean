#!/usr/bin/env python3
"""clash_scan.py — namespace-aware name-clash scan of the NEW declarations of an assembled corner-chain file
(everything not declared by Statements_FINAL.lean) against every .lean file of work/lean (`.lake` excluded).
Full names are computed by tracking `namespace X … end X` (dotted namespaces split; sections ignored; lines
inside block comments skipped).  Reports: full-name clashes (fatal at port), duplicated names inside the
assembled file, short-name coincidences in DIFFERENT namespaces (informational), and prefix statistics.
Usage: python3 tools/clash_scan.py [Wave2a_Assembled.lean]"""
import sys, pathlib, re, collections, json
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from wave2a_assemble import collect_decls
CORNER = pathlib.Path(__file__).resolve().parent.parent
LIB = CORNER.parent.parent / "lean"
asm = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else CORNER / "Wave2a_Assembled.lean")
base_decls, _ = collect_decls((CORNER / "Statements_FINAL.lean").read_text().split("\n"))
asm_decls, asm_order = collect_decls(asm.read_text().split("\n"))
new = {n: k for n, k in asm_order if n not in base_decls}
dups = [n for n, t in asm_decls.items() if len(t) > 1]
lib = collections.defaultdict(list)   # full name -> [file:line]
files = [p for p in LIB.rglob("*.lean") if ".lake" not in p.parts]
for p in files:
    try:
        d, order = collect_decls(p.read_text(encoding="utf-8").split("\n"))
    except Exception as e:
        print("skip", p, e); continue
    for n, k in order:
        lib[n].append(f"{p.relative_to(LIB)}:{k + 1}")
full = {n: lib[n] for n in new if n in lib}
short_lib = collections.defaultdict(list)
for n, locs in lib.items():
    short_lib[n.split(".")[-1]].append(n)
short = {n: sorted(set(short_lib[n.split(".")[-1]])) for n in new if n.split(".")[-1] in short_lib}
pref = collections.Counter()
for n in new:
    s = n[3:] if n.startswith("SM.") else n
    m = re.match(r"(s7[a-z]_|sg[a-z]_|sft[a-z]_|cvl_)", s)
    pref[m.group(1) if m else ("nested:" + s.split(".")[0] if "." in s else "UNPREFIXED:" + s)] += 1
print(json.dumps({"assembled": asm.name, "lib_files": len(files), "lib_decls": len(lib), "new_decls": len(new),
                  "duplicates_in_assembled": dups, "full_name_clashes": full,
                  "short_name_coincidences_count": len(short),
                  "short_name_coincidences": short, "prefix_stats": pref}, indent=1, ensure_ascii=False))
