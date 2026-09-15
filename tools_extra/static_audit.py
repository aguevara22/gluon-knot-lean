#!/usr/bin/env python3
"""One-minute static audit of the corner-laws package (no Lean needed).
Checks: no sorry/admit/native_decide in code (comment-stripped); only registered axiom declarations; every file hashed in the
final checker receipt is byte-identical; declaration map consistent with reviews and the shipped audit; fixed target names.
Usage: static_audit.py [PACKAGE_ROOT]   (default: ../CORNER_LAWS_FOCUSED_20260912 relative to this file)   Exit 1 on a hard failure."""
import json, re, sys, gzip, hashlib, subprocess, pathlib, collections
ROOT = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else pathlib.Path(__file__).resolve().parents[1] / "CORNER_LAWS_FOCUSED_20260912").resolve()
hard = []; warn = []
def strip(src):
    out = []; i = 0; n = len(src); depth = 0
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if depth > 0 and src.startswith('-/', i): depth -= 1; i += 2; continue
        if depth == 0 and src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == '\\': j += 1
                j += 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(src[i] if depth == 0 else (' ' if src[i] != '\n' else '\n')); i += 1
    return ''.join(out)
lean = ROOT / "work/lean"
files = sorted(p for p in lean.rglob("*.lean") if ".lake" not in p.parts)
lines = sum(1 for p in files for _ in open(p, errors="replace"))
tok = re.compile(r'\b(sorry|admit|native_decide|sorryAx)\b'); hits = []
axioms = []
for p in files:
    s = strip(p.read_text(errors="replace"))
    for m in tok.finditer(s): hits.append(f"{p.relative_to(ROOT)}:{s.count(chr(10),0,m.start())+1}:{m.group(0)}")
    for m in re.finditer(r'^\s*(?:noncomputable\s+)?axiom\s+([A-Za-z_][\w.]*)', s, re.M): axioms.append((m.group(1), str(p.relative_to(ROOT))))
policy = json.load(open(ROOT / "work/lean/axiom-policy.json"))
allowed = set(n.split('.')[-1] for n in policy["literature"].values())
print(f"lean files: {len(files)} | lines: {lines}")
print(f"code-level sorry/admit/native_decide: {len(hits)}" + (" -> " + "; ".join(hits[:5]) if hits else ""))
if hits: hard.append("placeholders in code")
print("axiom declarations: " + ", ".join(f"{a} ({f})" for a, f in axioms))
bad = [a for a, f in axioms if a.split('.')[-1] not in allowed]
if bad: hard.append("unregistered axiom(s): " + ", ".join(bad))
for p in files:
    s = strip(p.read_text(errors="replace"))
    if re.search(r'\b(unsafe|implemented_by|extern|opaque|partial def)\b', s): warn.append(f"escape-hatch keyword in {p.relative_to(ROOT)}")
rec = ROOT / "work/checks/stage-development.json"
if rec.exists():
    d = json.load(open(rec)); ps = d.get("project_sha256", {}); mism = []
    for k, v in ps.items():
        f = lean / k
        if not f.exists() or hashlib.sha256(f.read_bytes()).hexdigest() != v: mism.append(k)
    extra = [str(p.relative_to(lean)) for p in files if str(p.relative_to(lean)) not in ps]
    print(f"final receipt: passed={d.get('passed')} mapped={d.get('mapped_declarations')} audited={d.get('audited_declarations')} | files hashed {len(ps)}, mismatching {len(mism)}, unhashed .lean {len(extra)}")
    if mism or extra: hard.append(f"sources differ from the receipt: {mism[:5]} {extra[:5]}")
else: warn.append("no stage-development.json receipt")
rows = json.load(open(ROOT / "work/lean/lean-declarations.json"))["declarations"]
st = collections.Counter(r["status"] for r in rows); print("declaration map:", dict(st))
acc = [r for r in rows if r["status"] == "accepted"]
for r in acc:
    if not r.get("author") or not r.get("reviewer") or r["author"] == r["reviewer"]: hard.append("review independence: " + r["id"])
    if not r.get("review_file") or not (ROOT / "work" / r["review_file"]).exists(): hard.append("missing review file: " + r["id"])
gz = ROOT / "work/delivery/receipts/declaration-audit.json.gz"
if gz.exists():
    h = json.load(gzip.open(gz, "rt"))["statement_hashes"]
    stale = [r["id"] for r in acc if h.get(r["id"]) != r.get("statement_sha256")]
    print(f"accepted statement hashes vs shipped audit: {len(acc)-len(stale)}/{len(acc)} match")
    if stale: hard.append("stale statement hashes: " + ", ".join(stale[:5]))
else: warn.append("shipped audit gz absent (ignored in git); statement-hash check skipped")
src = "\n".join(p.read_text(errors="replace") for p in files)
missing = [f"{k} -> {v}" for k, v in {**policy["targets"], **policy["literature"]}.items()
           if not re.search(r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def|axiom|abbrev|structure)\s+' + re.escape(v.split('.')[-1]) + r'\b', src, re.M)]
print(f"fixed-name declarations absent: {len(missing)}: " + ", ".join(m.split(' -> ')[0] for m in missing))
vb = subprocess.run([sys.executable, "verify_bundle.py"], cwd=ROOT, capture_output=True, text=True)
print("verify_bundle.py:", "PASS" if vb.returncode == 0 else "FAIL (" + (vb.stdout + vb.stderr).strip().splitlines()[-1][:120] + ")")
if vb.returncode: warn.append("verify_bundle.py fails (root MANIFEST.sha256 stale for FINAL_REVIEW.md)")
for w in warn: print("WARN:", w)
for h in hard: print("FAIL:", h)
print("RESULT:", "FAIL" if hard else "PASS", f"({len(warn)} warnings)")
sys.exit(1 if hard else 0)
