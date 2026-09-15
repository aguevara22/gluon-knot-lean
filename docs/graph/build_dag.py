#!/usr/bin/env python3
"""Extract the corner-laws dependency graph with per-row status and compute swim-lane layouts."""
import json, csv, re, subprocess, sys, collections
from pathlib import Path

import os
# Package root: $CORNER_LAWS_ROOT, else the package folder next to this repo's docs/graph/ directory.
ROOT = Path(os.environ.get("CORNER_LAWS_ROOT") or (Path(__file__).resolve().parents[2] / "CORNER_LAWS_FOCUSED_20260912"))
OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("dag_data.json")

rows = json.load(open(ROOT / "work/lean/lean-declarations.json"))["declarations"]
dep = json.load(open(ROOT / "blueprint/DEPENDENCIES.json"))
edges = {k: list(v) for k, v in dep["edges"].items()}
nodes_tsv = {r["id"]: r for r in csv.DictReader(open(ROOT / "blueprint/NODES.tsv"), delimiter="\t")}
policy = json.load(open(ROOT / "work/lean/axiom-policy.json"))
TARGETS = ["prop:C-chamber", "prop:C-silent", "thm:C-S3", "thm:C-S7", "thm:C-S5", "thm:C-soft", "cor:C-inherits", "SM:corner_laws_and_soft"]
LITERATURE = set(policy["literature"])
HYPOTHESES = {"hyp:R", "CV:ax:R"}

num, kind = {}, {}
out = subprocess.run(["python3", "tools/claims.py"], cwd=ROOT, capture_output=True, text=True).stdout
for m in re.finditer(r"^\| (\d+) \| (\w+) \| `([^`]+)` \| ([\w-]+) \|", out, re.M):
    num[m.group(3)] = int(m.group(1)); kind[m.group(3)] = m.group(4)

reason = {}
fr = (ROOT / "FINAL_REVIEW.md").read_text()
block = fr.split("<!-- BEGIN:PENDING -->")[1].split("<!-- END:PENDING -->")[0]
for m in re.finditer(r"^\| (\S+) \| `([^`]+)` \| [^|]* \| pending \| (.*?) \|\s*$", block, re.M):
    reason[m.group(2)] = m.group(3).strip()

def lane_of(r):
    i = r["id"]; src = r.get("source", "") or ""
    if i == "SM:corner_laws_and_soft" or i.startswith("Bridge:"): return "Bridge & final"
    if i.startswith("R:"): return "R assembly"
    if i.startswith("CV:"): return "CV lane"
    f = src.split("/")[-1]
    if f.startswith("sm-1"): return "SM 1 Polygons"
    if f.startswith("sm-2"): return "SM 2 Tree amplitude"
    if f.startswith("sm-3"):
        p = i.split(":")[0]
        if p in ("lp", "rp", "lc", "mp", "lit"): return "SM 3 Polynomial block"
        if p in ("ng", "fd", "ce", "cf", "cb", "cp", "src"): return "SM 3 Fronts & contact"
        return "SM 3 State sum"
    if f.startswith("sm-4"): return "SM 4 Wall laws of C"
    if f.startswith("sm-5"): return "SM 5 Transport"
    if f.startswith("sm-6"): return "SM 6 Comparison"
    return "other"

LANES = ["SM 1 Polygons", "SM 2 Tree amplitude", "SM 3 State sum", "SM 3 Polynomial block", "SM 3 Fronts & contact",
         "SM 4 Wall laws of C", "SM 5 Transport", "SM 6 Comparison", "CV lane", "R assembly", "Bridge & final"]

def short(i): return re.sub(r"^(CV|R|Bridge|SM):", "", i)

N = {}
for r in rows:
    i = r["id"]; t = nodes_tsv.get(i, {})
    src = r.get("source") or t.get("source") or ""
    line = r.get("line") or t.get("line") or ""
    N[i] = dict(id=i, short=short(i), num=num.get(i), kind=kind.get(i) or t.get("env") or ("obligation" if i.startswith(("R:", "Bridge:", "SM:")) else "row"),
                action=t.get("action") or ("AXIOM" if i in LITERATURE else "PROVE"),
                status=r["status"], lane=lane_of(r), src=(src.replace("reference/", "") + (":" + str(line) if line else "")) if src else "",
                decl=r.get("declaration") or "", module=r.get("module") or "", deps=edges.get(i, []),
                target=i in TARGETS, literature=i in LITERATURE, hypothesis=i in HYPOTHESES, reason=reason.get(i, ""))
for i in N:
    N[i]["dependents"] = sorted(j for j in N if i in N[j]["deps"])
pending = {i for i in N if N[i]["status"] != "accepted"}
for i in N:
    pd = [d for d in N[i]["deps"] if d in pending]
    N[i]["pending_deps"] = pd
    N[i]["root_cause"] = (i in pending) and not pd
def roots(i, seen=None):
    seen = seen if seen is not None else set()
    if N[i]["status"] == "accepted": return []
    if not N[i]["pending_deps"]: return [i]
    out = []
    for d in N[i]["pending_deps"]:
        if d not in seen:
            seen.add(d); out += roots(d, seen)
    return sorted(set(out))
ROOT_TAG = {"cp:finite-contact-path": "GAP-2 origin: proved modulo AmbientIsotopyDescent",
            "lem:gauss-two-discs": "deferred: PL Schoenflies, 12-20k lines",
            "src:contact": "never declared (5th literature interface)"}
for i in N:
    n = N[i]
    if n["status"] == "accepted":
        n["tag"] = "literature axiom" if n["literature"] else ("hypothesis (Prop)" if n["hypothesis"] else "accepted")
    elif i in ROOT_TAG: n["tag"] = ROOT_TAG[i]
    elif i == "CV:ax:etnyre": n["tag"] = "needs src:contact; no sl object"
    else:
        pdn = [short(d) for d in n["pending_deps"]]
        n["tag"] = "blocked via " + ", ".join(pdn[:3]) + (" +%d" % (len(pdn) - 3) if len(pdn) > 3 else "")
    n["roots"] = roots(i)

print("pending:", len(pending), "| root causes:", sorted(i for i in pending if N[i]["root_cause"]))
print("roots of final:", N["SM:corner_laws_and_soft"]["roots"], "| of C-S7:", N["thm:C-S7"]["roots"], "| of 155:", N["CV:thm:carrierfloor"]["roots"])

def order_cells(ids, lane_fn, lanes):
    ids = list(ids); S = set(ids)
    cons = {i: [j for j in N[i]["dependents"] if j in S] for i in ids}
    h = {}
    def H(v):
        if v in h: return h[v]
        h[v] = 0 if not cons[v] else 1 + max(H(u) for u in cons[v]); return h[v]
    for v in ids: H(v)
    maxh = max(h.values()); layer = {v: maxh - h[v] for v in ids}; nl = maxh + 1
    cell = collections.defaultdict(list)
    for v in ids: cell[(lane_fn(v), layer[v])].append(v)
    for k in cell: cell[k].sort(key=lambda v: (N[v]["num"] or 999, v))
    lane_idx = {l: k for k, l in enumerate(lanes)}
    nbr = {v: [d for d in N[v]["deps"] if d in S] + cons[v] for v in ids}
    for sweep in range(8):
        y = {}
        for (l, L), vs in cell.items():
            for k, v in enumerate(vs): y[v] = lane_idx[l] * 1000 + k * (1000 / (len(vs) + 1))
        for k, vs in cell.items():
            vs.sort(key=lambda v: ((sum(y[n] for n in nbr[v]) / len(nbr[v])) if nbr[v] else y[v], N[v]["num"] or 999))
    return cell, nl, layer

def place_horizontal(cell, nl, lanes, pitch=26, layer_gap=210, lane_pad=18, node_h=22, char_w=6.7, min_w=70, x0=150):
    lane_rows = {l: max([len(cell[(l, L)]) for L in range(nl) if (l, L) in cell] or [1]) for l in lanes}
    ytop = {}; y0 = 0; boxes = []
    for l in lanes:
        hgt = lane_rows[l] * pitch + 2 * lane_pad
        ytop[l] = y0; boxes.append(dict(name=l, y=y0, h=hgt)); y0 += hgt
    pos = {}
    for (l, L), vs in cell.items():
        band_h = lane_rows[l] * pitch
        start = ytop[l] + lane_pad + (band_h - len(vs) * pitch) / 2
        for k, v in enumerate(vs):
            w = max(min_w, int(len(v) * char_w) + 16)
            pos[v] = dict(x=x0 + L * layer_gap, y=round(start + k * pitch + (pitch - node_h) / 2, 1), w=w, h=node_h, layer=L)
    return pos, boxes, dict(layers=nl, width=x0 + nl * layer_gap + 20, height=y0)

def place_vertical(cell, nl, lanes, col_w=206, node_w=188, node_h=40, row_pitch=50, row_pad=16, top=34, x0=8):
    row_n = {L: max([len(cell[(l, L)]) for l in lanes if (l, L) in cell] or [1]) for L in range(nl)}
    rtop = {}; y0 = top; rows_ = []
    for L in range(nl):
        hgt = row_n[L] * row_pitch + 2 * row_pad - (row_pitch - node_h)
        rtop[L] = y0; rows_.append(dict(layer=L, y=y0, h=hgt)); y0 += hgt
    cols = [dict(name=l, x=x0 + k * col_w, w=col_w) for k, l in enumerate(lanes)]
    lane_x = {l: x0 + k * col_w for k, l in enumerate(lanes)}
    pos = {}
    for (l, L), vs in cell.items():
        for k, v in enumerate(vs):
            pos[v] = dict(x=lane_x[l] + (col_w - node_w) / 2, y=rtop[L] + row_pad + k * row_pitch, w=node_w, h=node_h, layer=L)
    return pos, cols, rows_, dict(layers=nl, width=x0 * 2 + len(lanes) * col_w, height=y0 + 8)

cell, nl, layer = order_cells(N.keys(), lambda v: N[v]["lane"], LANES)
pos, lane_boxes, meta = place_horizontal(cell, nl, LANES)
print("full layout:", meta)

crit_ids = set(pending) | set(TARGETS) | {"lit:homfly", "hyp:R", "CV:ax:R"}
def crit_lane(v):
    if v in ("lit:homfly", "src:contact", "lem:gauss-two-discs"): return "Inputs"
    if v.startswith("CV:"): return "CV lane"
    if v.startswith("R:"): return "R assembly"
    if v.startswith("Bridge:") or v == "SM:corner_laws_and_soft": return "Bridge & final"
    if N[v]["lane"].startswith("SM 3"): return "SM 3 contact & floor"
    return "SM 4-6 laws of C"
CLANES = ["Inputs", "SM 3 contact & floor", "SM 4-6 laws of C", "CV lane", "R assembly", "Bridge & final"]
ccell, cnl, clayer = order_cells(crit_ids, crit_lane, CLANES)
cpos, ccols, crows, cmeta = place_vertical(ccell, cnl, CLANES)
cpos["lem:gauss-two-discs"]["y"] = cpos["fd:contact"]["y"]  # isolated row: show it with the inputs, not as a sink
cedges = sorted((d, v) for v in crit_ids for d in N[v]["deps"] if d in crit_ids)
print("critical:", len(crit_ids), "nodes", len(cedges), "edges", cmeta)
for L in range(cnl):
    print("  row", L, {l: ccell[(l, L)] for l in CLANES if (l, L) in ccell})

data = dict(nodes=N, lanes=LANES, laneBoxes=lane_boxes, pos=pos, meta=meta,
            crit=dict(ids=sorted(crit_ids), pos=cpos, cols=ccols, rows=crows, meta=cmeta, edges=cedges),
            edges=sorted((d, v) for v in N for d in N[v]["deps"]),
            stats=dict(accepted=sum(1 for i in N if N[i]["status"] == "accepted"), pending=len(pending), total=len(N),
                       claims_verified=109, claims_total=132, targets_accepted=sum(1 for t in TARGETS if N[t]["status"] == "accepted"), targets_total=8))
OUT.write_text(json.dumps(data))
print("wrote", OUT, OUT.stat().st_size, "bytes")
