#!/usr/bin/env python3
"""Render static SVGs (and a Mermaid block) of the proof graph from dag_data.json, for the README.
Usage: render_svg.py dag_data.json OUTDIR   -> OUTDIR/proof-graph-full.svg, proof-graph-critical.svg, critical.mmd
Literal colours (no CSS variables): these files are viewed as plain images."""
import json, sys, re
from pathlib import Path
from xml.sax.saxutils import escape as esc

D = json.load(open(sys.argv[1])); OUT = Path(sys.argv[2]); OUT.mkdir(parents=True, exist_ok=True)
N = D["nodes"]
C = dict(bg="#F2F3F6", bg2="#E9EBF0", surface="#FFFFFF", ink="#181B22", muted="#5C6473", line="#BFC5D0",
         ok="#2F8F5B", ok_soft="#E3F3EA", pend="#D07C1F", pend_soft="#FBEBD6", root="#C43D2F", root_soft="#F9DDD9",
         lit="#6E4FE0", lit_soft="#E7E0FB")
MONO = "ui-monospace, Menlo, Consolas, monospace"; SANS = "-apple-system, Segoe UI, Helvetica, Arial, sans-serif"

def style(n):
    if n["status"] == "accepted":
        return (C["lit"], C["lit_soft"], 1.6) if n["literature"] else (C["ok"], C["surface"], 1.4)
    if n["root_cause"]: return (C["root"], C["root_soft"], 2.2)
    return (C["pend"], C["pend_soft"], 1.6)

def node_svg(n, p, lines, font_px, bold_first):
    stroke, fill, sw = style(n)
    g = f'<g transform="translate({p["x"]},{p["y"]})">'
    if n["target"]:
        g += f'<rect x="-3" y="-3" width="{p["w"]+6}" height="{p["h"]+6}" rx="7" fill="none" stroke="{C["ink"]}" stroke-width="1" stroke-dasharray="3 2"/>'
    g += f'<rect width="{p["w"]}" height="{p["h"]}" rx="5" fill="{fill}" stroke="{stroke}" stroke-width="{sw + (1.0 if n["target"] else 0)}"/>'
    y = font_px + 4
    for k, (txt, fam, px, col) in enumerate(lines):
        w = "600" if (k == 0 and bold_first) else "400"
        g += f'<text x="9" y="{y}" font-family="{fam}" font-size="{px}" font-weight="{w}" fill="{col}">{esc(txt)}</text>'
        y += px + 4
    return g + "</g>"

# ---------- full graph, horizontal ----------
W, H = D["meta"]["width"], D["meta"]["height"]; TOP = 36
s = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H+TOP}" width="{W}" height="{H+TOP}" font-family="{SANS}">',
     f'<rect width="{W}" height="{H+TOP}" fill="{C["bg"]}"/>',
     f'<text x="12" y="22" font-size="15" font-weight="700" fill="{C["ink"]}">Corner laws proof graph: all 192 rows, prerequisites on the left, consumers on the right. '
     f'Green = accepted, orange = pending, red = pending root cause, violet = literature axiom, dashed ring = final target.</text>',
     f'<g transform="translate(0,{TOP})">']
lane_count = {}
for n in N.values():
    lane_count.setdefault(n["lane"], [0, 0]); lane_count[n["lane"]][1] += 1
    if n["status"] == "accepted": lane_count[n["lane"]][0] += 1
for i, b in enumerate(D["laneBoxes"]):
    a, t = lane_count.get(b["name"], (0, 0))
    s.append(f'<rect x="0" y="{b["y"]}" width="{W}" height="{b["h"]}" fill="{C["bg2"] if i % 2 else C["bg"]}"/>')
    s.append(f'<text x="12" y="{b["y"]+17}" font-size="13" font-weight="700" fill="{C["muted"]}">{esc(b["name"])}</text>')
    s.append(f'<text x="12" y="{b["y"]+31}" font-family="{MONO}" font-size="10.5" fill="{C["muted"]}">{a}/{t} accepted</text>')
def curve_h(a, b):
    x1, y1, x2, y2 = a["x"] + a["w"], a["y"] + a["h"] / 2, b["x"], b["y"] + b["h"] / 2
    dx = max(40, (x2 - x1) / 2)
    return f"M{x1},{y1} C{x1+dx},{y1} {x2-dx},{y2} {x2},{y2}"
for a, b in D["edges"]:
    blocked = N[a]["status"] != "accepted" and N[b]["status"] != "accepted"
    s.append(f'<path d="{curve_h(D["pos"][a], D["pos"][b])}" fill="none" stroke="{C["pend"] if blocked else C["line"]}" stroke-width="{1.3 if blocked else 0.9}" opacity="{0.8 if blocked else 0.55}"/>')
for id_, n in N.items():
    s.append(node_svg(n, D["pos"][id_], [(id_, MONO, 11, C["ink"])], 11, n["target"]))
s.append("</g></svg>")
(OUT / "proof-graph-full.svg").write_text("\n".join(s))

# ---------- critical path, vertical ----------
K = D["crit"]; W2, H2 = K["meta"]["width"], K["meta"]["height"]
def clip(t, n): return t if len(t) <= n else t[:n-1] + "…"
s = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W2} {H2}" width="{W2}" height="{H2}" font-family="{SANS}">',
     '<defs>' + "".join(f'<marker id="m-{k}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0 L10,5 L0,10 z" fill="{v}"/></marker>'
                        for k, v in [("line", C["line"]), ("pend", C["pend"]), ("root", C["root"]), ("lit", C["lit"])]) + '</defs>',
     f'<rect width="{W2}" height="{H2}" fill="{C["surface"]}"/>']
for i, c in enumerate(K["cols"]):
    s.append(f'<text x="{c["x"]+c["w"]/2}" y="20" text-anchor="middle" font-size="13" font-weight="700" fill="{C["muted"]}">{esc(c["name"])}</text>')
    if i: s.append(f'<line x1="{c["x"]}" y1="28" x2="{c["x"]}" y2="{H2-6}" stroke="{C["bg2"]}"/>')
def curve_v(a, b):
    x1, y1, x2, y2 = a["x"] + a["w"] / 2, a["y"] + a["h"], b["x"] + b["w"] / 2, b["y"]
    dy = max(22, (y2 - y1) / 2)
    return f"M{x1},{y1} C{x1},{y1+dy} {x2},{y2-dy} {x2},{y2}"
special = {("lit:homfly", "cp:finite-contact-path"): "root", ("lit:homfly", "fd:contact"): "root",
           ("src:contact", "fd:contact"): "lit", ("src:contact", "CV:ax:etnyre"): "lit"}
for a, b in K["edges"]:
    kind = special.get((a, b)) or ("pend" if N[a]["status"] != "accepted" and N[b]["status"] != "accepted" else "line")
    dash = ' stroke-dasharray="6 4"' if kind in ("root", "lit") else ""
    s.append(f'<path d="{curve_v(K["pos"][a], K["pos"][b])}" fill="none" stroke="{C[kind]}" stroke-width="{2 if kind=="root" else 1.6}"{dash} marker-end="url(#m-{kind})"/>')
pa, pb = K["pos"]["lit:homfly"], K["pos"]["cp:finite-contact-path"]
s.append(f'<text x="{(pa["x"]+pa["w"]/2+pb["x"]+pb["w"]/2)/2+14}" y="{(pa["y"]+pa["h"]+pb["y"])/2-8}" font-size="11" font-weight="600" fill="{C["root"]}">descent clause weaker than printed (D2)</text>')
for id_ in K["ids"]:
    n = N[id_]; num = f'{n["num"]} ' if n["num"] else ""
    s.append(node_svg(n, K["pos"][id_], [(clip(num + n["short"], 25), MONO, 12, C["ink"]), (clip(n["tag"], 33), SANS, 11, C["ink"] if n["status"] != "accepted" else C["muted"])], 12, True))
p = K["pos"]["lem:gauss-two-discs"]
s.append(f'<text x="{p["x"]+p["w"]/2}" y="{p["y"]+p["h"]+13}" text-anchor="middle" font-size="11" fill="{C["muted"]}">no pending consumer<tspan x="{p["x"]+p["w"]/2}" dy="12">row 104 was proved without it</tspan></text>')
s.append("</svg>")
(OUT / "proof-graph-critical.svg").write_text("\n".join(s))

# ---------- Mermaid block of the critical path (GitHub renders it) ----------
ident = {id_: "n%d" % k for k, id_ in enumerate(K["ids"])}
m = ["flowchart TD"]
for id_ in K["ids"]:
    n = N[id_]; num = f'{n["num"]} ' if n["num"] else ""
    label = (num + n["short"]).replace('"', "'") + "<br/><i>" + n["tag"].replace('"', "'") + "</i>"
    m.append(f'  {ident[id_]}["{label}"]')
for a, b in K["edges"]:
    kind = special.get((a, b))
    arrow = "-.->" if kind else "-->"
    m.append(f"  {ident[a]} {arrow} {ident[b]}")
m.append(f'  classDef ok fill:{C["ok_soft"]},stroke:{C["ok"]},color:{C["ink"]}')
m.append(f'  classDef pend fill:{C["pend_soft"]},stroke:{C["pend"]},color:{C["ink"]}')
m.append(f'  classDef root fill:{C["root_soft"]},stroke:{C["root"]},stroke-width:2px,color:{C["ink"]}')
m.append(f'  classDef lit fill:{C["lit_soft"]},stroke:{C["lit"]},color:{C["ink"]}')
m.append(f'  classDef target stroke-width:3px')
for cls, pred in [("ok", lambda n: n["status"] == "accepted" and not n["literature"]), ("lit", lambda n: n["literature"]),
                  ("root", lambda n: n["root_cause"]), ("pend", lambda n: n["status"] != "accepted" and not n["root_cause"])]:
    ids = [ident[i] for i in K["ids"] if pred(N[i])]
    if ids: m.append(f'  class {",".join(ids)} {cls}')
m.append("  class " + ",".join(ident[i] for i in K["ids"] if N[i]["target"]) + " target")
(OUT / "critical.mmd").write_text("\n".join(m) + "\n")
print("wrote", OUT / "proof-graph-full.svg", OUT / "proof-graph-critical.svg", OUT / "critical.mmd", "| mermaid lines:", len(m))
