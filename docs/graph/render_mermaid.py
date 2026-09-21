#!/usr/bin/env python3
"""Emit two Mermaid views from dag_data.json (built by build_dag.py):
  lanes.mmd  - the chapter-level DAG: one node per lane (chapter of the source, or CV / R / Bridge lane), one edge per
               pair of lanes with at least one blueprint dependency, labelled by the number of such dependencies;
  spine.mmd  - the 31-node chain from the literature inputs to the final theorem (the recorded critical chain)."""
import json, collections, re, sys, pathlib
D = json.load(open(pathlib.Path(__file__).resolve().parent / "dag_data.json"))
N, LANES, E = D["nodes"], D["lanes"], D["edges"]
lane_n = collections.Counter(N[v]["lane"] for v in N)
inter = collections.Counter()
for d, v in E:
    a, b = N[d]["lane"], N[v]["lane"]
    if a != b: inter[(a, b)] += 1
key = {l: f"L{i}" for i, l in enumerate(LANES)}
short = {"SM 1 Polygons": "1  Polygons, chambers, walls", "SM 2 Tree amplitude": "2  Tree coefficient A",
         "SM 3 State sum": "3  Corner state sum C", "SM 3 Polynomial block": "3  Link polynomials (HOMFLY)",
         "SM 3 Fronts & contact": "3  Fronts and contact inputs", "SM 4 Wall laws of C": "4  Wall laws of C",
         "SM 5 Transport": "5  Transport", "SM 6 Comparison": "6  Comparison C = A", "CV lane": "CV  triple wall on carriers",
         "R assembly": "R  Hypothesis R obligations", "Bridge & final": "Bridge and final theorem"}
out = ["flowchart LR"]
for l in LANES:
    out.append(f'  {key[l]}["{short.get(l, l)}<br/><i>{lane_n[l]} rows</i>"]')
for (a, b), c in sorted(inter.items(), key=lambda kv: (LANES.index(kv[0][0]), LANES.index(kv[0][1]))):
    out.append(f"  {key[a]} -->|{c}| {key[b]}")
out.append("  classDef lane fill:#EEF1F6,stroke:#5C6473,color:#181B22")
out.append("  class " + ",".join(key[l] for l in LANES) + " lane")
out.append("  classDef final fill:#E3F3EA,stroke:#2F8F5B,color:#181B22,stroke-width:3px")
out.append(f"  class {key['Bridge & final']} final")
pathlib.Path("lanes.mmd").write_text("\n".join(out) + "\n")
crit = D["crit"]; ids = crit["ids"]; ce = crit["edges"]
TARGETS = {"prop:C-chamber", "prop:C-silent", "thm:C-S3", "thm:C-S5", "thm:C-S7", "thm:C-soft", "Bridge:theorem", "SM:corner_laws_and_soft"}
LIT = {"lit:homfly", "src:contact"}
def label(v):
    n = N[v]; num = f"{n['num']} " if n.get("num") else ""
    kind = {"obligation": "obligation", "hypothesis": "hypothesis (Prop)"}.get(n.get("kind"), n.get("kind") or "")
    if v in LIT: kind = "literature axiom (admitted)"
    elif v == "CV:ax:R": kind = "CV form of Hypothesis R, proved"
    elif v.startswith("CV:ax:"): kind = "CV input, proved here"
    elif v == "hyp:R": kind = "Hypothesis R, proved"
    elif v == "SM:corner_laws_and_soft": kind = "final theorem"
    elif v == "Bridge:theorem": kind = "bridge theorem"
    elif v.startswith("R:"): kind = "R obligation"
    return f'{num}{n["short"]}<br/><i>{kind}</i>'
sid = {v: f"s{i}" for i, v in enumerate(ids)}
out = ["flowchart TD"] + [f'  {sid[v]}["{label(v)}"]' for v in ids] + [f"  {sid[d]} --> {sid[v]}" for d, v in ce]
out += ["  classDef ok fill:#E3F3EA,stroke:#2F8F5B,color:#181B22", "  classDef lit fill:#E7E0FB,stroke:#6E4FE0,color:#181B22",
        "  classDef target stroke-width:3px",
        "  class " + ",".join(sid[v] for v in ids if v not in LIT) + " ok",
        "  class " + ",".join(sid[v] for v in ids if v in LIT) + " lit",
        "  class " + ",".join(sid[v] for v in ids if v in TARGETS) + " target"]
pathlib.Path("spine.mmd").write_text("\n".join(out) + "\n")
print("lanes:", len(LANES), "nodes,", len(inter), "edges | spine:", len(ids), "nodes,", len(ce), "edges")
