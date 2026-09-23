#!/usr/bin/env python3
"""Generate blueprint/src/content.tex from the package's own data: the 192 checklist rows
(work/lean/lean-declarations.json), their printed statements and proofs (blueprint/STATEMENTS_AND_PROOFS.md,
frame SM15), the blueprint dependency edges (blueprint/DEPENDENCIES.json) and the chapter/lane assignment
(docs/graph/dag_data.json). Every node carries \\lean{<declaration>} and \\leanok (all rows are accepted).
Rows without a TeX source (the R obligations, the bridge, the final theorem, one helper lemma) get short
statements written from their printed sources, cited in place."""
import csv, json, re, pathlib, collections
ROOT = pathlib.Path(__file__).resolve().parents[1]
PKG = ROOT / "CORNER_LAWS_FOCUSED_20260912"
OUT = ROOT / "blueprint/src/content.tex"

rows = json.load(open(PKG / "work/lean/lean-declarations.json"))["declarations"]
decl = {r["id"]: r["declaration"] for r in rows}
module = {r["id"]: r["module"] for r in rows}
ids = [r["id"] for r in rows]; idset = set(ids)
nodes = json.load(open(ROOT / "docs/graph/dag_data.json"))["nodes"]
edges = json.load(open(PKG / "blueprint/DEPENDENCIES.json"))["edges"]
tsv = {r["id"]: r for r in csv.DictReader(open(PKG / "blueprint/NODES.tsv"), delimiter="\t")}

# ---- printed statements and proofs -------------------------------------------------------------
md = open(PKG / "blueprint/STATEMENTS_AND_PROOFS.md", encoding="utf-8").read()
stmt, proofs = {}, {}
for b in re.split(r"^## ", md, flags=re.M)[1:]:
    rid = b.split(" — ")[0].strip()
    texs = re.findall(r"```tex\n(.*?)```", b, re.S)
    if not texs: continue
    stmt[rid] = texs[0].rstrip()
    proofs[rid] = [t.rstrip() for t in texs[1:] if "\\begin{proof}" in t]

def strip_status(s):
    out = []; i = 0
    while True:
        j = s.find("\\status{", i)
        if j < 0: out.append(s[i:]); break
        out.append(s[i:j]); k = j + len("\\status{"); depth = 1
        while k < len(s) and depth:
            depth += {"{": 1, "}": -1}.get(s[k], 0); k += 1
        i = k
    return "".join(out)

all_labels = set()
for rid, t in stmt.items():
    pre = "CV:" if rid.startswith("CV:") else ""
    for m in re.finditer(r"\\label\{([^}]+)\}", t + "".join(proofs.get(rid, []))): all_labels.add(pre + m.group(1))
all_labels |= idset

def fix(rid, t):
    pre = "CV:" if rid.startswith("CV:") else ""
    t = strip_status(t)
    t = re.sub(r"\\cite(?:\[([^\]]*)\])?\{([^}]*)\}", lambda m: "\\textnormal{[\\texttt{" + m.group(2).replace("_", "\\_") + "}" + (", " + m.group(1) if m.group(1) else "") + "]}", t)
    t = t.replace("\\path{", "\\texttt{")
    if pre: t = re.sub(r"\\label\{([^}]+)\}", lambda m: "\\label{CV:" + m.group(1) + "}", t)
    def ref(m):
        cmd, lab = m.group(1), m.group(2)
        cand = pre + lab
        if cand in ALIAS: return "\\" + cmd + "{" + ALIAS[cand] + "}"
        if lab in ALIAS: return "\\" + cmd + "{" + ALIAS[lab] + "}"
        if cand in all_labels: return "\\" + cmd + "{" + cand + "}"
        if lab in all_labels: return "\\" + cmd + "{" + lab + "}"
        return "\\texttt{" + lab.replace("_", "\\_") + "}"
    t = re.sub(r"\\(ref|eqref)\{([^}]+)\}", ref, t)
    return t

# ---- rows without a TeX extract: statements written from their printed sources ----------------
def weak_open():
    src = open(PKG / "reference/SM/sm-1-polygons.tex", encoding="utf-8").read().split("\n")
    i = next(k for k, l in enumerate(src) if "label{lem:weak-open}" in l)
    j = next(k for k in range(i, len(src)) if src[k].strip() == "\\end{proof}")
    body = "\n".join(src[i:j + 1])
    s, p = body.split("\\begin{proof}", 1)
    return s.rstrip(), "\\begin{proof}" + p
EXTRA_ENV = {}
EXTRA = {}
_ws, _wp = weak_open(); stmt["lem:weak-open"] = _ws; proofs["lem:weak-open"] = [_wp]

def ob(rid, title, text, src):
    EXTRA[rid] = (title, text + "\n\nSource: \\texttt{" + src.replace("_", "\\_") + "}.")
    EXTRA_ENV[rid] = "obligation"

ob("R:localization", "R-LOC-2, localization",
 r"""Let $t\mapsto P(t)$ be a simple transversal Reidemeister-III event with zero set exactly the forced bundle
$Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},\mathrm{G4}_{g;e,f}\}$, $e<f<g$ pairwise remote and
concurrent at $t=0$ at a point interior to all three, and let $T=\{x_{ef},x_{eg},x_{fg}\}$. On a punctured
neighbourhood of $t=0$: the crossing set, indexed by carrying edge pairs, is constant; on each of $e,f,g$ the two
crossings of $T$ carried by that edge occupy adjacent crossing-visits of the traversal circle, in opposite order on the
two sides; only the three internal pairs of $T$ change their interlacement; and the local graphs induced on $T$ on the two
sides are complements of each other.""", "reference/R/RA/R_ATTACHMENT_WARRANTS.md, R-LOC-2")
ob("R:parity", "R-PAR-v6, parity and availability",
 r"""With $T=\{x_{ef},x_{eg},x_{fg}\}$ the triangle of a simple transversal RIII event and $P$ either side's polygon near the
wall: (P1) every crossing $y\notin T$ interlaces exactly $0$ or exactly $2$ of the three crossings of $T$, and an interlaced
pair is one of the three pairs sharing a bundle edge; (P2) for any set $S'$ of crossings disjoint from $T$, the available set
$\mathrm{avail}(S')=\{x\in T: x\text{ interlaces no element of }S'\}$ has size $3$, $1$ or $0$.""",
 "reference/R/RA/R_ATTACHMENT_WARRANTS.md, R-PAR-v6")
ob("R:fibre_partition", "the fibre partition of the state sum",
 r"""Identify the crossing sets of the two sides through R-LOC-2; let $T$ be the three local crossings and $W$ the
complement. Every independent support $S$ decomposes uniquely as $Q\cup J$ with $Q=S\cap W$ independent in the outside
graph and $J=S\cap T$ independent in the local graph and contained in the availability set
$\mathcal A(Q)=\{t\in T:\text{no element of }Q\text{ is adjacent to }t\}$, and every such pair gives an independent support.
Hence $X_1(P_\pm)=\sum_{Q\in\Ind(G[W])}\Phi_\pm(Q)$ with $\Phi_\pm(Q)=\sum_{J\in\Ind(G_\pm[\mathcal A(Q)])}F_\pm(Q\cup J)$,
$F_\pm(S)$ the complete summand of CV \texttt{def:X1} at $S$.""", "R_ASSEMBLY_SPEC.md, (1)-(3)")
ob("R:generic_table", "the generic-orbit table",
 r"""In the generic graph orbit ($P_3$ on one side, one edge plus one isolated vertex on the other), with the three exterior
gaps $A,B,C$ between the strand blocks, the two sides have the exact local words $P=a\,b\,A\,a\,c\,B\,b\,c\,C$ (edges $ab$,
$bc$; centre $b$) and $E=b\,a\,A\,c\,a\,B\,c\,b\,C$ (edge $ac$; $b$ isolated). The table of local supports, masks, residual
words and successor cycles on both sides is as printed, and the graph-selected complement couple is $b/ac$.""",
 "reference/R/RA/R_GENERIC_ORBIT_ACTUAL_TABLE.md")
ob("R:exterior", "R-EXTERIOR-1, the triangle-disjoint factor",
 r"""Let $P_-$, $P_+$ be the generic sides of a simple transversal RIII event, $T$ its three crossings, and $Q$ an outside
independent set. On either side $\sigma$, for every $A\subseteq T$ with $S=Q\cup A$ independent, let $C_{Q,\sigma}(A)$ be the
product of the weights of the triangle-disjoint carriers of $S$ (those containing none of the six traversal visits of $T$).
Then $C_{Q,\sigma}(A)$ does not depend on $A$, and it takes the same value on the two sides.""",
 "reference/R/RA/R_ATTACHMENT_WARRANTS.md, R-EXTERIOR-1")
ob("R:availability_0_1", "the fibre identities at availability $0$ and $1$",
 r"""For every outside independent support $Q$ whose availability set has size $0$ or $1$, $\Phi_+(Q)=\Phi_-(Q)$: the local
supports correspond across the wall and their complete summands agree after transporting the carrier records, selectors,
rotation numbers and coefficients.""", "R_ASSEMBLY_SPEC.md, (4)")
ob("R:generic_selector", "the non-selected pair rows have selector zero",
 r"""Fix a full-availability fibre at a simple RIII wall in the generic graph orbit. Among the three one-sided local pair
supports, one is the graph-selected pair complementary to the degree-two singleton of $P_3$. Each of the other two pair rows
has winding selector zero on the side where it is present, for arbitrary exterior gaps and outside independent support $Q$.""",
 "reference/R/RA/R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, Statement")
ob("R:generic_transport", "common endpoint transports in the generic orbit",
 r"""Fix a full-availability fibre at a simple RIII wall in the generic graph orbit and an exterior independent support $Q$,
with the local words $P=a\,b\,A\,a\,c\,B\,b\,c\,C$ and $E=b\,a\,A\,c\,a\,B\,c\,b\,C$; the generic branch has
$\sgn\det(u_1,u_2)=\sgn\det(u_1,u_3)=\sgn\det(u_2,u_3)$. Writing $T_\nu(J)$ for the complete $X_1$ term of $Q\cup J$ on side
$\nu$: $T_P(\varnothing)=T_E(\varnothing)$, $T_P(a)=T_E(a)$, $T_P(c)=T_E(c)$.""",
 "reference/R/RA/R_GENERIC_COMMON_TRANSPORT_PROOF.md, Statement")
ob("R:generic_selected", "the selected complementary couple in the generic orbit",
 r"""Fix a full-availability fibre at a simple RIII wall in the generic graph orbit and an exterior independent support $Q$,
with the local words $P=a\,b\,A\,a\,c\,B\,b\,c\,C$ (edges $ab$, $bc$) and $E=b\,a\,A\,c\,a\,B\,c\,b\,C$ (edge $ac$). With
$T_\nu(J)$ the complete $X_1$ term of $Q\cup J$ on side $\nu$, absent rows being zero: $T_E(b)=T_P(b)+T_P(ac)$.""",
 "reference/R/RA/R_GENERIC_SELECTED_COUPLE_PROOF.md, Statement")
ob("R:extreme_pair_zero", "pair rows vanish in the extreme orbit",
 r"""Fix the two nearby generic sides of a simple RIII wall in the extreme graph orbit ($K_3$ on one side, the empty graph on
the other) and a full-availability fibre. Each local pair support is absent on the $K_3$ side and present on the empty-graph
side, and its complete $X_1$ term on the latter is zero, for arbitrary outside support and exterior geometry.""",
 "reference/R/RA/R_EXTREME_PAIR_ZERO_PROOF.md, Statement")
ob("R:extreme_transport", "singleton transports in the extreme orbit",
 r"""Fix a full-availability fibre at a simple RIII wall in the extreme graph orbit, an outside support $Q$, and the canonical
words $H=x\,y\,A\,z\,x\,B\,y\,z\,C$ (local graph $K_3$) and $L=y\,x\,A\,x\,z\,B\,z\,y\,C$ (local graph empty). With
$T_\nu(J)$ the complete $X_1$ term of $Q\cup J$: $T_H(x)=T_L(x)$, $T_H(y)=T_L(y)$, $T_H(z)=T_L(z)$.""",
 "reference/R/RA/R_EXTREME_SINGLETON_TRANSPORT_PROOF.md, Statement")
ob("R:extreme_selected", "the selected complementary couple in the extreme orbit",
 r"""Fix a full-availability fibre at a simple RIII wall in the extreme graph orbit; let $H$ be the side whose local graph is
$K_3$ and $L$ the side whose local graph is empty, and fix the outside support $Q$, with the canonical words
$H=x\,y\,A\,z\,x\,B\,y\,z\,C$ and $L=y\,x\,A\,x\,z\,B\,z\,y\,C$. With $T_\nu(J)$ the complete $X_1$ term of $Q\cup J$, an
absent row read as zero: $T_H(\varnothing)-T_L(\varnothing)=T_L(xyz)$.""",
 "reference/R/RA/R_EXTREME_SELECTED_COUPLE_PROOF.md, Statement")
ob("R:cv_theorem", "the R theorem in CV form",
 r"""$X_1(P_+)=X_1(P_-)$ across every simple transversal Reidemeister-III event with the forced zero set (CV \texttt{ax:R}
on its entire printed domain), obtained by summing the fibre identities $\Phi_+(Q)=\Phi_-(Q)$ over the partition
$X_1(P_\pm)=\sum_Q\Phi_\pm(Q)$.""", "R_ASSEMBLY_SPEC.md, (3)-(4); OPEN_WORK.md item 4")
ob("Bridge:B1", "B1, transfer of a triple germ",
 r"""Under the labelled coordinate identification, an SM simple triple wall germ is a CV event of polygons, generic at every
nonzero time and non-generic at time zero.""", "reference/BRIDGE/BRIDGE.md, Lemma B1")
ob("Bridge:B2", "B2, exactly the forced bundle",
 r"""For the germ of B1, the CV zero set is exactly $\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},
\mathrm{G4}_{g;e,f}\}$, with increasing edge representatives, pairwise remoteness, and a central point interior to all
three edges.""", "reference/BRIDGE/BRIDGE.md, Lemma B2")
ob("Bridge:B3", "B3, all four sign changes",
 r"""The three parameter-difference sign changes of SM type T, together with its central conditions, imply CV transversality
for that zero set: all four members change sign.""", "reference/BRIDGE/BRIDGE.md, Lemma B3")
ob("Bridge:B4", "B4, pointwise dictionary and side values",
 r"""On every SM-generic labelled representative the two state sums have equal values, $C^{\mathrm{SM}}(P)=X_1^{\mathrm{CV}}(P)$.
On either punctured side of a triple germ this identifies the SM side value with the value of $X_1$ on the containing CV
chamber.""", "reference/BRIDGE/BRIDGE.md, Lemma B4, displays (17)-(18)")
ob("Bridge:theorem", "the bridge theorem: Hypothesis R for SM",
 r"""The R theorem in CV form implies $C(P_+)=C(P_-)$ for every SM simple triple wall germ, that is, Hypothesis R: by B1-B3
the germ is a simple transversal RIII event with the forced bundle, the CV theorem gives $X_1(P_+)=X_1(P_-)$, and B4
converts both sides to $C$.""", "reference/BRIDGE/BRIDGE.md, displays (19)-(21)")
EXTRA["SM:corner_laws_and_soft"] = ("the corner laws and the soft theorem",
 r"""For every generic polygon, on the printed domains: $C$ is constant on every chamber and invariant across the silent
walls (exterior extension, pure cut); the flat law $C(P_{\rm right})-C(P_{\rm left})=C(P(0)\setminus j)$; the vertex-edge
law $C(P_+)-C(P_-)=s\,C(\lambda_1)\,C(\lambda_2)$ in both bigon branches and the sliding branch; triple-wall invariance
$C(P_+)=C(P_-)$ (Hypothesis R, proved); the full cusp law $C(P_{\rm loop})-C(P_{\rm no})=-\kappa\,C(P(0)\setminus j)$
when the deletion satisfies (G1), threaded cusps included; the empty-cusp zero $C(P_{\rm no})=0$; the soft theorem
$C(P_\varepsilon)=\frac{\chi_-+\chi_+}2C(P)$ in every sector; and the reversal, cyclic and triangle normalizations of
\texttt{cor:A-lawful}. In Lean this is the structure \texttt{SM.CornerLawsAndSoftData}, one field per clause, and the
theorem \texttt{SM.corner\_laws\_and\_soft} instantiates the conditional assembly with the proved bridge theorem.

Source: \texttt{TARGETS.md}, Exact final target.""")
EXTRA_ENV["SM:corner_laws_and_soft"] = "theorem"

# ---- chapters -----------------------------------------------------------------------------------
LANES = ["SM 1 Polygons", "SM 2 Tree amplitude", "SM 3 State sum", "SM 3 Polynomial block", "SM 3 Fronts & contact",
         "SM 4 Wall laws of C", "SM 5 Transport", "SM 6 Comparison", "CV lane", "R assembly", "Bridge & final"]
TITLE = {"SM 1 Polygons": "Polygons, chirotopes, chambers and walls",
         "SM 2 Tree amplitude": "The tree coefficient $A$",
         "SM 3 State sum": "The corner state sum $C$",
         "SM 3 Polynomial block": "Link diagrams and the HOMFLY-PT interface",
         "SM 3 Fronts & contact": "Fronts, contact inputs and the carrier floor",
         "SM 4 Wall laws of C": "The wall laws of $C$",
         "SM 5 Transport": "Fixed-count transport",
         "SM 6 Comparison": "Root independence, uniqueness and the comparison $C=A$",
         "CV lane": "The companion document: the triple wall on carriers",
         "R assembly": "Hypothesis R: the R obligations",
         "Bridge & final": "The bridge to SM and the final theorem"}
INTRO = {"SM 1 Polygons": "Chapter 1 of the source: the objects every later statement is about.",
         "SM 2 Tree amplitude": "Chapter 2 of the source: the tree coefficient and the laws proved for it directly.",
         "SM 3 State sum": "Chapter 3 of the source: decompositions, carriers, positive lifts and the definition of $C$.",
         "SM 3 Polynomial block": "Chapter 3 of the source: the HOMFLY-PT interface, the local polynomial and the record bridge. The literature inputs of this chapter are the admitted axioms.",
         "SM 3 Fronts & contact": "Chapter 3 of the source: fronts, the contact-topology inputs and the carrier floor.",
         "SM 4 Wall laws of C": "Chapter 4 of the source: chamber constancy, silence, the flat, vertex-edge, empty-cusp and soft laws of $C$, and Hypothesis R.",
         "SM 5 Transport": "Chapter 5 of the source: the circular stars and fixed-count transport.",
         "SM 6 Comparison": "Chapter 6 of the source: the uniqueness theorem, the comparison $C=A$ under Hypothesis R, and the laws $C$ inherits.",
         "CV lane": "The companion document (CV) in its own conventions: the objects and lemmas the proof of Hypothesis R consumes. Its four printed axioms are proved here from the SM base; \\texttt{ax:R} is the CV form of Hypothesis R, proved in the next chapter.",
         "R assembly": "The proof obligations that establish the R theorem in CV form: localization, parity, the fibre partition, the exterior factor, and the two graph orbits.",
         "Bridge & final": "The four bridge lemmas, the bridge theorem giving Hypothesis R for SM, and the final theorem."}

def num(rid): return nodes[rid].get("num") or 10**6
by_lane = collections.defaultdict(list)
for rid in ids: by_lane[nodes[rid]["lane"]].append(rid)
for l in by_lane: by_lane[l].sort(key=lambda r: (num(r), r))

def uses(rid): return [d for d in edges.get(rid, []) if d in idset and d != rid]

ENVRE = re.compile(r"\\(begin|end)\{([A-Za-z*]+)\}")
def balance(t):
    """Close every environment a fragment leaves open (some extracts are clause-level fragments of a longer
    environment); returns the text with the missing \\end{...} appended in the right order."""
    stack = []
    for m in ENVRE.finditer(t):
        if m.group(1) == "begin": stack.append(m.group(2))
        elif stack and stack[-1] == m.group(2): stack.pop()
    return t + "".join("\n\\end{" + e + "}" for e in reversed(stack))

# rows whose extract carries a label different from the row id: the row id becomes the label, references follow
ALIAS = {}
for _rid, _t in stmt.items():
    _pre = "CV:" if _rid.startswith("CV:") else ""
    _m = re.search(r"\\label\{([^}]+)\}", _t)
    if _m and _pre + _m.group(1) != _rid: ALIAS[_pre + _m.group(1)] = _rid

def env_of(t):
    m = re.match(r"\s*\\begin\{(\w+)\}", t); return m.group(1) if m else None

def render(rid):
    d = decl[rid]; us = uses(rid); ustr = ("\\uses{" + ", ".join(us) + "}") if us else ""
    tag = "\\lean{" + d + "}\\leanok"
    if rid in EXTRA:
        title, text = EXTRA[rid]; env = EXTRA_ENV[rid]
        s = f"\\begin{{{env}}}[{title}]\\label{{{rid}}}{tag}\n{text}\n\\end{{{env}}}\n"
        s += f"\\begin{{proof}}\\leanok{ustr}\nFormalized as \\texttt{{{d.replace('_', chr(92)+'_')}}} in \\texttt{{{module[rid].replace('_', chr(92)+'_')}}}.\n\\end{{proof}}\n"
        return s
    t = fix(rid, stmt[rid]); env = env_of(t)
    if env is None:
        body = t.strip()
        if body.startswith("\\item"): body = "\\begin{enumerate}\n" + body + "\n\\end{enumerate}"   # a clause fragment
        t = f"\\begin{{clause}}[{rid}]\\label{{{rid}}}\n" + body + "\n\\end{clause}"; env = "clause"
    if rid.startswith("CV:ax:") and rid != "CV:ax:R":
        t = re.sub(r"\\begin\{axiom\}\[", "\\\\begin{theorem}[CV axiom, proved here: ", t, count=1).replace("\\end{axiom}", "\\end{theorem}"); env = "theorem"
    elif rid == "CV:ax:R":
        t = re.sub(r"\\begin\{axiom\}\[", "\\\\begin{hypothesis}[CV form of Hypothesis R: ", t, count=1).replace("\\end{axiom}", "\\end{hypothesis}"); env = "hypothesis"
    for _orig, _new in ALIAS.items():
        if _new == rid: t = t.replace(f"\\label{{{_orig}}}", f"\\label{{{rid}}}", 1)
    if f"\\label{{{rid}}}" in t:
        t = t.replace(f"\\label{{{rid}}}", f"\\label{{{rid}}}{tag}", 1)
    else:
        t = re.sub(r"(\\begin\{\w+\}(?:\[[^\]]*\])?)", lambda m: m.group(1) + f"\\label{{{rid}}}{tag}", t, count=1)
    action = tsv.get(rid, {}).get("action", "PROVE")
    is_def = action in ("DEFINE", "AXIOM", "HYPOTHESIS")
    if is_def and ustr:
        t = t.replace(tag, tag + ustr, 1)
    out = balance(t) + "\n"
    if not is_def:
        ps = [balance(fix(rid, p)) for p in proofs.get(rid, [])]
        if ps:
            body = "\n".join(ps)
            body = body.replace("\\begin{proof}", "\\begin{proof}\\leanok" + ustr, 1)
            out += body + "\n"
        else:
            out += f"\\begin{{proof}}\\leanok{ustr}\nFormalized as \\texttt{{{d.replace('_', chr(92)+'_')}}}.\n\\end{{proof}}\n"
    return out

parts = [r"""\chapter*{How to read this blueprint}
Every numbered statement below is one row of the formalization: a printed definition, lemma, theorem, literature input,
hypothesis or proof obligation of the source (frame SM15), followed by the name of the Lean declaration that formalizes it.
All 192 rows are accepted: kernel-checked and independently reviewed. The dependency graph (link in the navigation bar)
shows every row as a node and the source's proof-route dependencies as edges; a proof is collapsed under its statement.
The five literature inputs are the only admitted axioms; everything else is proved. The Lean library is at
\url{https://github.com/aguevara22/corner-laws-lean} (\texttt{CORNER\_LAWS\_FOCUSED\_20260912/work/lean}).
"""]
for lane in LANES:
    parts.append(f"\\chapter{{{TITLE[lane]}}}\n{INTRO[lane]}\n")
    for rid in by_lane[lane]: parts.append(render(rid))
OUT.write_text("\n".join(parts))
print("content.tex:", OUT.stat().st_size, "bytes;", len(ids), "rows;", sum(len(uses(r)) for r in ids), "uses edges;",
      "chapters:", len(LANES), "| rows per chapter:", {TITLE[l][:22]: len(by_lane[l]) for l in LANES})
