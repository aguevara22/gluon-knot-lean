#!/usr/bin/env python3
"""Assemble G11_Assembled.lean from G11_Skeleton.lean and the unit files G11_U1..U6.lean.

Step 1: parse `diff skeleton unit` (normal format) for every unit; every hunk must be
  (a) an insertion of import lines right after line 1,
  (b) an insertion of helper lines after some skeleton line,
  (c) a replacement of a single skeleton `  sorry` line by a proof body, or
  (d) (U5 only) a replacement of `<header> := by` + `  sorry` by `<header> :=` + one term line
      (normalised here to the frozen header + `  exact <term>`).
Anything else is a freeze violation and aborts.
Step 2: splice.  Step 3 (post-processing, clearly separated below): the two `include … in` fixes for the
skeleton's under-included leaves, the deletion of the X2 branch, docstring rewrite.
"""
import re, subprocess, sys, os

D = os.path.dirname(os.path.abspath(__file__))
SK = os.path.join(D, "G11_Skeleton.lean")
UNITS = [os.path.join(D, f"G11_U{u}.lean") for u in range(1, 7)]
OUT = os.path.join(D, "G11_Assembled.lean")
POST = "--post" in sys.argv
RELOCATE = {(2, 696): 692}  # U2's gu2_cfg_hpq (+docstring): from after the G11_cfg_hpq leaf to after G11_cfg_hmq

sk = open(SK, encoding="utf-8").read().split("\n")
if sk[-1] == "":
    sk.pop()
N = len(sk)

imports = []          # extra import lines (deduped, order of first appearance)
insert_after = {}     # skeleton line no (1-based; 0 = before first) -> list of (unit, [lines])
replace = {}          # skeleton line no -> (unit, [lines])
log = []

hunk_re = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")

for ui, uf in enumerate(UNITS, start=1):
    un = open(uf, encoding="utf-8").read().split("\n")
    if un[-1] == "":
        un.pop()
    out = subprocess.run(["diff", SK, uf], capture_output=True, text=True).stdout.split("\n")
    i = 0
    while i < len(out):
        m = hunk_re.match(out[i])
        if not m:
            i += 1
            continue
        a1 = int(m.group(1)); a2 = int(m.group(2) or a1); op = m.group(3)
        b1 = int(m.group(4)); b2 = int(m.group(5) or b1)
        i += 1
        if op == "d":
            sys.exit(f"U{ui}: DELETION hunk {out[i-1]} — freeze violation")
        new_lines = un[b1 - 1:b2]
        if op == "a":
            if a1 == 1 and all(l.startswith("import ") for l in new_lines):
                for l in new_lines:
                    if l not in imports and l != sk[0]:
                        imports.append(l)
                log.append(f"U{ui}: imports {new_lines}")
            else:
                tgt = a1
                if POST and (ui, a1) in RELOCATE:
                    tgt = RELOCATE[(ui, a1)]
                    log.append(f"U{ui}: block after skeleton L{a1} RELOCATED to after L{tgt} (helper needed by the leaf it followed)")
                    new_lines = [l.replace("The frozen `G11_cfg_hpq` above does not have", "The frozen `G11_cfg_hpq` below did not have") for l in new_lines]
                insert_after.setdefault(tgt, []).append((ui, new_lines))
                log.append(f"U{ui}: insert {len(new_lines)} lines after skeleton L{tgt} (unit L{b1}-{b2})")
        elif op == "c":
            old = sk[a1 - 1:a2]
            if a1 == a2:
                if old != ["  sorry"]:
                    sys.exit(f"U{ui}: replaced skeleton L{a1} is not a sorry line: {old!r} — freeze violation")
                if a1 in replace:
                    sys.exit(f"U{ui}: skeleton L{a1} replaced twice (also U{replace[a1][0]})")
                replace[a1] = (ui, new_lines)
                log.append(f"U{ui}: leaf body at skeleton L{a1} <- unit L{b1}-{b2} ({len(new_lines)} lines)")
            else:
                # U5 style: header `:= by` + sorry  ->  header `:=` + term
                if not (a2 == a1 + 1 and old[1] == "  sorry" and old[0].endswith(" := by")
                        and len(new_lines) == 2 and new_lines[0] == old[0][:-3]
                        and new_lines[1].startswith("  ")):
                    sys.exit(f"U{ui}: unexpected multi-line change at skeleton L{a1}-{a2}: {old!r} -> {new_lines!r}")
                term = new_lines[1].strip()
                replace[a2] = (ui, ["  exact " + term])
                log.append(f"U{ui}: leaf at skeleton L{a1} given as term `{term}`; header kept frozen, body `exact` (normalised)")
        # skip the hunk body lines
        while i < len(out) and not hunk_re.match(out[i]):
            i += 1

# ---- splice ----
res = [sk[0]] + imports
for ln in range(2, N + 1):
    if ln in replace:
        res.extend(replace[ln][1])
    else:
        res.append(sk[ln - 1])
    for (ui, lines) in insert_after.get(ln, []):
        res.extend(lines)
text = "\n".join(res) + "\n"

# ---- verify contiguity of every inserted/replaced block ----
for ln, blocks in insert_after.items():
    for (ui, lines) in blocks:
        blk = "\n".join(lines) + "\n"
        if text.count(blk) < 1:
            sys.exit(f"U{ui}: inserted block after L{ln} not found contiguously in output")
for ln, (ui, lines) in replace.items():
    blk = "\n".join(lines) + "\n"
    if blk not in text:
        sys.exit(f"U{ui}: body for L{ln} not found in output")

# every non-sorry skeleton line must survive verbatim, in order
pos = 0
for ln in range(1, N + 1):
    if ln in replace:
        continue
    l = sk[ln - 1]
    j = text.find(l + "\n", pos) if l else pos
    if j < 0:
        sys.exit(f"skeleton L{ln} lost: {l!r}")
    pos = j + len(l) + 1

remaining_sorry = [ln for ln in range(1, N + 1) if sk[ln - 1] == "  sorry" and ln not in replace]
log.append(f"skeleton sorry lines still sorry: {remaining_sorry}")

# ---- post-processing (assembler-level edits, all reported in G11_ASSEMBLY_REPORT.md) ----
if POST:
    # (P1) G11_clear: the frozen leaf lacks `hG` (false without it, U2 counterexample); `include hG in` + gu2_clear
    hdr = "theorem G11_clear (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)\n"
    doc = "/-- **A8 (clearance, local form).**"
    assert text.count(hdr) == 1 and text.count(doc) == 1
    text = text.replace(doc, "include hG in\n" + doc)
    k = text.index(hdr)
    e = text.index("\n  sorry\n", k)
    text = text[:e] + "\n  exact gu2_clear hG hs hef heg hfg hcef hceg hcfg hX\n" + text[e + len("\n  sorry\n"):]
    # (P2) G11_cfg_hpq: the frozen leaf lacks `hfg hcfg`; `include hfg hcfg in` + gu2_cfg_hpq, call sites updated
    hdr = "theorem G11_cfg_hpq (hX : ExactTriangleVisitOrders P P' e f g hs) :\n"
    assert text.count(hdr) == 1
    text = text.replace(hdr, "include hfg hcfg in\n" + hdr)
    k = text.index(hdr)
    e = text.index("\n  sorry\n", k)
    text = text[:e] + "\n  exact gu2_cfg_hpq hn hG hs hT q hcef hceg htri hfg hcfg hX\n" + text[e + len("\n  sorry\n"):]
    old = "G11_cfg_hpq hn hG hs hT q hcef hceg htri hX"
    new = "G11_cfg_hpq hn hG hs hT q hfg hcef hceg hcfg htri hX"
    n_old = text.count(old)
    text = text.replace(old, new)
    # inside G11_configOf the crossing hypothesis is named `_hcfg`
    text = text.replace("  hpq := " + new, "  hpq := G11_cfg_hpq hn hG hs hT q hfg hcef hceg _hcfg htri hX")
    for nm in ("G11_cfg_clear_frontier", "G11_cfg_clear_vertex"):
        o = f"{nm} hn hG hs hT q hcef hceg htri hef heg hfg hX"
        assert text.count(o) == 1, (nm, text.count(o))
        text = text.replace(o, f"{nm} hn hG hs hT q hcef hceg _hcfg htri hef heg hfg hX")
    o = "gu2_cfg_clear_vertex hn hG hs hT q hcef hceg htri hef heg hfg hX"
    n_cv = text.count(o)
    text = text.replace(o, "gu2_cfg_clear_vertex hn hG hs hT q hcef hceg hcfg htri hef heg hfg hX")
    log.append(f"post: G11_cfg_hpq call sites updated: {n_old}; gu2_cfg_clear_vertex call sites updated: {n_cv}")
    # (P3) drop X2 + the two NOT-ON-THE-ROW'S-PATH declarations
    def cut(text, start_marker, end_marker):
        s = text.index(start_marker); e = text.index(end_marker, s)
        return text[:s] + text[e:], text[s:e]
    s0 = text.index("/-- **Leaf X2 (exactly two local crossings: impossible — FLAGGED).**")
    t0 = text.index("theorem G11_two_crossings_absurd", s0)
    e0 = text.index("\n  sorry\n", t0) + len("\n  sorry\n")
    c1 = text[s0:e0]
    assert text[e0] == "\n"
    text = text[:s0] + text[e0 + 1:]
    text, c2 = cut(text, "/-- **`GT_G11` PROVED** from `GT_G11_strong` and the branch leaves X1–X3. -/",
                   "/-! ### The row theorem, from `GT_G11_strong` alone")
    text, c3 = cut(text, "-- NOT ON THE ROW'S PATH (uses the flagged leaf X2 through `GT_G11_proof`)", "end RProof\n")
    log.append(f"post: removed X2 block ({c1.count(chr(10))} lines), GT_G11_proof ({c2.count(chr(10))} lines), "
               f"generic_transport_of_GT_G11 ({c3.count(chr(10))} lines)")
    open("/tmp/g11asm/removed.lean", "w").write(c1 + "\n----\n" + c2 + "\n----\n" + c3)

    # (P4) module docstring: describe the assembled state (the file has no unproved leaf any more)
    old_head = """/-! # G11 skeleton — HOMFLY invariance of the distinguished carrier's grouped diagram across the RIII wall

Written 2026-09-14 by the G11 architect (R lane, row 173 follow-up) on Mark's RunPod home pod. Plan:
`work/drafts/rlane2/G11_PLAN.md`. This file `import RProof.X1Rows3` (the accepted wave-3 module) and
contains ONLY the new material, all `G11_`-prefixed (namespace `RProof`). Every leaf (49) is `sorry`; the
assembled theorems `GT_G11_strong_proof`, `GT_G11_proof : GT_G11` and the row theorem
`RProof.generic_transport` are PROVED from the leaves.
"""
    new_head = """/-! # G11 — HOMFLY invariance of the distinguished carrier's grouped diagram across the RIII wall

Skeleton written 2026-09-14 by the G11 architect (R lane, row 173 follow-up) on Mark's RunPod home pod;
assembled the same day from the six unit files `G11_U1`–`G11_U6` (`work/drafts/rlane2/G11_ASSEMBLY_REPORT.md`,
built by `G11_assemble.py`). Plan: `work/drafts/rlane2/G11_PLAN.md`. This file `import RProof.X1Rows3` (the
accepted wave-3 module; plus `SM.CS3` and two Mathlib affine-basis files) and contains ONLY the new material,
all `G11_`-prefixed (namespace `RProof`; the unit helpers are `gu1_`–`gu6_`-prefixed). Every leaf is proved;
`GT_G11_strong_proof` and the row theorem `RProof.generic_transport` are proved from the leaves with no axiom
beyond those of the accepted sibling rows (`propext`, `Classical.choice`, `Quot.sound`, `SM.lit_homfly`,
`SM.lp_lm`, `SM.lp_lm_uniqueness`). Two skeleton leaves (`G11_clear`, `G11_cfg_hpq`) had section hypotheses
missing from their statements (`hG`; `hfg hcfg`) and are stated with `include … in`; see the assembly report.
"""
    assert text.count(old_head) == 1
    text = text.replace(old_head, new_head)
    old_find = """RIII route, re-derive the row `generic_transport` from it (copying the accepted 60-line assembly), and
prove the literal `GT_G11` from `GT_G11_strong` plus two branch leaves: `≤ 1` triangle crossing (a plain
record isomorphism, provable) and exactly two triangle crossings (contradictory by Gauss parity — NOT in
the library; flagged). -/"""
    new_find = """RIII route and re-derive the row `generic_transport` from it (copying the accepted 60-line assembly). The
literal `GT_G11` would additionally need the two branch cases `≤ 1` triangle crossing (a plain record
isomorphism, proved below as `G11_le_one_crossing`) and exactly two triangle crossings (contradictory by
Gauss parity, which is NOT in the library); that branch is not on the row's path and is omitted here. -/"""
    assert text.count(old_find) == 1
    text = text.replace(old_find, new_find)
    log.append("post: module docstring rewritten (assembled state)")

open(OUT, "w", encoding="utf-8").write(text)
print("\n".join(log))
print(f"wrote {OUT}: {text.count(chr(10))} lines; imports added: {imports}")
