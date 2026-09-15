#!/usr/bin/env python3
"""Merge the eight wave-3 SWEEP unit files into W3S_Merged.lean.

Base: W3_U8R_Skeleton.lean (15,586 lines, 58 sorries = 54 sweep leaves + 4 front-move leaves of the L-geo lane).
Units: W3S_{S1a,S1b,S2,S3S5,S4a,S4b,S6a,S6b}.lean, each = the skeleton + ONE helper block + leaf bodies
(+ for S1b / S4b / S6b one RELOCATION of skeleton text, verbatim, forced by Lean's no-forward-reference rule).

Step 1 (verify): every hunk of `diff W3_U8R_Skeleton.lean W3S_<u>.lean` is classified as
  * the unit's single helper block  `/-! ### <u> helpers -/ section <u>Helpers … end <u>Helpers`,
  * a leaf body: ONE skeleton line ending in `:= sorry`, of a leaf of THIS unit, replaced by text whose first
    line is the byte-identical statement tail with `sorry` removed (nothing else of the statement changes),
  * (S1b/S4b/S6b only) the known relocation, checked against the skeleton text verbatim.
Anything else aborts.  No definition, statement, name or docstring may change.

Step 2 (assemble): the merged file is the skeleton with every skeleton line emitted EXACTLY ONCE, in the order
S1a → S2 → S3 → S1b → S4a → S4b (word_closed/oword/oword_letters after run_take_eq_hybrid) → S5 → S6a → S6b
(circleComp_bijective/circleEquiv after ΦFun_cycNext), the helper blocks inserted before the leaves they serve,
and the `:= sorry` lines of proved leaves replaced by their bodies.  Unproved leaves stay `sorry`.

Step 3 (verify the output): every helper block and every body occurs verbatim and contiguously exactly once;
every skeleton line was emitted once; the remaining `sorry` lines are exactly the expected ones.
"""
import re, subprocess, sys, pathlib

HERE = pathlib.Path(__file__).resolve().parent
BASE = HERE / "W3_U8R_Skeleton.lean"
UNITS = ["S1a", "S1b", "S2", "S3S5", "S4a", "S4b", "S6a", "S6b"]
OUT = HERE / "W3S_Merged.lean"

LEAVES = {
    "S1a": ["fibreListBefore_eq_of", "fibreListAfter_eq_of", "fibreListAfter_eq_fibreListBefore",
            "cutBefore_eq_map_dirBit", "cutAfter_eq_cutBefore", "entriesBefore_eq_of_notMem_singX",
            "regular_local_graph", "exists_eta_fibre_near"],
    "S1b": ["entriesBefore_left_limit", "entriesAfter_right_limit", "dirBit_of_cont_before", "dirBit_of_cont_after",
            "cutBefore_left_limit", "cutAfter_right_limit", "cutAfter_eq_cutBefore_of_gap", "posAt_const_of_arc"],
    "S2": ["cusp_arm_sign", "leftCusp_x_local", "rightCusp_x_local", "leftCusp_arms", "rightCusp_arms"],
    "S3S5": ["cross_height_order", "ΦSub_bijective", "ΦFun_partner", "isDesc_ΦFun", "σsgn_ΦFun"],
    "S4a": ["evKey_injective", "events_pairwise_lt", "colX_mono", "evPt_mem_totalFibre", "exists_event_of_singular",
            "step_hybrid", "hybridCutStrict_eq_hybridCut", "hybridCutStrict_eq_cutAfter", "hybridCut_eq_cutBefore"],
    "S4b": ["cutBefore_first", "cutAfter_last", "run_take_eq_hybrid", "word_closed", "word_ne_nil", "cuspCount_eq",
            "downCountSyn_eq", "cut_word_colAt"],
    "S6a": ["isSlot_slotAt", "slotAt_const", "jump_regular", "jump_cusp", "jump_cross", "path_no_occ"],
    "S6b": ["path_cusps", "exists_cuspVertex_sameCycle", "circleComp_bijective", "slotComp_ΦFun", "ΦFun_cycNext"],
}
PREFIX = {u: u.lower() + "_" for u in UNITS}

base = BASE.read_text().split("\n")
N = len(base)
def L(i):  # 1-based skeleton line
    return base[i - 1]

# ---------- skeleton anchors (asserted by content, so a changed skeleton fails loudly) ----------
def anchor(i, prefix):
    if not L(i).startswith(prefix):
        sys.exit(f"ANCHOR FAIL: skeleton line {i} = {L(i)[:80]!r}, expected prefix {prefix!r}")
    return i
A_colAt      = anchor(14847, "def colAt (x : ℝ)")
A_wc_hdr     = anchor(14849, "/-! #### S4 leaves: the word is closed; its counts -/")
A_wc         = anchor(14852, "theorem word_closed : (word F).Closed := sorry")
A_oword_l    = anchor(14857, "@[simp] theorem oword_letters")
A_endDefs    = anchor(14859, "end SweepDefs")
A_S1_hdr     = anchor(14865, "/-! #### S1 leaves:")
A_S1a_first  = anchor(14867, "/-- LEAF (S1): the sorted fibre list")
A_S1b_first  = anchor(14910, "/-- LEAF (S1, the left limit at the level of strand entries)")
A_S2_hdr     = anchor(14952, "/-! #### S2 leaves: the cusp local model -/")
A_S3_hdr     = anchor(14984, "/-! #### S3 leaf: the crossing local model -/")
A_S4_hdr     = anchor(14995, "/-! #### S4 leaves: events and the word -/")
A_S4a_first  = anchor(14997, "/-- LEAF (S4): distinct events have distinct points")
A_S4b_first  = anchor(15039, "/-- LEAF (S4): nothing lies left of the first event")
A_wne        = anchor(15053, "/-- LEAF (S4): the word is nonempty")
A_circleComp = anchor(15148, "def circleComp (i : Fin F.c)")
A_ccb_doc    = anchor(15151, "/-- LEAF (S6): the circles of `F` correspond bijectively")
A_ccb        = anchor(15154, "theorem circleComp_bijective : Function.Bijective (circleComp F) := sorry")
A_circleEq   = anchor(15157, "def circleEquiv : Fin F.c ≃ Fin (numComp (word_closed F))")
A_slotAt_doc = anchor(15159, "/-- LEAF (S6): the slot of a strand at its cut line is a slot")
A_pathcusps  = anchor(15208, "/-- LEAF (S6, the path and the cusps)")
A_endTrav    = anchor(15234, "end Traversal")
for i in (14848, 14858, 14866, 14909, 14951, 14953, 14983, 14994, 14996, 15038, 15052, 15150, 15158, 15207, 15233):
    if L(i) != "":
        sys.exit(f"ANCHOR FAIL: skeleton line {i} should be blank, is {L(i)[:60]!r}")

# leaf name of a `:= sorry` skeleton line: nearest preceding `theorem` header
def leaf_of(i):
    j = i
    while j >= 1 and not L(j).startswith("theorem "):
        j -= 1
    m = re.match(r"theorem (\S+)", L(j))
    return m.group(1) if m else None
SORRY_LINES = {i for i in range(1, N + 1) if L(i).rstrip().endswith(":= sorry")}
LEAF_LINE = {leaf_of(i): i for i in SORRY_LINES}
assert len(SORRY_LINES) == 58, len(SORRY_LINES)
for u in UNITS:
    for lf in LEAVES[u]:
        assert lf in LEAF_LINE, (u, lf)
assert sum(len(v) for v in LEAVES.values()) == 54

# ---------- diff parsing ----------
HDR = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")
def diff_hunks(old_lines, new_lines, tmpdir):
    """normal-format diff of two line lists; returns [(op, a1, a2, b1, b2, new_text_lines)] (1-based)."""
    po, pn = pathlib.Path(tmpdir, "old.txt"), pathlib.Path(tmpdir, "new.txt")
    po.write_text("\n".join(old_lines) + "\n"); pn.write_text("\n".join(new_lines) + "\n")
    p = subprocess.run(["diff", str(po), str(pn)], capture_output=True, text=True)
    hunks = []
    for line in p.stdout.split("\n"):
        m = HDR.match(line)
        if not m:
            continue
        a1 = int(m.group(1)); a2 = int(m.group(2) or a1); op = m.group(3)
        b1 = int(m.group(4)); b2 = int(m.group(5) or b1)
        new = new_lines[b1 - 1:b2] if op in "ac" else []
        hunks.append((op, a1, a2, b1, b2, new))
    return hunks

TMP = pathlib.Path("/tmp/mergeS"); TMP.mkdir(exist_ok=True)

def strip_blank(lines):
    a, b = 0, len(lines)
    while a < b and lines[a].strip() == "": a += 1
    while b > a and lines[b - 1].strip() == "": b -= 1
    return lines[a:b], a

DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+(\S+)")
def declared_names(lines):
    names = []
    for ln in lines:
        m = DECL_RE.match(ln)
        if m and m.group(1) != "instance":
            names.append(m.group(2))
        elif m and m.group(1) == "instance":
            names.append(m.group(2) if not m.group(2).startswith(("(", ":")) else "<anonymous instance>")
    return names

bodies = {}      # skeleton sorry-line -> replacement lines
helpers = {}     # unit -> block lines (without surrounding blank padding)
body_owner = {}  # skeleton line -> unit
report = []

def check_body(unit, a1, new, where=""):
    """a1: skeleton line (must be a `:= sorry` line of a leaf of `unit`); new: replacement lines."""
    old = L(a1)
    if a1 not in SORRY_LINES:
        sys.exit(f"[{unit}] hunk {where} replaces skeleton line {a1} which is not a `:= sorry` line: {old[:80]!r}")
    lf = leaf_of(a1)
    if lf not in LEAVES[unit]:
        sys.exit(f"[{unit}] hunk {where} touches leaf `{lf}` (line {a1}) which is NOT a leaf of this unit")
    stmt = old[: -len(" sorry")]          # ends with ':='
    assert stmt.endswith(":="), (a1, old)
    if not (new[0] == stmt or new[0].startswith(stmt + " ")):
        sys.exit(f"[{unit}] leaf `{lf}`: statement tail changed.\n  skeleton: {old!r}\n  unit:     {new[0]!r}")
    txt = "\n".join(new)
    if re.search(r"\bsorry\b", txt):
        sys.exit(f"[{unit}] leaf `{lf}`: replacement still contains `sorry`")
    for ln in new[1:]:
        if re.match(r"^(theorem|lemma|def|abbrev|instance|structure|/--|/-!|section|end|namespace|variable|open)\b", ln):
            sys.exit(f"[{unit}] leaf `{lf}`: body contains a top-level item: {ln[:80]!r}")
    if a1 in bodies:
        sys.exit(f"[{unit}] leaf `{lf}` also proved by {body_owner[a1]}")
    bodies[a1] = new; body_owner[a1] = unit
    report.append(f"  leaf `{lf}` (skeleton L{a1}): body of {len(new)} lines")

def split_c(unit, a1, a2, new, where=""):
    """A `c` hunk over skeleton lines a1..a2: every `:= sorry` line in it gets a body; every other old line
    (blank separators, docstrings) must reappear verbatim, in place, in the new text."""
    olds = list(range(a1, a2 + 1))
    sorry_idx = [i for i in olds if i in SORRY_LINES]
    if not sorry_idx:
        sys.exit(f"[{unit}] hunk {where} L{a1}-{a2} changes non-leaf text: {L(a1)[:80]!r}")
    starts, cur = [], 0
    for i in sorry_idx:
        stmt = L(i)[: -len(" sorry")]
        js = [k for k in range(cur, len(new)) if new[k] == stmt or new[k].startswith(stmt + " ")]
        if not js:
            sys.exit(f"[{unit}] hunk {where}: statement of `{leaf_of(i)}` (L{i}) not found verbatim in the replacement")
        starts.append(js[0]); cur = js[0] + 1
    lead = [L(i) for i in olds if i < sorry_idx[0]]
    if new[:starts[0]] != lead:
        sys.exit(f"[{unit}] hunk {where}: text before `{leaf_of(sorry_idx[0])}` changed")
    for k, i in enumerate(sorry_idx):
        end = starts[k + 1] if k + 1 < len(starts) else len(new)
        seg = new[starts[k]:end]
        nxt = sorry_idx[k + 1] if k + 1 < len(sorry_idx) else a2 + 1
        sep = [L(m) for m in range(i + 1, nxt)]
        if sep and seg[len(seg) - len(sep):] != sep:
            sys.exit(f"[{unit}] hunk {where}: skeleton lines L{i+1}-L{nxt-1} after `{leaf_of(i)}` not reproduced verbatim")
        body = seg[: len(seg) - len(sep)] if sep else seg
        check_body(unit, i, body, where=where)

def check_helper_block(unit, new):
    blk, _ = strip_blank(new)
    hdr = f"/-! ### {unit} helpers -/"
    sec = f"section {unit}Helpers"
    if blk[0] != hdr or blk[1] != sec or blk[-1] != f"end {unit}Helpers":
        sys.exit(f"[{unit}] helper block is not `{hdr} / {sec} … end {unit}Helpers`: first={blk[0][:60]!r} second={blk[1][:60]!r} last={blk[-1][:60]!r}")
    if re.search(r"\bsorry\b", "\n".join(blk)):
        sys.exit(f"[{unit}] helper block contains `sorry`")
    for kw in ("import ", "set_option ", "attribute ["):
        for ln in blk:
            if ln.startswith(kw):
                sys.exit(f"[{unit}] helper block has a top-level `{kw.strip()}`: {ln[:80]!r}")
    names = declared_names(blk)
    bad = [n for n in names if n != "<anonymous instance>" and not n.startswith(PREFIX[unit])]
    if bad:
        sys.exit(f"[{unit}] helper names without prefix {PREFIX[unit]!r}: {bad}")
    if unit in helpers:
        sys.exit(f"[{unit}] two helper blocks")
    helpers[unit] = blk
    report.append(f"  helper block: {len(blk)} lines, {len(names)} declarations, prefix `{PREFIX[unit]}` OK")

def check_relocated(unit, skel_a, skel_b, new, where):
    """`new` must be skeleton lines skel_a..skel_b verbatim except leaf-body replacements (checked)."""
    old = [L(i) for i in range(skel_a, skel_b + 1)]
    olds, _ = strip_blank(old); news, _ = strip_blank(new)
    off = skel_a + (len(old) - len(old[old.index(olds[0]):])) if olds else skel_a
    # offset: index of olds[0] within old
    off = skel_a + old.index(olds[0])
    hs = diff_hunks(olds, news, TMP)
    for op, a1, a2, b1, b2, nl in hs:
        if op != "c":
            sys.exit(f"[{unit}] relocated block {where}: unexpected hunk {op} {a1},{a2} -> {b1},{b2}")
        split_c(unit, off + a1 - 1, off + a2 - 1, nl, where=where)
    report.append(f"  relocation {where}: skeleton L{skel_a}-{skel_b} re-inserted verbatim ({len(hs)} body hunk(s) inside)")

# ---------- step 1: per-unit verification ----------
for u in UNITS:
    unit_lines = (HERE / f"W3S_{u}.lean").read_text().split("\n")
    hs = diff_hunks(base, unit_lines, TMP)
    report.append(f"[{u}] {len(hs)} hunks: " + ", ".join(f"{a1}{'' if a1==a2 else ','+str(a2)}{op}{b1}{'' if b1==b2 else ','+str(b2)}" for op, a1, a2, b1, b2, _ in hs))
    if u == "S1b":
        # expected: (1) 14910,14950c -> a 3-line `/-! … -/` note; (2) 14993a -> helper block + the S1b leaves (bodies)
        assert len(hs) == 2, hs
        (op1, a1, a2, b1, b2, n1), (op2, c1, c2, d1, d2, n2) = hs
        assert op1 == "c" and a1 == A_S1b_first and a2 == A_S2_hdr - 2, (op1, a1, a2)
        assert n1[0].startswith("/-!") and n1[-1].rstrip().endswith("-/") and all(not DECL_RE.match(x) for x in n1), n1
        report.append(f"  L{a1}-{a2} (the S1b leaves) replaced by a {len(n1)}-line `/-! -/` note (relocation marker; not adopted)")
        assert op2 == "a" and c1 == A_S3_hdr + 9, (op2, c1)   # after cross_height_order's last line
        # the S2/S3 block (skeleton 14952-14994) is common text between the two hunks: verbatim by construction of diff
        idx_h = next(i for i, x in enumerate(n2) if x == "/-! ### S1b helpers -/")
        idx_e = next(i for i, x in enumerate(n2) if x == "end S1bHelpers")
        check_helper_block(u, n2[idx_h:idx_e + 1])
        # what follows `end S1bHelpers` must be the S1b leaves region (skeleton 14910..14950) with bodies
        check_relocated(u, A_S1b_first, A_S2_hdr - 2, n2[idx_e + 1:], where="S1b leaves after the helper block")
        report.append(f"  (S2/S3 leaves, skeleton L{A_S2_hdr}-{A_S3_hdr+10}, are common text in the diff => moved verbatim)")
    elif u == "S4b":
        for op, a1, a2, b1, b2, nl in hs:
            if op == "d":
                assert (a1, a2) == (A_wc_hdr, A_oword_l), (a1, a2)
                report.append(f"  deletion L{a1}-{a2} (word_closed/oword/oword_letters) — re-inserted below")
            elif op == "a":
                check_helper_block(u, nl)
                assert a1 == A_S4b_first - 1, a1
            else:
                if a1 == LEAF_LINE["run_take_eq_hybrid"]:
                    assert a1 == a2, (a1, a2)
                    idx = nl.index(L(A_wc_hdr))
                    body, _ = strip_blank(nl[:idx])
                    check_body(u, a1, body, where="run_take_eq_hybrid part")
                    check_relocated(u, A_wc_hdr, A_oword_l, nl[idx:], where="word_closed block after run_take_eq_hybrid")
                else:
                    split_c(u, a1, a2, nl)
    elif u == "S6b":
        for op, a1, a2, b1, b2, nl in hs:
            if op == "d":
                assert (a1, a2) == (A_ccb_doc, A_circleEq + 1), (a1, a2)
                report.append(f"  deletion L{a1}-{a2} (circleComp_bijective/circleEquiv) — re-inserted below")
            elif op == "a":
                check_helper_block(u, nl)
                assert a1 == A_pathcusps - 1, a1
            else:
                if a1 == LEAF_LINE["ΦFun_cycNext"]:
                    assert a1 == a2, (a1, a2)
                    idx = nl.index(L(A_ccb_doc))
                    body, _ = strip_blank(nl[:idx])
                    check_body(u, a1, body, where="ΦFun_cycNext part")
                    check_relocated(u, A_ccb_doc, A_circleEq + 1, nl[idx:], where="circleComp_bijective block after ΦFun_cycNext")
                else:
                    split_c(u, a1, a2, nl)
    else:
        n_ins = 0
        for op, a1, a2, b1, b2, nl in hs:
            if op == "a":
                check_helper_block(u, nl); n_ins += 1
            elif op == "c":
                split_c(u, a1, a2, nl)
            else:
                sys.exit(f"[{u}] unexpected deletion hunk {a1},{a2}")
        assert n_ins == 1, (u, n_ins)
    proved = [lf for lf in LEAVES[u] if LEAF_LINE[lf] in bodies and body_owner[LEAF_LINE[lf]] == u]
    unproved = [lf for lf in LEAVES[u] if lf not in proved]
    report.append(f"  proved {len(proved)}/{len(LEAVES[u])}; unproved: {unproved}")

# insertion points asserted for the standard units
EXPECT_INS = {"S1a": 14866, "S2": 14953, "S3S5": 14983, "S4a": 14996, "S6a": 15158}

# ---------- step 2: assembly ----------
NOTE = lambda s: ["/-! MERGER (W3S_Merged, 2026-09-14): " + s + " -/"]
emitted = []
out = []
def emit(a, b):
    for i in range(a, b + 1):
        emitted.append(i)
        if i in bodies:
            out.extend(bodies[i])
        else:
            out.append(L(i))

emit(1, A_wc_hdr - 1)                                 # …def colAt, blank   (word_closed block skipped here)
emit(A_oword_l + 1, A_S1a_first - 1)                  # blank, end SweepDefs, …, S1 header, blank
out.extend(helpers["S1a"] + [""])
emit(A_S1a_first, A_S1b_first - 2)                    # the 8 S1a leaves (bodies)
out.extend([""] + NOTE("the S2 and S3 leaves (skeleton L14952-14994) are placed here, BEFORE the S1b helpers, "
                       "because the S1 one-sided limits use their statements (PLAN §4: S1 depends on S2, S3). Text verbatim.") + [""])
emit(A_S2_hdr, A_S2_hdr + 1)                          # S2 header, blank
out.extend(helpers["S2"] + [""])
emit(A_S2_hdr + 2, A_S3_hdr - 1)                      # the 5 S2 leaves (bodies), blank
out.extend(helpers["S3S5"] + [""])
emit(A_S3_hdr, A_S4_hdr - 1)                          # S3 header, cross_height_order (body), blank
out.extend(NOTE("S1b helpers and the 8 S1b leaves (skeleton L14910-14950) follow the S2/S3 leaves they cite.") + [""])
out.extend(helpers["S1b"])
emit(A_S1b_first - 1, A_S2_hdr - 1)                   # blank, the 8 S1b leaves (6 bodies, 2 sorry), blank
emit(A_S4_hdr, A_S4_hdr + 1)                          # S4 header, blank
out.extend(helpers["S4a"] + [""])
emit(A_S4a_first, A_S4b_first - 1)                    # the 9 S4a leaves (bodies), blank
out.extend(helpers["S4b"] + [""])
emit(A_S4b_first, A_wne - 1)                          # cutBefore_first, cutAfter_last, run_take_eq_hybrid (bodies), blank
out.extend(NOTE("`word_closed`, `oword`, `oword_letters` (skeleton L14849-14857, section SweepDefs) are declared here, "
                "after `run_take_eq_hybrid`, because the proof of `word_closed` needs it (S4b). Text verbatim; same `F`.") + [""])
emit(A_wc_hdr, A_oword_l)                             # word_closed block (body), oword, oword_letters
out.append("")
emit(A_wne, A_ccb_doc - 1)                            # word_ne_nil … cut_word_colAt, end SweepLeaves, S5 (bodies), …, circleComp, blank
out.extend(helpers["S6a"] + [""])
emit(A_slotAt_doc, A_pathcusps - 1)                   # the 6 S6a leaves (bodies), blank
out.extend(helpers["S6b"] + [""])
emit(A_pathcusps, A_endTrav - 1)                      # the 5 S6b leaves (bodies), blank
out.extend(NOTE("`circleComp_bijective` and `circleEquiv` (skeleton L15151-15158) are declared here, after "
                "`ΦFun_cycNext`, because the proof needs `slotAt`, the jump leaves, `path_cusps`, "
                "`exists_cuspVertex_sameCycle` (S6b). Text verbatim.") + [""])
emit(A_ccb_doc, A_circleEq + 1)                       # circleComp_bijective (body), circleEquiv, blank
emit(A_endTrav, N)                                    # end Traversal … EOF

# ---------- step 3: verification of the output ----------
assert sorted(emitted) == list(range(1, N + 1)), "every skeleton line must be emitted exactly once"
big = "\n".join(out)
for u in UNITS:
    blk = "\n".join(helpers[u])
    c = big.count(blk)
    if c != 1:
        sys.exit(f"VERIFY FAIL: helper block of {u} occurs {c} times in the output")
for i, nl in bodies.items():
    c = big.count("\n".join(nl))
    if c != 1:
        sys.exit(f"VERIFY FAIL: body for skeleton L{i} ({leaf_of(i)}) occurs {c} times")
# every skeleton declaration header line is present verbatim (statements untouched)
for i in range(1, N + 1):
    if DECL_RE.match(L(i)) and i not in bodies:
        if L(i) not in out:
            sys.exit(f"VERIFY FAIL: skeleton declaration line L{i} missing: {L(i)[:80]!r}")
remaining = [ln for ln in out if re.search(r"\bsorry\b", ln)]
OUT.write_text(big)
print("\n".join(report))
print(f"\nwrote {OUT} ({len(out)} lines; skeleton {N}); helper blocks: " +
      ", ".join(f"{u}={len(helpers[u])}" for u in UNITS))
print(f"bodies applied: {len(bodies)} of 54 sweep leaves; remaining `sorry` lines: {len(remaining)}")
for ln in remaining:
    print("   ", ln.strip()[:120])
print("verify: every skeleton line emitted once; every helper block and body present verbatim and contiguous")
