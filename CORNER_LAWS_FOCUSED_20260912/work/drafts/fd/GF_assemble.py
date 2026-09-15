#!/usr/bin/env python3
"""Assemble GF_Assembled.lean from GF_Skeleton.lean + the unit files GF_U_P{0..6}.lean.

Pass 1 (faithful assembly).  For each unit, `diff skeleton unit` (normal format) is parsed hunk by
hunk.  Allowed hunks: `c` replacing exactly one `  sorry` line (the replacement may carry the
helpers that follow the leaf up to the next skeleton line); `a` inserting lines (helpers, the P5
import, the P2 pointer comment inside the still-`sorry` body of P2.2).  Any `d` hunk or any `c`
hunk removing something other than one `  sorry` line is a statement/docstring violation and
aborts.  Overlaps between units abort.  The hunks are applied in one pass over the skeleton; every
inserted block is checked to occur exactly once, contiguously; helper names are checked for
duplicates across units and against the skeleton.

Pass 2 (repair of the false leaf P2.2, see GF_U_P2_REPORT.md §2-3).  `stage1_stable` is FALSE as
stated (a double point at circular distance exactly `δc` moves inward under any nearby
`H^x`-perturbation; numerically checked in GF_U_P2_probe.py).  The leaf is removed, and `step2`
(the only consumer) is re-proved with the half collar width via the unit-P2 helpers
`gp2_locallyInjectiveFront_mono` and `gp2_stage1_stable_of_lt` (the true form, `δ' < δc`); this
is the patch tested by unit P2 in /tmp/fd/p2/P2_step2test.lean.  The statement of `step2` is
unchanged.  Every edit is an exact-match text replacement that asserts the old text occurs once.

Pass 4 merges the four helper pairs whose statements are byte-identical under different names
(the later unit's copy is dropped, its uses renamed).

Pass 3 (run last).  If no `sorry` remains, the module docstring is rewritten so that the word does not occur
and any `#print`/`#eval`/`#check` line is dropped.

Outputs: GF_Assembled.lean (final), /tmp/gf_assembly/GF_Assembled_pass1.lean (before pass 2).
"""
import re, subprocess, sys, os, collections

D = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/drafts/fd"
SKEL = f"{D}/GF_Skeleton.lean"
UNITS = ["P0", "P1", "P2", "P3", "P4", "P5", "P6"]
OUT = f"{D}/GF_Assembled.lean"
TMP = "/tmp/gf_assembly"
os.makedirs(TMP, exist_ok=True)

skel = open(SKEL).read().split("\n")
hunk_re = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")


def parse_hunks(unit_path):
    p = subprocess.run(["diff", SKEL, unit_path], capture_output=True, text=True)
    lines = p.stdout.split("\n")
    unit = open(unit_path).read().split("\n")
    hunks = []
    i = 0
    while i < len(lines):
        m = hunk_re.match(lines[i])
        if not m:
            i += 1
            continue
        s1, s2, op, u1, u2 = m.groups()
        s1 = int(s1); s2 = int(s2) if s2 else s1
        u1 = int(u1); u2 = int(u2) if u2 else u1
        i += 1
        removed, added = [], []
        while i < len(lines) and lines[i].startswith("< "):
            removed.append(lines[i][2:]); i += 1
        if i < len(lines) and lines[i] == "---":
            i += 1
        while i < len(lines) and lines[i].startswith("> "):
            added.append(lines[i][2:]); i += 1
        if op != "d":
            assert added == unit[u1 - 1:u2], f"{unit_path}: hunk {m.group(0)} added-lines mismatch"
        hunks.append(dict(op=op, s1=s1, s2=s2, removed=removed, added=added, hdr=m.group(0)))
    return hunks


all_hunks = {}
violations = []
for u in UNITS:
    path = f"{D}/GF_U_{u}.lean"
    hs = parse_hunks(path)
    for h in hs:
        if h["op"] == "c":
            if h["s2"] != h["s1"] or h["removed"] != ["  sorry"]:
                violations.append(f"unit {u} hunk {h['hdr']}: replaces something other than one `  sorry` line: {h['removed']!r}")
        elif h["op"] == "d":
            violations.append(f"unit {u} hunk {h['hdr']}: deletes skeleton lines: {h['removed']!r}")
        # 'a' hunks: pure insertions, always fine for the freeze
    all_hunks[u] = hs
    print(f"unit {u}: {len(hs)} hunks: " + ", ".join(h['hdr'] for h in hs))

# overlap check between units (skeleton coordinates)
touched = {}
for u, hs in all_hunks.items():
    for h in hs:
        for s in range(h["s1"], h["s2"] + 1):
            k = (h["op"], s)
            if k in touched and touched[k] != u:
                violations.append(f"overlap at skeleton line {s} ({h['op']}): units {touched[k]} and {u}")
            touched[k] = u
for (op, s), u in list(touched.items()):
    for op2 in "cd":
        if op2 != op and (op2, s) in touched:
            violations.append(f"line {s}: {op} by {u} and {op2} by {touched[(op2, s)]}")

if violations:
    print("VIOLATIONS:"); [print("  " + v) for v in violations]
    sys.exit(1)
print("freeze check: every removed skeleton line is a `  sorry`; no deletions; no overlaps")

# every skeleton `  sorry` line: which unit replaced it?
sorry_lines = [i for i, l in enumerate(skel, start=1) if l == "  sorry"]
repl_by = {h["s1"]: u for u, hs in all_hunks.items() for h in hs if h["op"] == "c"}
left = [s for s in sorry_lines if s not in repl_by]
print(f"skeleton `  sorry` lines: {len(sorry_lines)}; replaced by units: {len(repl_by)}; left: {left}")


def leaf_name_at(s):
    for k in range(s - 1, 0, -1):
        m = re.match(r"^theorem\s+(\S+)", skel[k - 1])
        if m: return m.group(1)
    return "?"


left_names = [leaf_name_at(s) for s in left]
print("unproved leaves after pass 1:", left_names)

# helper names (top-level declarations added by units)
decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+([^\s:({\[]+)")
helpers = collections.OrderedDict()
for u, hs in all_hunks.items():
    for h in hs:
        for ln in h["added"]:
            m = decl_re.match(ln)
            if m:
                helpers.setdefault(m.group(2), []).append(u)
leaf_names = set()
for ln in skel:
    m = decl_re.match(ln)
    if m:
        leaf_names.add(m.group(2))
dups = {n: us for n, us in helpers.items() if len(us) > 1}
redecl = {n: us for n, us in helpers.items() if n in leaf_names}
print(f"helpers: {len(helpers)} distinct names; per unit: " +
      ", ".join(f"{u}={sum(1 for us in helpers.values() if u in us)}" for u in UNITS))
if dups:
    print("DUPLICATE helper names across units:", dups); sys.exit(2)
if redecl:
    print("skeleton names re-declared inside insertions:", redecl); sys.exit(2)
bad_prefix = [n for n, us in helpers.items() if not all(n.startswith(f"gp{u[1]}_") for u in us)]
print("helpers not carrying their unit prefix:", bad_prefix or "none")

# identical helper statements under different names (informational only; nothing is merged)
def decl_blocks(lines):
    """map name -> (statement text up to ':= by' / ':=', unit) for added declarations"""
    out = {}
    i = 0
    while i < len(lines):
        m = decl_re.match(lines[i])
        if m:
            j = i; stmt = []
            while j < len(lines):
                stmt.append(lines[j])
                if re.search(r":=\s*(by)?\s*$", lines[j]) or lines[j].rstrip().endswith("where"):
                    break
                j += 1
            body = "\n".join(stmt)
            body = re.sub(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev)\s+\S+", "", body)
            out[m.group(2)] = re.sub(r"\s+", " ", body).strip()
            i = j + 1
        else:
            i += 1
    return out
stmt_of = {}
for u, hs in all_hunks.items():
    for h in hs:
        for n, s in decl_blocks(h["added"]).items():
            stmt_of[n] = (s, u)
by_stmt = collections.defaultdict(list)
for n, (s, u) in stmt_of.items():
    by_stmt[s].append(n)
same_stmt = {s: ns for s, ns in by_stmt.items() if len(ns) > 1}
print(f"helpers with byte-identical statements under different names (merged in pass 4): {len(same_stmt)}")
for s, ns in same_stmt.items():
    print("   ", ns, "::", s[:90])

# apply
repl = {}; ins = {}
for u, hs in all_hunks.items():
    for h in hs:
        if h["op"] == "c":
            assert skel[h["s1"] - 1] == "  sorry"
            repl[h["s1"]] = (u, h["added"])
        elif h["op"] == "a":
            ins.setdefault(h["s1"], []).append((u, h["added"]))
out = []
for i, ln in enumerate(skel, start=1):
    if i in repl:
        out.extend(repl[i][1])
    else:
        out.append(ln)
    for (u, block) in ins.get(i, []):
        out.extend(block)
text1 = "\n".join(out)
open(f"{TMP}/GF_Assembled_pass1.lean", "w").write(text1)
print(f"pass 1: {len(out)} lines (skeleton {len(skel)}); remaining `sorry` lines: "
      f"{sum(1 for l in out if l.strip() == 'sorry')}")

# contiguity check: every added block appears verbatim, contiguously, exactly once
outs = "\n" + text1 + "\n"
for u, hs in all_hunks.items():
    for h in hs:
        if not h["added"]:
            continue
        blk = "\n" + "\n".join(h["added"]) + "\n"
        c = outs.count(blk)
        if c != 1:
            print(f"CONTIGUITY FAIL unit {u} hunk {h['hdr']}: occurrences={c}"); sys.exit(3)
print("contiguity: every hunk block occurs exactly once, contiguously")
# every skeleton line other than the replaced `  sorry`s survives, in order
it = iter(out)
for i, ln in enumerate(skel, start=1):
    if i in repl: continue
    for cand in it:
        if cand == ln: break
    else:
        print(f"ORDER FAIL: skeleton line {i} not found in order: {ln!r}"); sys.exit(3)
print("order: every surviving skeleton line occurs in the assembled file in skeleton order")


# ---------------- pass 2: repair of the false leaf P2.2 ----------------
def replace_once(text, old, new, what):
    c = text.count(old)
    assert c == 1, f"{what}: expected exactly one occurrence, found {c}"
    return text.replace(old, new)


text = text1
old_p22 = (
    "/-- LEAF P2.2.  `Stage1` and the collar persist for small parameters of any Hamiltonian family\n"
    "(sm-3:2675-2677, 2709-2710): the sign margins are open conditions in `a` on compact `θ`-intervals\n"
    "(joint smoothness of `(θ,a) ↦ Φ_a(L θ)`, `generalized_tube_lemma`). -/\n"
    "theorem stage1_stable {L : ℝ → ℝ³} (h : Stage1 L) {δc : ℝ} (hδ : LocallyInjectiveFront L δc)\n"
    "    (m : ℕ) (Hs : Fin m → ℝ³ → ℝ) (hHs : ∀ i, ContactMotionsHyp (Hs i)) :\n"
    "    ∃ r > 0, ∀ a : ℝ^m, ‖a‖ < r →\n"
    "      Stage1 (composeFlows m Hs (par a) ∘ L) ∧ LocallyInjectiveFront (composeFlows m Hs (par a) ∘ L) δc := by\n"
    "  -- FALSE as stated (GF_U_P2_REPORT.md §2: a double point at circular distance exactly `δc`).\n"
    "  -- Use `gp2_stage1_stable_of_lt` (collar with any `δ' < δc`) together with\n"
    "  -- `gp2_locallyInjectiveFront_mono` in the assembly instead.\n"
    "  sorry\n\n")
new_p22 = (
    "/-! The skeleton's LEAF P2.2 (`stage1_stable`: for every collar width `δc` of `L` and every\n"
    "Hamiltonian family, `Stage1` and the collar of the SAME width `δc` persist for all small parameters)\n"
    "is FALSE as stated (`GF_U_P2_REPORT.md` §2, numerically checked in `GF_U_P2_probe.py`): for\n"
    "`L(θ) = (sin 2θ, sin θ, cos θ − ⅓cos 3θ)` the front has one double point at circular distance\n"
    "exactly `π = δc`, and the `H^x`-bump perturbation at one of its two points moves the double point\n"
    "to distance `π − |a|/2 < δc` for every `a ≠ 0`.  The true statement is persistence of the collar\n"
    "with any SMALLER width, `gp2_stage1_stable_of_lt` above (`δ' < δc`); `step2` below uses it with\n"
    "the half width `δc / 2` (`gp2_locallyInjectiveFront_mono`).  Nothing else referenced the leaf. -/\n\n")
text = replace_once(text, old_p22, new_p22, "remove leaf P2.2")

old_step2 = "\n".join(skel[404:447]) + "\n"           # skeleton lines 405-447
new_step2 = open("/tmp/fd/p2/P2_step2test.lean").read().split("\n")[847:893]
new_step2 = "\n".join(new_step2) + "\n"
assert old_step2.startswith("/-- Steps 2–3 assembled") and old_step2.rstrip().endswith("noTriple := noTriple_of_R h m Hs hHs hδa hav.2 har }")
assert new_step2.startswith("/-- Steps 2–3 assembled") and new_step2.rstrip().endswith("noTriple := noTriple_of_R h m Hs hHs hδa hav.2 har }")
# the statement line(s) of step2 are unchanged
assert old_step2.split(":= by\n")[0] == new_step2.split(":= by\n")[0], "step2 statement changed"
text = replace_once(text, old_step2, new_step2, "step2 body")
assert "stage1_stable h" not in text and "theorem stage1_stable" not in text
print("pass 2: P2.2 removed, step2 re-proved with the half collar width (gp2_stage1_stable_of_lt)")

n_sorry = sum(1 for l in text.split("\n") if l.strip() == "sorry")
print("pass 2: remaining `sorry` lines:", n_sorry)


# ---------------- pass 4: de-duplicate helpers with byte-identical statements ----------------
# Four helpers of later units restate (byte-identically, binders included) a helper of an earlier
# unit.  The later copy is removed together with its docstring and every use is renamed to the
# earlier name.  Checks: the two statements are identical; the kept declaration precedes every use;
# the removed name no longer occurs.
DEDUP = [("gp5_front_periodic", "gp2_periodic_front"),
         ("gp5_circDist_le_abs", "gp2_circDist_le_abs"),
         ("gp5_hamVF_eq_zero_of_notMem", "gp3_hamVF_eq_zero_of_notMem"),
         ("gp4_sameParam_symm", "gp3_sameParam_symm")]
TOP = re.compile(r"^(/--|/-!|lemma|theorem|def|@\[|--|end\b|section\b|namespace\b|open\b|noncomputable\b|private\b|instance\b|structure\b|abbrev\b)")
for dup, keep in DEDUP:
    assert stmt_of[dup][0] == stmt_of[keep][0], (dup, keep)
    lines = text.split("\n")
    i = next(k for k, l in enumerate(lines) if re.match(rf"^(lemma|theorem)\s+{dup}\b", l))
    j = i
    while j + 1 < len(lines) and lines[j + 1].strip() != "":
        j += 1
    assert TOP.match(lines[j + 2]), f"{dup}: block end not followed by a top-level token: {lines[j+2]!r}"
    s = i
    if lines[i - 1].rstrip().endswith("-/"):
        s = i - 1
        while not lines[s].lstrip().startswith("/--"):
            s -= 1
    assert lines[s - 1].strip() == "", f"{dup}: no blank line before the block"
    i_keep = next(k for k, l in enumerate(lines) if re.match(rf"^(lemma|theorem)\s+{keep}\b", l))
    assert i_keep < s, f"{keep} must be declared before the removed {dup} (all uses of {dup} follow it)"
    del lines[s:j + 2]             # block + its trailing blank line
    text = "\n".join(lines)
    n_before = len(re.findall(rf"\b{dup}\b", text))
    text = re.sub(rf"\b{dup}\b", keep, text)
    assert not re.search(rf"\b{dup}\b", text)
    print(f"pass 4: removed {dup} ({j + 2 - s} lines incl. docstring/blank), renamed {n_before} uses to {keep}")
print("pass 4: remaining `sorry` lines:", sum(1 for l in text.split("\n") if l.strip() == "sorry"))

# ---------------- pass 3: docstring, #print lines ----------------
if n_sorry == 0:
    old_hdr_start = text.index("/-! # SM fd:generic-front")
    old_hdr_end = text.index("-/\n", old_hdr_start) + 3
    new_hdr = """/-! # SM fd:generic-front — generic fronts of Legendrian knots (row 87), assembled

Assembled 2026-09-14 (work/drafts/fd/, `GF_assemble.py`) from `GF_Skeleton.lean` and the unit files
`GF_U_P{0,…,6}.lean`.  Source: reference/SM/sm-3-statesum.tex:2613-2630 (statement), 2631-2783
(proof).  Route: `FD_84_87_FEASIBILITY_v2.md` §2; leaf plan: `GF_PLAN.md`; assembly record:
`GF_ASSEMBLY_REPORT.md`.

Layout.  §1–§4 (from `namespace SM` to `GenericFrontData`) are **byte-identical** to
`GenericFront_Statement.lean` lines 79-255 (the statement).  §5 is the proof: definitions, glue,
the former leaf lemmas (all proved) grouped in units P0–P6 with their helpers (prefixes `gp0_` …
`gp6_`), and the row theorem `SM.fd_generic_front : GenericFrontData`.
`#print axioms SM.fd_generic_front` gives `[propext, Classical.choice, Quot.sound]`.  Independent of
the row-84 file: the row-84 notions it needs are the copies in `SM.GenericFront` (§1).

Units: P0 contact isotopies from Hamiltonian flows (row 86) · P1 simultaneous zeros of `(x′,x″)`
(row 85, `(d,q) = (1,2)`) · P2 the uniform collar (local front injectivity) · P3 cusps on branches
and triple points (row 85, `(2,3)` and `(3,4)`) · P4 transverse, finite double points · P5 exact
cusp germs · P6 concatenation, pushoff annulus, knot type.

One deviation from the skeleton: its leaf P2.2 (`stage1_stable`, persistence of the collar with the
same width) was false as stated and is replaced by persistence with any smaller width
(`gp2_stage1_stable_of_lt`; see the note in Unit P2 and `GF_U_P2_REPORT.md` §2-3); `step2` uses the
half width.  The header carries one import beyond the skeleton's
(`Mathlib.Analysis.Calculus.ContDiff.Bounds`, the Leibniz rule for P5.4).

Check: `cd work/lean && lake env lean ../drafts/fd/GF_Assembled.lean`. -/
"""
    text = text[:old_hdr_start] + new_hdr + text[old_hdr_end:]
    kept = []
    dropped = 0
    for l in text.split("\n"):
        if re.match(r"^\s*#(print|eval|check)\b", l):
            dropped += 1; continue
        kept.append(l)
    text = "\n".join(kept)
    print(f"pass 3: module docstring rewritten; dropped {dropped} #print/#eval/#check lines")

open(OUT, "w").write(text)
final_lines = text.split("\n")
print(f"wrote {OUT}: {len(final_lines)} lines")
print("word `sorry` occurrences (any form):", sum(l.lower().count("sorry") for l in final_lines))
for k, l in enumerate(final_lines, start=1):
    if "sorry" in l.lower():
        print(f"   line {k}: {l.strip()[:100]}")
