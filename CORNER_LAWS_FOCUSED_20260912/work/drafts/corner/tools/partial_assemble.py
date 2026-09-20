#!/usr/bin/env python3
"""partial_assemble.py — assemble Partial_Assembled.lean from Statements_FINAL.lean and the returned
wave-1 unit files U_*.lean (2026-09-15).

For every unit file the script computes the GNU-diff hunks against Statements_FINAL.lean and CLASSIFIES
each hunk:
  * `import` insertion (an added `import X` line inside the import header)  -> adopted (imports are unioned);
  * pure insertion (`Na…`) anywhere else                                    -> a helper block, adopted;
  * `N c …` hunk whose removed lines are exactly the `sorry` body of a LEAF   -> the leaf's proof body, adopted
    (the accepted shapes are `  sorry` alone, or `<statement tail> := by` + `  sorry` replaced by
    `<statement tail> :=` + a one-line term, which is normalised back to `:= by` / `  exact <term>` so the
    frozen line stays byte-identical);
  * anything else (a deleted or changed frozen line)                        -> a VIOLATION: the unit is NOT
    adopted and the violation is reported.
Then it writes Statements_FINAL.lean with every clean hunk applied: leaf bodies replaced in place, every
helper block inserted contiguously at the unit's own anchor (blocks sharing an anchor follow in unit order),
identical duplicated top-level declarations dropped, clashing names renamed with a unit suffix.

Usage:  python3 tools/partial_assemble.py [--out Partial_Assembled.lean] [--units U_SGA,U_SGB,...]
Prints a JSON summary on stdout; exit code 0 even when a unit is rejected (the report says so).
"""
import argparse
import json
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
CORNER = HERE.parent
BASE = CORNER / "Statements_FINAL.lean"
DEFAULT_UNITS = ["U_SGA", "U_SGB", "U_SGC", "U_SGE", "U_SFTA", "U_SFTB",
                 "U_S7B", "U_S7C", "U_S7D", "U_S7G", "U_S7H", "U_S7I"]
# the ten unit leaves of PLAN_FINAL §4 (frozen statements whose `sorry` bodies a unit may replace)
LEAVES = ["sg_isolated_undominated", "sg_daughters_products", "sg_daughters_rotation",
          "s7_sliding_law_at", "s7_bigon_law_at", "s7_universal_extraction", "s7_corner_product",
          "sft_same_sign", "sft_mixed", "sft_loop"]
# the four §6 row theorems: their `sorry` may NOT be replaced by a unit
ROW_THEOREMS = ["cb_singleton", "corner_values", "thm_C_S7", "thm_C_soft"]

HUNK_RE = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")
DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+|@\[[^\]]*\]\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({\[]+)")


def run_diff(a: pathlib.Path, b: pathlib.Path):
    """GNU diff in normal format; returns list of (i1, i2, kind, j1, j2, removed, added) with 1-based
    inclusive ranges as diff prints them (for `a` hunks i1 == i2 is the line AFTER which to insert)."""
    p = subprocess.run(["diff", str(a), str(b)], capture_output=True, text=True)
    if p.returncode not in (0, 1):
        raise SystemExit(f"diff failed on {b}: {p.stderr}")
    lines = p.stdout.splitlines()
    hunks, k = [], 0
    while k < len(lines):
        m = HUNK_RE.match(lines[k])
        if not m:
            raise SystemExit(f"unparsable diff line in {b.name}: {lines[k]!r}")
        i1 = int(m.group(1)); i2 = int(m.group(2) or i1); kind = m.group(3)
        j1 = int(m.group(4)); j2 = int(m.group(5) or j1)
        k += 1
        removed, added = [], []
        while k < len(lines) and lines[k].startswith("< "):
            removed.append(lines[k][2:]); k += 1
        if k < len(lines) and lines[k] == "---":
            k += 1
        while k < len(lines) and lines[k].startswith("> "):
            added.append(lines[k][2:]); k += 1
        # `diff` prints "\ No newline at end of file" occasionally
        while k < len(lines) and lines[k].startswith("\\"):
            k += 1
        hunks.append((i1, i2, kind, j1, j2, removed, added))
    return hunks


def decl_of_body(base_lines, idx0):
    """Name of the declaration whose body contains base line idx0 (0-based): scan backwards for a
    declaration keyword."""
    for k in range(idx0, -1, -1):
        m = DECL_RE.match(base_lines[k])
        if m:
            return m.group(2)
    return None


def classify(unit, base_lines, hunks, n_import_lines):
    """Return (imports, blocks, bodies, violations, notes)."""
    imports, blocks, bodies, violations, notes = [], [], [], [], []
    for (i1, i2, kind, j1, j2, removed, added) in hunks:
        if kind == "a":
            if all(l.startswith("import ") for l in added) and i1 <= n_import_lines:
                imports.extend(added)
                notes.append(f"import line(s) {added} inserted after base line {i1}")
            else:
                blocks.append({"anchor": i1, "lines": added, "unit": unit,
                               "hunk": f"{i1}a{j1},{j2}"})
        elif kind == "d":
            violations.append(f"{unit}: deletes frozen line(s) {i1}-{i2}: {removed}")
        elif kind == "c":
            leaf = decl_of_body(base_lines, i1 - 1)
            if removed == ["  sorry"]:
                if leaf in LEAVES:
                    bodies.append({"line": i1, "leaf": leaf, "lines": added, "unit": unit,
                                   "hunk": f"{i1}c{j1},{j2}"})
                elif leaf in ROW_THEOREMS:
                    violations.append(f"{unit}: replaces the sorry of ROW THEOREM {leaf} (line {i1}) — not allowed")
                else:
                    violations.append(f"{unit}: replaces a sorry that is not a leaf body ({leaf}, line {i1})")
            elif (len(removed) == 2 and removed[1] == "  sorry" and removed[0].endswith(" := by")
                  and added and added[0] == removed[0][:-3] and leaf in LEAVES):
                term = added[1:]
                if len(term) == 1 and term[0].startswith("  "):
                    new_body = ["  exact " + term[0].strip()]
                    notes.append(f"{leaf}: term-mode body `{term[0].strip()}` normalised to `:= by` / `exact …` "
                                 f"so the frozen statement line {i1} stays byte-identical")
                else:
                    new_body = ["  exact (" ] + term + ["  )"]
                    notes.append(f"{leaf}: multi-line term-mode body wrapped in `exact ( … )`")
                bodies.append({"line": i1 + 1, "leaf": leaf, "lines": new_body, "unit": unit,
                               "hunk": f"{i1},{i2}c{j1},{j2}"})
            else:
                violations.append(f"{unit}: changes frozen line(s) {i1}-{i2} (decl {leaf}): removed={removed!r}")
    return imports, blocks, bodies, violations, notes


def collect_decls(lines):
    """Full declaration names (with namespace tracking) declared in a list of lines, with their text
    (declaration line to next blank line) for de-duplication."""
    ns, out = [], {}
    for k, l in enumerate(lines):
        s = l.strip()
        if s.startswith("namespace "):
            ns.append(s.split()[1])
        elif s.startswith("end ") and ns and s.split()[1] == ns[-1]:
            ns.pop()
        m = DECL_RE.match(l)
        if m:
            name = ".".join(ns + [m.group(2)])
            e = k
            while e < len(lines) and lines[e].strip() != "":
                e += 1
            out.setdefault(name, []).append("\n".join(lines[k:e]))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(CORNER / "Partial_Assembled.lean"))
    ap.add_argument("--units", default=",".join(DEFAULT_UNITS))
    args = ap.parse_args()
    units = [u for u in args.units.split(",") if u]

    base_lines = BASE.read_text(encoding="utf-8").split("\n")
    if base_lines and base_lines[-1] == "":
        base_lines.pop()  # trailing newline
    n_import_lines = 0
    while n_import_lines < len(base_lines) and base_lines[n_import_lines].startswith("import "):
        n_import_lines += 1

    summary = {"base": str(BASE), "adopted_units": [], "rejected_units": {}, "missing_units": [],
               "imports_added": [], "helper_blocks": [], "leaf_bodies": [], "notes": [],
               "dedup_dropped": [], "renamed": []}
    all_imports, all_blocks, all_bodies = [], [], []
    for u in units:
        f = CORNER / f"{u}.lean"
        if not f.exists():
            summary["missing_units"].append(u)
            continue
        hunks = run_diff(BASE, f)
        imports, blocks, bodies, violations, notes = classify(u, base_lines, hunks, n_import_lines)
        if violations:
            summary["rejected_units"][u] = violations
            continue
        summary["adopted_units"].append(u)
        summary["notes"].extend(f"{u}: {n}" for n in notes)
        all_imports.extend(imports)
        all_blocks.extend(blocks)
        all_bodies.extend(bodies)
        for b in blocks:
            summary["helper_blocks"].append({"unit": u, "hunk": b["hunk"], "anchor_after_line": b["anchor"],
                                             "n_lines": len(b["lines"])})
        for b in bodies:
            summary["leaf_bodies"].append({"unit": u, "hunk": b["hunk"], "leaf": b["leaf"],
                                           "n_lines": len(b["lines"])})

    # leaf-body conflicts: two units proving the same leaf -> keep the first, report
    seen = {}
    kept_bodies = []
    for b in all_bodies:
        if b["leaf"] in seen:
            summary["notes"].append(f"CONFLICT: {b['unit']} also proves {b['leaf']} (kept {seen[b['leaf']]}'s body)")
            continue
        seen[b["leaf"]] = b["unit"]
        kept_bodies.append(b)

    # de-duplication / clash handling of top-level names across blocks
    base_decls = collect_decls(base_lines)
    known = {n: ("Statements_FINAL", t[0]) for n, t in base_decls.items()}
    for b in all_blocks:
        decls = collect_decls(b["lines"])
        for name, texts in decls.items():
            if name in known:
                owner, text = known[name]
                if text == texts[0]:
                    # identical helper: drop it from this block
                    b["lines"] = drop_decl(b["lines"], name.split(".")[-1])
                    summary["dedup_dropped"].append({"name": name, "kept_from": owner, "dropped_from": b["unit"]})
                else:
                    new = name.split(".")[-1] + "_" + b["unit"].lower()
                    b["lines"] = [re.sub(r"\b" + re.escape(name.split(".")[-1]) + r"\b", new, l) for l in b["lines"]]
                    summary["renamed"].append({"name": name, "unit": b["unit"], "new": new, "clashes_with": owner})
            else:
                known[name] = (b["unit"], texts[0])

    # assemble
    body_at = {}
    for b in kept_bodies:
        body_at[b["line"] - 1] = b["lines"]
    blocks_after = {}
    for b in all_blocks:
        blocks_after.setdefault(b["anchor"] - 1, []).append(b)  # anchor is 1-based "after line N"

    out = []
    for k, line in enumerate(base_lines):
        if k == n_import_lines - 1:
            out.append(line)
            for imp in all_imports:
                if imp not in base_lines[:n_import_lines] and imp not in out:
                    out.append(imp)
                    summary["imports_added"].append(imp)
            continue
        if k in body_at:
            out.extend(body_at[k])
        else:
            out.append(line)
        for b in blocks_after.get(k, []):
            lines = b["lines"]
            if out and out[-1].strip() != "" and lines and lines[0].strip() != "":
                out.append("")
            out.extend(lines)
            nxt = base_lines[k + 1] if k + 1 < len(base_lines) else ""
            if lines and lines[-1].strip() != "" and nxt.strip() != "":
                out.append("")
    # anything anchored after the last line
    for b in blocks_after.get(len(base_lines) - 1, []):
        pass  # already handled in the loop (k == len-1)

    text = "\n".join(out) + "\n"
    pathlib.Path(args.out).write_text(text, encoding="utf-8")
    summary["out"] = args.out
    summary["out_lines"] = len(out)
    summary["sorry_lines"] = sum(1 for l in out if "sorry" in l)
    print(json.dumps(summary, indent=2, ensure_ascii=False))


def drop_decl(lines, short_name):
    """Remove the declaration `short_name` (with its docstring) from a block: from the docstring/decl line
    to the next blank line."""
    res, k = [], 0
    while k < len(lines):
        m = DECL_RE.match(lines[k])
        if m and m.group(2) == short_name:
            # drop preceding docstring
            while res and (res[-1].strip().startswith("/--") or (res and not res[-1].strip().endswith("-/") and
                           any(x.strip().startswith("/--") for x in res[-6:]))):
                res.pop()
                if res and res[-1].strip() == "":
                    break
            while k < len(lines) and lines[k].strip() != "":
                k += 1
            continue
        res.append(lines[k]); k += 1
    return res


if __name__ == "__main__":
    main()
