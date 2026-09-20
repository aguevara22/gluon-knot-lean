#!/usr/bin/env python3
"""wave2a_assemble.py — wave-2a assembly of the corner chain (2026-09-15).

Same hunk classification as tools/partial_assemble.py (wave 1), generalised:
  * `--base` names the skeleton the units were written against (default Partial_Assembled.lean, the base
    of the W2_* files);
  * every unit is diffed against that base; a hunk is CLEAN iff it is an import line inside the header, a
    pure insertion (helper block) elsewhere, or a `c`-hunk whose removed lines are exactly the `sorry`
    body of a PLAN_FINAL §4 leaf; anything else is a VIOLATION and the unit is rejected;
  * `--expect` maps unit -> (leaf it may prove or '-', helper prefix): a block declaring a top-level name
    outside the unit's prefix (or its prefixed namespaces), a `c`-hunk on another leaf, or any
    `sorry`/`#print`/`#eval`/`#check`/`axiom`/`import`/`set_option` inside an added block is reported as
    a VIOLATION too;
  * after writing the output, every adopted block is located in the output as ONE contiguous slice
    (contiguity check) and its enclosing top-level `section` is reported.

Usage: python3 tools/wave2a_assemble.py [--base Partial_Assembled.lean] [--out Wave2a_Assembled.lean]
         [--units Wave1_Assembled,W2_SGD,W2_SFTC,W2_SFTD]
Prints a JSON summary; exit 1 iff some unit was rejected.
"""
import argparse, json, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
CORNER = HERE.parent
LEAVES = ["sg_isolated_undominated", "sg_daughters_products", "sg_daughters_rotation",
          "s7_sliding_law_at", "s7_bigon_law_at", "s7_universal_extraction", "s7_corner_product",
          "sft_same_sign", "sft_mixed", "sft_loop"]
ROW_THEOREMS = ["cb_singleton", "corner_values", "thm_C_S7", "thm_C_soft"]
# unit -> (leaf it is allowed to prove, helper prefix)
EXPECT = {"Wave1_Assembled": ("s7_corner_product", "s7a_"),
          "W2_SGD": ("sg_daughters_products", "sgd_"),
          "W2_SFTC": ("sft_same_sign", "sftc_"),
          "W2_SFTD": ("sft_loop", "sftd_"),
          "W2_S7A2": (None, "s7a2_")}   # wave 2b: helper-only unit written against Wave1_Assembled.lean
HUNK_RE = re.compile(r"^(\d+)(?:,(\d+))?([acd])(\d+)(?:,(\d+))?$")
DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+|@\[[^\]]*\]\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({\[]+)")
FORBIDDEN = re.compile(r"\bsorry\b|^\s*#(print|eval|check|reduce|exit)\b|^\s*axiom\b|^\s*import\b|^\s*set_option\b", re.M)


def run_diff(a, b):
    p = subprocess.run(["diff", str(a), str(b)], capture_output=True, text=True)
    if p.returncode not in (0, 1):
        raise SystemExit(f"diff failed on {b}: {p.stderr}")
    lines = p.stdout.splitlines(); hunks, k = [], 0
    while k < len(lines):
        m = HUNK_RE.match(lines[k])
        if not m:
            raise SystemExit(f"unparsable diff line in {b.name}: {lines[k]!r}")
        i1 = int(m.group(1)); i2 = int(m.group(2) or i1); kind = m.group(3)
        j1 = int(m.group(4)); j2 = int(m.group(5) or j1); k += 1
        removed, added = [], []
        while k < len(lines) and lines[k].startswith("< "):
            removed.append(lines[k][2:]); k += 1
        if k < len(lines) and lines[k] == "---":
            k += 1
        while k < len(lines) and lines[k].startswith("> "):
            added.append(lines[k][2:]); k += 1
        while k < len(lines) and lines[k].startswith("\\"):
            k += 1
        hunks.append((i1, i2, kind, j1, j2, removed, added))
    return hunks


def decl_of_body(base_lines, idx0):
    for k in range(idx0, -1, -1):
        m = DECL_RE.match(base_lines[k])
        if m:
            return m.group(2)
    return None


def comment_depth_after(line, depth):
    """block-comment depth after scanning `line` (tokens `/-` open, `-/` close; nesting honoured)."""
    i = 0
    while i < len(line) - 1:
        two = line[i:i + 2]
        if two == "/-":
            depth += 1; i += 2
        elif two == "-/" and depth > 0:
            depth -= 1; i += 2
        else:
            i += 1
    return depth


def collect_decls(lines):
    """full names (namespace-tracked) -> [text] ; also returns list of (name, lineidx).  Lines inside a
    block comment / docstring are never read as declarations."""
    ns, out, order, depth = [], {}, [], 0
    for k, l in enumerate(lines):
        if depth > 0:
            depth = comment_depth_after(l, depth); continue
        depth = comment_depth_after(l, 0)
        s = l.strip()
        if s.startswith("--"):
            continue
        if s.startswith("namespace "):
            ns.extend(s.split()[1].split("."))
        elif s.startswith("end ") and ns:
            nm = s.split()[1].split(".")
            if ns[-len(nm):] == nm:
                del ns[-len(nm):]
        m = DECL_RE.match(l)
        if m:
            name = ".".join(ns + [m.group(2)])
            e = k
            while e < len(lines) and lines[e].strip() != "":
                e += 1
            out.setdefault(name, []).append("\n".join(lines[k:e]))
            order.append((name, k))
    return out, order


def classify(unit, base_lines, hunks, n_import_lines):
    imports, blocks, bodies, violations, notes = [], [], [], [], []
    exp_leaf, exp_prefix = EXPECT.get(unit, (None, None))
    for (i1, i2, kind, j1, j2, removed, added) in hunks:
        if kind == "a":
            if all(l.startswith("import ") for l in added) and i1 <= n_import_lines:
                imports.extend(added); notes.append(f"import line(s) {added} inserted after base line {i1}")
            else:
                blk = {"anchor": i1, "lines": added, "unit": unit, "hunk": f"{i1}a{j1},{j2}"}
                blocks.append(blk)
                # audit the block
                txt = "\n".join(added)
                for m in FORBIDDEN.finditer(txt):
                    ln = txt[:m.start()].count("\n")
                    violations.append(f"{unit}: forbidden token {m.group(0)!r} inside added block (block line {ln+1}: {added[ln].strip()[:80]!r})")
                decls, order = collect_decls(added)
                blk["decls"] = [n for n, _ in order]
                if exp_prefix:
                    bad = [n for n in blk["decls"]
                           if not any(part.startswith(exp_prefix) for part in n.split("."))]
                    if bad:
                        violations.append(f"{unit}: block declares names outside prefix {exp_prefix!r}: {bad}")
                dup = [n for n, t in decls.items() if len(t) > 1]
                if dup:
                    violations.append(f"{unit}: block declares a name twice: {dup}")
        elif kind == "d":
            violations.append(f"{unit}: deletes frozen line(s) {i1}-{i2}: {removed}")
        elif kind == "c":
            leaf = decl_of_body(base_lines, i1 - 1)
            if removed == ["  sorry"]:
                if leaf in LEAVES:
                    if exp_leaf and leaf != exp_leaf:
                        violations.append(f"{unit}: replaces the sorry of leaf {leaf} (line {i1}) but is expected to prove {exp_leaf}")
                    txt = "\n".join(added)
                    for m in FORBIDDEN.finditer(txt):
                        violations.append(f"{unit}: forbidden token {m.group(0)!r} inside the body of {leaf}")
                    bodies.append({"line": i1, "leaf": leaf, "lines": added, "unit": unit, "hunk": f"{i1}c{j1},{j2}"})
                elif leaf in ROW_THEOREMS:
                    violations.append(f"{unit}: replaces the sorry of ROW THEOREM {leaf} (line {i1}) — not allowed")
                else:
                    violations.append(f"{unit}: replaces a sorry that is not a leaf body ({leaf}, line {i1})")
            elif (len(removed) == 2 and removed[1] == "  sorry" and removed[0].endswith(" := by")
                  and added and added[0] == removed[0][:-3] and leaf in LEAVES):
                term = added[1:]
                if len(term) == 1 and term[0].startswith("  "):
                    new_body = ["  exact " + term[0].strip()]
                    notes.append(f"{leaf}: term-mode body normalised to `:= by` / `exact …`")
                else:
                    new_body = ["  exact ("] + term + ["  )"]
                    notes.append(f"{leaf}: multi-line term-mode body wrapped in `exact ( … )`")
                bodies.append({"line": i1 + 1, "leaf": leaf, "lines": new_body, "unit": unit, "hunk": f"{i1},{i2}c{j1},{j2}"})
            else:
                violations.append(f"{unit}: changes frozen line(s) {i1}-{i2} (decl {leaf}): removed={removed!r}")
    return imports, blocks, bodies, violations, notes


def enclosing_section(lines, idx):
    """nearest preceding top-level `section X` not yet closed (depth tracking on column-0 section/end)."""
    depth, k = 0, idx
    while k >= 0:
        l = lines[k]
        if l.startswith("end ") or l == "end":
            depth += 1
        elif l.startswith("section") or l.startswith("namespace "):
            if depth == 0:
                return l.strip()
            depth -= 1
        k -= 1
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default=str(CORNER / "Partial_Assembled.lean"))
    ap.add_argument("--out", default=str(CORNER / "Wave2a_Assembled.lean"))
    ap.add_argument("--units", default="Wave1_Assembled,W2_SGD,W2_SFTC,W2_SFTD")
    args = ap.parse_args()
    base = pathlib.Path(args.base)
    units = [u for u in args.units.split(",") if u]
    base_lines = base.read_text(encoding="utf-8").split("\n")
    if base_lines and base_lines[-1] == "":
        base_lines.pop()
    n_import_lines = 0
    while n_import_lines < len(base_lines) and base_lines[n_import_lines].startswith("import "):
        n_import_lines += 1

    summary = {"base": str(base), "adopted_units": [], "rejected_units": {}, "missing_units": [],
               "imports_added": [], "helper_blocks": [], "leaf_bodies": [], "notes": [],
               "dedup_dropped": [], "renamed": [], "contiguity": []}
    all_imports, all_blocks, all_bodies = [], [], []
    for u in units:
        f = CORNER / f"{u}.lean"
        if not f.exists():
            summary["missing_units"].append(u); continue
        hunks = run_diff(base, f)
        imports, blocks, bodies, violations, notes = classify(u, base_lines, hunks, n_import_lines)
        removed_total = [l for (_, _, kind, _, _, removed, _) in hunks for l in removed]
        summary["notes"].append(f"{u}: hunks={[f'{i1}{kind}{j1}' + (f',{j2}' if j2 != j1 else '') for (i1, i2, kind, j1, j2, r, a) in hunks]} removed_lines={removed_total!r}")
        if violations:
            summary["rejected_units"][u] = violations; continue
        summary["adopted_units"].append(u)
        summary["notes"].extend(f"{u}: {n}" for n in notes)
        all_imports.extend(imports); all_blocks.extend(blocks); all_bodies.extend(bodies)
        for b in blocks:
            summary["helper_blocks"].append({"unit": u, "hunk": b["hunk"], "anchor_after_base_line": b["anchor"],
                                             "n_lines": len(b["lines"]), "n_decls": len(b["decls"]),
                                             "decls_head": b["decls"][:5]})
        for b in bodies:
            summary["leaf_bodies"].append({"unit": u, "hunk": b["hunk"], "leaf": b["leaf"], "n_lines": len(b["lines"])})

    seen, kept_bodies = {}, []
    for b in all_bodies:
        if b["leaf"] in seen:
            summary["notes"].append(f"CONFLICT: {b['unit']} also proves {b['leaf']} (kept {seen[b['leaf']]}'s body)"); continue
        seen[b["leaf"]] = b["unit"]; kept_bodies.append(b)

    base_decls, _ = collect_decls(base_lines)
    known = {n: (base.stem, t[0]) for n, t in base_decls.items()}
    for b in all_blocks:
        decls, _ = collect_decls(b["lines"])
        for name, texts in decls.items():
            if name in known:
                owner, text = known[name]
                if text == texts[0]:
                    b["lines"] = drop_decl(b["lines"], name.split(".")[-1])
                    summary["dedup_dropped"].append({"name": name, "kept_from": owner, "dropped_from": b["unit"]})
                else:
                    new = name.split(".")[-1] + "_" + b["unit"].lower()
                    b["lines"] = [re.sub(r"\b" + re.escape(name.split(".")[-1]) + r"\b", new, l) for l in b["lines"]]
                    summary["renamed"].append({"name": name, "unit": b["unit"], "new": new, "clashes_with": owner})
            else:
                known[name] = (b["unit"], texts[0])

    body_at = {b["line"] - 1: b["lines"] for b in kept_bodies}
    blocks_after = {}
    for b in all_blocks:
        blocks_after.setdefault(b["anchor"] - 1, []).append(b)
    out = []
    for k, line in enumerate(base_lines):
        if k == n_import_lines - 1:
            out.append(line)
            for imp in all_imports:
                if imp not in base_lines[:n_import_lines] and imp not in out:
                    out.append(imp); summary["imports_added"].append(imp)
            continue
        if k in body_at:
            out.extend(body_at[k])
        else:
            out.append(line)
        for b in blocks_after.get(k, []):
            lines = b["lines"]
            if out and out[-1].strip() != "" and lines and lines[0].strip() != "":
                out.append("")
            b["out_start"] = len(out)
            out.extend(lines)
            nxt = base_lines[k + 1] if k + 1 < len(base_lines) else ""
            if lines and lines[-1].strip() != "" and nxt.strip() != "":
                out.append("")
    text = "\n".join(out) + "\n"
    pathlib.Path(args.out).write_text(text, encoding="utf-8")

    # contiguity: each block's text occurs exactly once in the output, as one slice
    for b in all_blocks:
        blk = "\n".join(b["lines"])
        cnt = text.count("\n" + blk + "\n")
        s = b.get("out_start", -1)
        ok = cnt == 1 and out[s:s + len(b["lines"])] == b["lines"]
        summary["contiguity"].append({"unit": b["unit"], "out_lines": f"{s + 1}-{s + len(b['lines'])}", "occurrences": cnt,
                                      "contiguous": ok, "section": enclosing_section(out, s)})
    for b in kept_bodies:
        # locate the body in the output
        blk = "\n".join(b["lines"])
        summary["contiguity"].append({"unit": b["unit"], "leaf": b["leaf"], "occurrences": text.count("\n" + blk + "\n")})
    summary["out"] = args.out; summary["out_lines"] = len(out)
    summary["sorry_lines"] = sum(1 for l in out if "sorry" in l)
    summary["sorry_line_numbers"] = [k + 1 for k, l in enumerate(out) if "sorry" in l]
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    sys.exit(1 if summary["rejected_units"] else 0)


def drop_decl(lines, short_name):
    res, k = [], 0
    while k < len(lines):
        m = DECL_RE.match(lines[k])
        if m and m.group(2) == short_name:
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
