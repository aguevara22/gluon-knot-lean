#!/usr/bin/env python3
"""corner_assemble.py — merge assembly of the corner chain (waves 1 + 2a + 2b), 2026-09-15.

Output: Corner_Assembled.lean = Wave1_Assembled.lean + every clean wave-2a hunk + every clean wave-2b hunk.

Every unit is diffed against ITS OWN base (the file it was written against), and every hunk is classified
exactly as in tools/wave2a_assemble.py:
  * an `a`-hunk is a helper block (pure insertion) — audited: every top-level declaration carries one of the
    unit's prefixes (or lives in a namespace carrying it), no `sorry` / `#print` / `#eval` / `#check` / `axiom` /
    `import` / `set_option` inside, no name declared twice;
  * a `c`-hunk is CLEAN iff its removed lines are exactly the `  sorry` body of one of the unit's OWN leaves
    (PLAN_FINAL §4), located by scanning back in the base to the enclosing declaration;
  * anything else (a `d`-hunk, a changed frozen line, another unit's leaf, a §6 row theorem) is a VIOLATION and
    the unit is rejected (nothing of it is adopted).
The clean hunks are then applied SEQUENTIALLY on a line-id model: each line of the growing output has a unique
id, every base file carries a map line -> id (Wave1's map is given; a unit whose own file is the base of a later
unit — W2_S7A2 for W2_S7E — has its map recorded at the moment the output is byte-identical to it, which is
verified).  Anchors therefore resolve by content, never by line arithmetic.  After the assembly: import header
unchanged / unioned, contiguity of every block (each occurs exactly once, as one slice), no declaration name
twice in the output (identical duplicates would be dropped, differing ones renamed `<name>_<unit>` — both
reported), `sorry` line list, and the enclosing section of every block.

Units of this merge and their bases:
  W2_S7A2          base Wave1_Assembled.lean   helper unit, prefix s7a2_  (no leaf)
  W2_S7E           base W2_S7A2.lean           leaf s7_sliding_law_at allowed, prefix s7e_
  Wave2a_Assembled base Wave1_Assembled.lean   the audited 2a product = W2_SGD + W2_SFTC + W2_SFTD rebased
                                              (leaves sg_daughters_products, sft_same_sign, sft_loop;
                                              prefixes sgd_, sftc_, sftd_)
Audit-only (classified against Partial_Assembled.lean, not applied; their blocks/bodies must equal the 2a hunks):
  W2_SGD, W2_SFTC, W2_SFTD.

Usage: python3 tools/corner_assemble.py [--out Corner_Assembled.lean]
Prints a JSON summary; exit 1 iff some unit was rejected or a consistency check failed.
"""
import argparse, json, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
CORNER = HERE.parent
sys.path.insert(0, str(HERE))
from wave2a_assemble import (LEAVES, ROW_THEOREMS, HUNK_RE, DECL_RE, FORBIDDEN, run_diff, decl_of_body,
                             collect_decls, enclosing_section)

# unit -> (base file stem, allowed leaves, allowed prefixes)
UNITS = [
    ("W2_S7A2", "Wave1_Assembled", set(), ("s7a2_",)),
    ("W2_S7E", "W2_S7A2", {"s7_sliding_law_at"}, ("s7e_",)),
    ("Wave2a_Assembled", "Wave1_Assembled", {"sg_daughters_products", "sft_same_sign", "sft_loop"},
     ("sgd_", "sftc_", "sftd_")),
]
AUDIT_ONLY = [
    ("W2_SGD", "Partial_Assembled", {"sg_daughters_products"}, ("sgd_",)),
    ("W2_SFTC", "Partial_Assembled", {"sft_same_sign"}, ("sftc_",)),
    ("W2_SFTD", "Partial_Assembled", {"sft_loop"}, ("sftd_",)),
]


def read_lines(p):
    ls = p.read_text(encoding="utf-8").split("\n")
    if ls and ls[-1] == "":
        ls.pop()
    return ls


def classify(unit, base_lines, hunks, n_import_lines, leaves_ok, prefixes):
    imports, blocks, bodies, violations, notes = [], [], [], [], []
    for (i1, i2, kind, j1, j2, removed, added) in hunks:
        if kind == "a":
            if all(l.startswith("import ") for l in added) and i1 <= n_import_lines:
                imports.extend(added); notes.append(f"import line(s) {added} inserted after base line {i1}")
                continue
            blk = {"anchor": i1, "lines": added, "unit": unit, "hunk": f"{i1}a{j1},{j2}"}
            blocks.append(blk)
            txt = "\n".join(added)
            for m in FORBIDDEN.finditer(txt):
                ln = txt[:m.start()].count("\n")
                violations.append(f"{unit}: forbidden token {m.group(0)!r} inside added block "
                                  f"(block line {ln + 1}: {added[ln].strip()[:80]!r})")
            decls, order = collect_decls(added)
            blk["decls"] = [n for n, _ in order]
            bad = [n for n in blk["decls"] if not any(part.startswith(p) for part in n.split(".") for p in prefixes)]
            if bad:
                violations.append(f"{unit}: block declares names outside prefixes {prefixes}: {bad}")
            dup = [n for n, t in decls.items() if len(t) > 1]
            if dup:
                violations.append(f"{unit}: block declares a name twice: {dup}")
        elif kind == "d":
            violations.append(f"{unit}: deletes base line(s) {i1}-{i2}: {removed}")
        else:  # 'c'
            leaf = decl_of_body(base_lines, i1 - 1)
            if removed == ["  sorry"]:
                if leaf in LEAVES:
                    if leaf not in leaves_ok:
                        violations.append(f"{unit}: replaces the sorry of leaf {leaf} (line {i1}) — not this unit's leaf")
                    txt = "\n".join(added)
                    for m in FORBIDDEN.finditer(txt):
                        violations.append(f"{unit}: forbidden token {m.group(0)!r} inside the body of {leaf}")
                    bodies.append({"line": i1, "leaf": leaf, "lines": added, "unit": unit, "hunk": f"{i1}c{j1},{j2}"})
                elif leaf in ROW_THEOREMS:
                    violations.append(f"{unit}: replaces the sorry of ROW THEOREM {leaf} (line {i1}) — not allowed")
                else:
                    violations.append(f"{unit}: replaces a sorry that is not a leaf body ({leaf}, line {i1})")
            elif (len(removed) == 2 and removed[1] == "  sorry" and removed[0].endswith(" := by")
                  and added and added[0] == removed[0][:-3] and leaf in LEAVES and leaf in leaves_ok):
                term = added[1:]
                new_body = (["  exact " + term[0].strip()] if len(term) == 1 and term[0].startswith("  ")
                            else ["  exact ("] + term + ["  )"])
                notes.append(f"{leaf}: term-mode body normalised to `:= by` / `exact …`")
                bodies.append({"line": i1 + 1, "leaf": leaf, "lines": new_body, "unit": unit, "hunk": f"{i1},{i2}c{j1},{j2}"})
            else:
                violations.append(f"{unit}: changes base line(s) {i1}-{i2} (decl {leaf}): removed={removed!r}")
    return imports, blocks, bodies, violations, notes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(CORNER / "Corner_Assembled.lean"))
    args = ap.parse_args()
    summary = {"base": "Wave1_Assembled.lean", "adopted_units": [], "rejected_units": {}, "audit_only": {},
               "imports_added": [], "helper_blocks": [], "leaf_bodies": [], "notes": [], "dedup_dropped": [],
               "renamed": [], "contiguity": [], "checks": {}}
    failed = False

    # ---- audit-only units (2a units against their own base) -------------------------------------------------
    audit_blocks, audit_bodies = [], []
    for unit, base, leaves_ok, prefixes in AUDIT_ONLY:
        bl = read_lines(CORNER / f"{base}.lean")
        n_imp = 0
        while n_imp < len(bl) and bl[n_imp].startswith("import "):
            n_imp += 1
        hunks = run_diff(CORNER / f"{base}.lean", CORNER / f"{unit}.lean")
        imports, blocks, bodies, violations, notes = classify(unit, bl, hunks, n_imp, leaves_ok, prefixes)
        removed_total = [l for h in hunks for l in h[5]]
        summary["audit_only"][unit] = {
            "base": f"{base}.lean",
            "hunks": [f"{h[0]}{h[2]}{h[3]}" + (f",{h[4]}" if h[4] != h[3] else "") for h in hunks],
            "removed_lines": removed_total, "violations": violations, "imports": imports,
            "blocks": [{"hunk": b["hunk"], "n_lines": len(b["lines"]), "n_decls": len(b["decls"])} for b in blocks],
            "bodies": [{"hunk": b["hunk"], "leaf": b["leaf"], "n_lines": len(b["lines"])} for b in bodies],
            "verdict": "clean" if not violations else "VIOLATION"}
        if violations:
            failed = True
        audit_blocks.extend(blocks); audit_bodies.extend(bodies)

    # ---- the merge units ------------------------------------------------------------------------------------
    wave1 = CORNER / "Wave1_Assembled.lean"
    base_lines = read_lines(wave1)
    n_import_lines = 0
    while n_import_lines < len(base_lines) and base_lines[n_import_lines].startswith("import "):
        n_import_lines += 1
    out = list(base_lines)
    ids = list(range(len(out)))                       # unique id per output line
    next_id = len(out)
    line_map = {"Wave1_Assembled": {k + 1: k for k in range(len(out))}}   # base stem -> {line no -> id}
    all_blocks, all_bodies, all_imports = [], [], []
    inserted_after = {}

    def idx_of(id_):
        return ids.index(id_)

    for unit, base, leaves_ok, prefixes in UNITS:
        uf = CORNER / f"{unit}.lean"
        bf = CORNER / f"{base}.lean"
        bl = read_lines(bf)
        n_imp = 0
        while n_imp < len(bl) and bl[n_imp].startswith("import "):
            n_imp += 1
        hunks = run_diff(bf, uf)
        imports, blocks, bodies, violations, notes = classify(unit, bl, hunks, n_imp, leaves_ok, prefixes)
        removed_total = [l for h in hunks for l in h[5]]
        summary["notes"].append(f"{unit} (base {base}.lean): hunks="
                                f"{[f'{h[0]}{h[2]}{h[3]}' + (f',{h[4]}' if h[4] != h[3] else '') for h in hunks]} "
                                f"removed_lines={removed_total!r}")
        if violations:
            summary["rejected_units"][unit] = violations; failed = True; continue
        if base not in line_map:
            summary["rejected_units"][unit] = [f"base {base} is not available as a line map (its unit was rejected?)"]
            failed = True; continue
        summary["adopted_units"].append(unit)
        summary["notes"].extend(f"{unit}: {n}" for n in notes)
        bmap = line_map[base]
        # imports (union into the header)
        for imp in imports:
            if imp not in out[:n_import_lines] and imp not in all_imports:
                all_imports.append(imp)
        # bodies: replace the `  sorry` line (by id) — verify the target line is still `  sorry`
        for b in bodies:
            k = idx_of(bmap[b["line"]])
            if out[k] != "  sorry":
                summary["rejected_units"].setdefault(unit, []).append(
                    f"body target for {b['leaf']} (base line {b['line']}) is no longer `  sorry`: {out[k]!r} "
                    f"(already proved by another unit — CONFLICT, this body not adopted)")
                failed = True; continue
            new_ids = list(range(next_id, next_id + len(b["lines"]))); next_id += len(b["lines"])
            out[k:k + 1] = b["lines"]; ids[k:k + 1] = new_ids
            b["ids"] = new_ids
            all_bodies.append(b)
            summary["leaf_bodies"].append({"unit": unit, "hunk": b["hunk"], "leaf": b["leaf"], "n_lines": len(b["lines"])})
        # blocks: insert after the anchor line (by id); blocks of one unit sharing an anchor keep file order
        for b in sorted(blocks, key=lambda x: x["anchor"]):
            k = idx_of(bmap[b["anchor"]])
            # blocks of the same unit sharing an anchor land in file order: skip what this unit already put there
            j = k + 1 + inserted_after.get((unit, bmap[b["anchor"]]), 0)
            inserted_after[(unit, bmap[b["anchor"]])] = inserted_after.get((unit, bmap[b["anchor"]]), 0) + len(b["lines"])
            new_ids = list(range(next_id, next_id + len(b["lines"]))); next_id += len(b["lines"])
            out[j:j] = b["lines"]; ids[j:j] = new_ids
            b["ids"] = new_ids
            all_blocks.append(b)
            summary["helper_blocks"].append({"unit": unit, "hunk": b["hunk"], "base": f"{base}.lean",
                                             "anchor_after_base_line": b["anchor"], "n_lines": len(b["lines"]),
                                             "n_decls": len(b["decls"]), "decls_head": b["decls"][:4]})
        # checkpoint: if this unit's file is a base for a later unit, the output must equal it byte-for-byte NOW
        if any(u[1] == unit for u in UNITS):
            ul = read_lines(uf)
            same = (ul == out)
            summary["checks"][f"output == {unit}.lean after applying {unit}"] = same
            if not same:
                failed = True
                summary["notes"].append(f"CHECKPOINT FAILED: output differs from {unit}.lean after applying it")
            line_map[unit] = {k + 1: ids[k] for k in range(len(out))}

    # imports union into header (after the last base import line)
    if all_imports:
        k = n_import_lines - 1
        for imp in all_imports:
            k += 1
            out.insert(k, imp); ids.insert(k, next_id); next_id += 1
            summary["imports_added"].append(imp)

    # ---- de-duplication / rename-on-clash over the whole output ---------------------------------------------
    decls, order = collect_decls(out)
    dups = {n: t for n, t in decls.items() if len(t) > 1}
    for n, t in dups.items():
        if all(x == t[0] for x in t):
            summary["dedup_dropped"].append({"name": n, "note": "identical duplicate — WOULD drop later copies"})
        else:
            summary["renamed"].append({"name": n, "note": "differing duplicate — WOULD rename later copies"})
    if dups:
        failed = True
        summary["notes"].append(f"DUPLICATE declaration names in output (not auto-fixed, report): {sorted(dups)}")

    text = "\n".join(out) + "\n"
    pathlib.Path(args.out).write_text(text, encoding="utf-8")

    # ---- contiguity, sections, sorry ------------------------------------------------------------------------
    pos = {id_: k for k, id_ in enumerate(ids)}
    for b in all_blocks:
        core = list(b["lines"])
        trail = 0
        while core and core[-1].strip() == "":
            core.pop(); trail += 1      # trailing blank lines of a hunk may be split by a later unit's insertion
        blk = "\n".join(core)
        cnt = text.count("\n" + blk + "\n")
        s = pos[b["ids"][0]]
        ok = cnt == 1 and out[s:s + len(core)] == core and [pos[i] for i in b["ids"][:len(core)]] == list(range(s, s + len(core)))
        summary["contiguity"].append({"unit": b["unit"], "hunk": b["hunk"], "out_lines": f"{s + 1}-{s + len(core)}",
                                      "trailing_blank_lines_of_hunk": trail, "occurrences": cnt, "contiguous": ok,
                                      "section": enclosing_section(out, s)})
        if not ok:
            failed = True
    for b in all_bodies:
        s = pos[b["ids"][0]]
        ok = out[s:s + len(b["lines"])] == b["lines"]
        summary["contiguity"].append({"unit": b["unit"], "leaf": b["leaf"], "out_lines": f"{s + 1}-{s + len(b['lines'])}",
                                      "in_place": ok, "occurrences": text.count("\n" + "\n".join(b["lines"]) + "\n")})
        if not ok:
            failed = True
    # header check
    hdr_out = [l for l in out[:n_import_lines + len(all_imports)]]
    summary["checks"]["import_header"] = {"base_imports": n_import_lines, "added": all_imports,
                                          "out_header_is_imports": all(l.startswith("import ") for l in hdr_out)}
    # 2a consistency: the blocks/bodies of the audit-only units equal (as text) those of Wave2a_Assembled's hunks
    w2a_blocks = ["\n".join(b["lines"]) for b in all_blocks if b["unit"] == "Wave2a_Assembled"]
    w2a_bodies = ["\n".join(b["lines"]) for b in all_bodies if b["unit"] == "Wave2a_Assembled"]
    au_blocks = ["\n".join(b["lines"]) for b in audit_blocks]
    au_bodies = ["\n".join(b["lines"]) for b in audit_bodies]
    summary["checks"]["2a_blocks_equal_units_blocks"] = sorted(w2a_blocks) == sorted(au_blocks)
    summary["checks"]["2a_bodies_equal_units_bodies"] = sorted(w2a_bodies) == sorted(au_bodies)
    if not (summary["checks"]["2a_blocks_equal_units_blocks"] and summary["checks"]["2a_bodies_equal_units_bodies"]):
        failed = True
    summary["out"] = args.out; summary["out_lines"] = len(out)
    summary["sorry_lines"] = sum(1 for l in out if "sorry" in l)
    summary["sorry_line_numbers"] = [k + 1 for k, l in enumerate(out) if "sorry" in l]
    summary["sorry_decls"] = [decl_of_body(out, k) for k, l in enumerate(out) if l.strip() == "sorry"]
    summary["n_decls_out"] = len(order)
    summary["failed"] = failed
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
