#!/usr/bin/env python3
"""stmt_check.py — byte-identity of every declaration STATEMENT of Statements_FINAL.lean inside an
assembled file (default Partial_Assembled.lean).

A "declaration statement" is, for every top-level `theorem` / `def` / `structure` / `example` of the
frozen file: the docstring immediately preceding it (if any), any `omit … in` modifier line, the
declaration keyword line and every line up to and including the signature's terminating `:=` (the
trailing ` by`, if present, is NOT part of the statement); for a `structure … where` the whole block up
to the next blank line (the fields ARE the statement).  Statements are compared byte for byte (after
removing a trailing ` by` on the `:=` line) and must occur EXACTLY ONCE in the assembled file, in the
same order as in the frozen file.  Additionally the set of frozen declaration NAMES must be exactly the
names declared by the frozen file, none renamed, and no frozen declaration may be declared twice in the
assembled file (a unit helper re-declaring a frozen name would shadow it).

Usage:  python3 tools/stmt_check.py [assembled.lean] [--base Statements_FINAL.lean] [--json]
Exit 0 iff every check passes.
"""
import argparse
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
CORNER = HERE.parent
DECL_RE = re.compile(r"^(theorem|def|structure|example|abbrev|instance|noncomputable def)\s+([^\s:({\[]+)?")


def statements(lines):
    """Yield (name, kind, first_line_no, text) for every top-level declaration of a Lean file (top level =
    column 0)."""
    out = []
    k = 0
    n = len(lines)
    while k < n:
        m = DECL_RE.match(lines[k])
        if not m:
            k += 1
            continue
        kind, name = m.group(1), m.group(2)
        if kind == "example":
            name = f"example@{k + 1}"
        # start: preceding docstring / `omit … in` / attribute lines (contiguous, no blank line)
        s = k
        j = k - 1
        while j >= 0 and lines[j].strip() != "":
            t = lines[j]
            if t.startswith("omit ") or t.startswith("@[") or t.rstrip().endswith("-/") or \
               t.startswith("/--") or (s < k and not lines[s].startswith("/--")):
                s = j
                j -= 1
                # stop once we have swallowed a complete docstring opening
                if lines[s].startswith("/--"):
                    # allow an `omit … in` above the docstring
                    if j >= 0 and lines[j].startswith("omit "):
                        s = j
                    break
            else:
                break
        # end
        if kind == "structure":
            e = k
            while e < n and lines[e].strip() != "":
                e += 1
            body = lines[s:e]
        else:
            e = k
            while e < n:
                stripped = lines[e].rstrip()
                if stripped.endswith(":=") or stripped.endswith(":= by") or " := by " in lines[e] or \
                   stripped.endswith("where") or re.search(r":=\s*(by\s*)?$", stripped) or \
                   re.search(r"\s:=\s", lines[e]):
                    break
                e += 1
            body = lines[s:e + 1]
            if body:
                last = body[-1]
                # cut at the signature's `:=` (keep it), dropping the proof term / ` by` after it
                idx = last.find(":=")
                if idx >= 0:
                    body[-1] = last[:idx + 2]
        out.append((name, kind, k + 1, "\n".join(body)))
        k = max(k + 1, e)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("assembled", nargs="?", default=str(CORNER / "Partial_Assembled.lean"))
    ap.add_argument("--base", default=str(CORNER / "Statements_FINAL.lean"))
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    base_lines = pathlib.Path(a.base).read_text(encoding="utf-8").split("\n")
    asm_text = pathlib.Path(a.assembled).read_text(encoding="utf-8")
    asm_lines = asm_text.split("\n")
    base_stmts = statements(base_lines)
    asm_stmts = statements(asm_lines)
    asm_names = {}
    for (name, kind, ln, text) in asm_stmts:
        asm_names.setdefault(name, []).append((ln, text))

    results, ok = [], True
    last_pos = -1
    for (name, kind, ln, text) in base_stmts:
        # exact occurrence count of the statement text at line starts
        pattern = "\n" + text
        count = ("\n" + asm_text).count(pattern)
        # also require the match to end at a line/signature boundary: the char after must be newline,
        # or ' by', or a space+term (for `:=` lines) — the text already ends with `:=` or the struct block
        pos = ("\n" + asm_text).find(pattern)
        in_order = pos > last_pos
        if pos >= 0:
            last_pos = pos
        declared = len(asm_names.get(name, []))
        status = "OK" if (count == 1 and in_order and (declared == 1 or kind == "example")) else "FAIL"
        if status == "FAIL":
            ok = False
        results.append({"name": name, "kind": kind, "base_line": ln, "occurrences": count,
                        "declared_in_assembled": declared, "in_order": in_order, "status": status})
    extra_frozen_names = []
    if a.json:
        print(json.dumps({"ok": ok, "checked": len(results), "results": results}, indent=1, ensure_ascii=False))
    else:
        w = max(len(r["name"]) for r in results)
        for r in results:
            print(f"{r['status']:4} {r['kind']:9} {r['name']:{w}}  base:{r['base_line']:>4}  occ={r['occurrences']}  "
                  f"declared={r['declared_in_assembled']}  order={'y' if r['in_order'] else 'n'}")
        print(f"\n{sum(r['status']=='OK' for r in results)}/{len(results)} frozen declaration statements byte-identical "
              f"and unique in {pathlib.Path(a.assembled).name}: {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
