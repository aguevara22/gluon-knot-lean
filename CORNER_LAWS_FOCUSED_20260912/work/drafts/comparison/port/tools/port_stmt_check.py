#!/usr/bin/env python3
"""port_stmt_check.py — statement / block identity of the comparison-lane port modules against Comparison_Assembled.lean.

For every column-0 declaration (modifiers and `@[…]` allowed) of every port module the script computes, namespace-aware,
its FULL NAME, its STATEMENT (the paragraph start — docstring / attribute lines — through the signature: the line carrying
the first `:=`, cut after it; a line ending in `where`; or, for structure / class / inductive, the whole paragraph), its
SIGNATURE (declaration line through the same cut, no docstring) and its BLOCK (the whole paragraph), and compares them
byte-for-byte with the declaration of the same full name in the assembled file.  `example`s (nameless) are matched by
their whole block.  Coverage: every declaration of the assembled file must appear exactly once across the port modules
except the expected exclusions (the four DELETED §0 copies, the two deferred row theorems).
Exit 0 iff every ported declaration is statement- and block-identical (the row theorem `SM.prop_anchor_values`:
signature-identical, docstring new by design, body the prescribed one-liner), every example block is verbatim, and the
coverage is exactly as expected.  Usage: python3 port_stmt_check.py [--json]"""
import json, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
PORT = HERE.parent
LANE = PORT.parent
ASM = LANE / "Comparison_Assembled.lean"
MODULES = ["CornerPolygon", "AnchorValues", "AnchorValuesRow", "CuspDeletionGeneric", "Comparison", "CInherits"]
DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+|@\[[^\]]*\]\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom|example)\s+([^\s:({\[]+)?")
EXPECTED_ABSENT = {
    "SM.CS7Data": "DELETED — accepted SM/CornerChainStatements.lean:232 (byte-identical declaration block; imported)",
    "SM.CSoftData": "DELETED — accepted SM/CornerChainStatements.lean:289 (byte-identical declaration block; imported)",
    "SM.cvl_embedded_of_no_crossings": "DELETED — accepted SM/CornerChainUnits.lean:1158 (byte-identical declaration block; imported)",
    "SM.corner_values_i": "DELETED — accepted SM/CornerChainUnits.lean:1184 (byte-identical declaration block; imported)",
    "SM.thm_comparison": "NOT PORTED — row 127 (FIXED name) needs SM.thm_C_S7 (row 110); one-liner deferred, PORT_REPORT.md §5",
    "SM.cor_C_inherits": "NOT PORTED — row 128 (FIXED name) needs SM.thm_C_S7 (row 110); one-liner deferred, PORT_REPORT.md §5",
}
ROW_THEOREMS = {"SM.prop_anchor_values": "anchor_values_of thm_C_soft"}


def comment_depth_after(line, depth):
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


def scan(path, warn=True):
    """-> list of dicts {name, kind, line, stmt, block, sig, file} for the column-0 declarations of a Lean file."""
    lines = path.read_text(encoding="utf-8").split("\n")
    if lines and lines[-1] == "":
        lines = lines[:-1]
    ns, depth, out = [], 0, []
    n = len(lines)
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
        if not m:
            continue
        kind, short = m.group(1), m.group(2)
        if kind == "example" or short is None:
            short = f"{kind}@{k + 1}"
        name = ".".join(ns + [short])
        ps = k
        while ps > 0 and lines[ps - 1].strip() != "":
            ps -= 1
        pe = k
        while pe < n and lines[pe].strip() != "":
            pe += 1
        block = lines[ps:pe]
        head = lines[ps]
        if warn and not (head.startswith("/--") or head.startswith("omit ") or head.startswith("@[") or
                head.startswith("open ") or head.startswith("include ") or head.startswith("set_option ") or
                head.startswith("attribute ") or DECL_RE.match(head)):
            print(f"WARN {path.name}:{ps + 1}: paragraph of {name} starts with {head[:60]!r}", file=sys.stderr)
        if kind in ("structure", "class", "inductive"):
            stmt = block[:]
        else:
            e = k
            while e < pe:
                t = lines[e]
                if ":=" in t or t.rstrip().endswith(" where") or t.strip().startswith("|"):
                    break
                e += 1
            if e >= pe:
                e = pe - 1
            stmt = lines[ps:e + 1]
            if ":=" in stmt[-1]:
                stmt[-1] = stmt[-1][: stmt[-1].find(":=") + 2]
            elif stmt[-1].strip().startswith("|"):
                stmt = stmt[:-1]
        j = 0
        while j < len(stmt) and not DECL_RE.match(stmt[j]):
            j += 1
        sig = stmt[j:]
        out.append({"name": name, "kind": kind, "line": k + 1, "stmt": "\n".join(stmt),
                    "block": "\n".join(block), "sig": "\n".join(sig), "file": path.name})
    return out


def main():
    want_json = "--json" in sys.argv
    asm = scan(ASM)
    asm_by, asm_ex = {}, {}
    for d in asm:
        if d["kind"] == "example":
            asm_ex.setdefault(d["block"], []).append(d)
        else:
            asm_by.setdefault(d["name"], []).append(d)
    dup_asm = [nme for nme, v in asm_by.items() if len(v) > 1]
    port, per_module = [], {}
    for mname in MODULES:
        ds = scan(PORT / "SM" / f"{mname}.lean")
        per_module[mname] = ds
        port.extend(ds)
    port_by, port_ex = {}, {}
    for d in port:
        if d["kind"] == "example":
            port_ex.setdefault(d["block"], []).append(d)
        else:
            port_by.setdefault(d["name"], []).append(d)

    rows, ok = [], True
    counts = {"identical": 0, "row_theorem_sig_identical": 0, "example_verbatim": 0, "FAIL": 0}
    for d in port:
        if d["kind"] == "example":
            if d["block"] in asm_ex:
                st = "example: block verbatim"; counts["example_verbatim"] += 1
                rows.append({"name": d["name"], "module": d["file"], "asm_line": asm_ex[d["block"]][0]["line"], "port_line": d["line"], "status": st})
            else:
                rows.append({"name": d["name"], "module": d["file"], "port_line": d["line"], "status": "FAIL: example block not in assembled"})
                ok = False; counts["FAIL"] += 1
            continue
        a = asm_by.get(d["name"])
        if not a:
            rows.append({"name": d["name"], "module": d["file"], "status": "FAIL: not in assembled"}); ok = False
            counts["FAIL"] += 1; continue
        a = a[0]
        if d["stmt"] == a["stmt"] and d["block"] == a["block"]:
            st = "identical (statement + block)"; counts["identical"] += 1
        elif d["name"] in ROW_THEOREMS:
            a_sig = a["sig"]; d_sig = d["sig"]
            body = d["block"].split(":=", 1)[1].strip() if ":=" in d["block"] else ""
            if d_sig == a_sig and body == ROW_THEOREMS[d["name"]]:
                st = f"row theorem: signature identical; docstring new; body `{body}`"; counts["row_theorem_sig_identical"] += 1
            else:
                st = f"FAIL: row theorem signature or body differs (body {body!r})"; ok = False; counts["FAIL"] += 1
        elif d["stmt"] == a["stmt"]:
            st = "FAIL: statement identical but block differs"; ok = False; counts["FAIL"] += 1
        else:
            st = "FAIL: statement differs"; ok = False; counts["FAIL"] += 1
        rows.append({"name": d["name"], "module": d["file"], "asm_line": a["line"], "port_line": d["line"], "status": st})
    missing = {nme: EXPECTED_ABSENT.get(nme, "UNEXPECTED") for nme in asm_by if nme not in port_by}
    unexpected_missing = [nme for nme, why in missing.items() if why == "UNEXPECTED"]
    unexpected_present = [nme for nme in EXPECTED_ABSENT if nme in port_by]
    dup_port = {nme: [x["file"] + ":" + str(x["line"]) for x in v] for nme, v in port_by.items() if len(v) > 1}
    ex_missing = [v[0]["line"] for b, v in asm_ex.items() if b not in port_ex]
    ex_dup = [v[0]["line"] for b, v in port_ex.items() if len(v) > 1]
    if unexpected_missing or unexpected_present or dup_port or dup_asm or ex_missing or ex_dup:
        ok = False
    summary = {"ok": ok, "assembled_decls": len(asm), "assembled_examples": len(asm_ex), "port_decls": len(port),
               "per_module": {m: len(v) for m, v in per_module.items()}, "counts": counts,
               "absent_from_port": missing, "unexpected_missing": unexpected_missing,
               "unexpected_present": unexpected_present, "declared_twice_in_port": dup_port,
               "declared_twice_in_assembled": dup_asm, "examples_missing_from_port(asm lines)": ex_missing,
               "examples_duplicated_in_port": ex_dup}
    if want_json:
        print(json.dumps({"summary": summary, "rows": rows}, indent=1, ensure_ascii=False))
    else:
        for r in rows:
            if not r["status"].startswith("identical"):
                print(f"{r['status']:75} {r['name']} [{r['module']}]")
        print(json.dumps(summary, indent=1, ensure_ascii=False))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
