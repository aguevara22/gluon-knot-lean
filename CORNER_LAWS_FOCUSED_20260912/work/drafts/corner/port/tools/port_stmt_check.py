#!/usr/bin/env python3
"""port_stmt_check.py — statement / block identity of the port modules against Wave2a_Assembled.lean.

For every column-0 declaration (modifiers and `@[…]` allowed) of every port module the script computes, namespace-
aware, its FULL NAME, its STATEMENT (the paragraph start — docstring / `omit … in` / attribute lines — through the
signature: the line carrying the first `:=`, cut after it; a line ending in `where`; or, for structure / class /
inductive, the whole paragraph) and its BLOCK (the whole paragraph: statement + body up to the next blank line), and
compares both byte-for-byte with the declaration of the same full name in the assembled file.  Coverage: every
declaration of the assembled file must appear exactly once across the port modules except the expected exclusions.
Exit 0 iff every ported declaration is statement-identical (the three row theorems: signature-identical, their
docstrings are new by design and reported), every block is identical (except the three row bodies), and the
coverage is exactly as expected.
Usage: python3 port_stmt_check.py [--json]"""
import json, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
PORT = HERE.parent
CORNER = PORT.parent
ASM = CORNER / "Wave2a_Assembled.lean"
MODULES = ["CornerChainStatements", "CornerChainUnits", "CBSingleton", "CornerValues", "CSoft"]
DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+|@\[[^\]]*\]\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom|example)\s+([^\s:({\[]+)?")
EXPECTED_ABSENT = {  # assembled declarations deliberately not in any port module
    "SM.AllLeftOrOneRight": "DELETED — accepted SM/CarrierFloor.lean:377-408 (byte-identical copy)",
    "SM.CarrierUniformOrOneDissent": "DELETED — accepted SM/CarrierFloor.lean:377-408 (byte-identical copy)",
    "SM.FloorTheoremData": "DELETED — accepted SM/CarrierFloor.lean:377-408 (byte-identical copy)",
    "SM.s7_sliding_law_at": "NOT PORTED — row 110 open leaf (U110-E)",
    "SM.s7_bigon_law_at": "NOT PORTED — row 110 open leaf (U110-K)",
    "SM.thm_C_S7_of": "NOT PORTED — row 110 assembly (depends on the open leaves)",
    "SM.thm_C_S7_of_floor": "NOT PORTED — row 110 assembly (depends on the open leaves)",
    "SM.thm_C_S7": "NOT PORTED — row 110 row theorem (fixed name; unmapped)",
    "SM.example@12228": "DROPPED — the §7 example used thm_C_S7_of_floor; reduced form in SM/CSoft.lean",
}
ROW_THEOREMS = {"SM.cb_singleton", "SM.corner_values", "SM.thm_C_soft"}


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
    """-> list of dicts {name, kind, line, stmt, block, sig} for the column-0 declarations of a Lean file."""
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
        # paragraph
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
        # statement
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
        # signature only (no docstring / modifiers): from the decl line
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
    asm_by = {}
    for d in asm:
        asm_by.setdefault(d["name"], []).append(d)
    dup_asm = [nme for nme, v in asm_by.items() if len(v) > 1]
    port, per_module = [], {}
    for mname in MODULES:
        ds = scan(PORT / "SM" / f"{mname}.lean")
        per_module[mname] = ds
        port.extend(ds)
    port_by = {}
    for d in port:
        port_by.setdefault(d["name"], []).append(d)

    rows, ok = [], True
    counts = {"identical": 0, "row_theorem_sig_identical": 0, "example_reduced": 0, "FAIL": 0}
    for d in port:
        a = asm_by.get(d["name"])
        if d["kind"] == "example":
            # the reduced §7 example in SM/CSoft.lean: not a frozen statement; report only
            rows.append({"name": d["name"], "module": d["file"], "status": "example (reduced §7 check, new)"})
            counts["example_reduced"] += 1
            continue
        if not a:
            rows.append({"name": d["name"], "module": d["file"], "status": "FAIL: not in assembled"}); ok = False
            counts["FAIL"] += 1; continue
        a = a[0]
        if d["stmt"] == a["stmt"] and d["block"] == a["block"]:
            st = "identical (statement + block)"; counts["identical"] += 1
        elif d["name"] in ROW_THEOREMS and d["sig"] == a["sig"]:
            st = "row theorem: signature identical; docstring new; body one-liner"; counts["row_theorem_sig_identical"] += 1
        elif d["stmt"] == a["stmt"]:
            st = "FAIL: statement identical but block differs"; ok = False; counts["FAIL"] += 1
        else:
            st = "FAIL: statement differs"; ok = False; counts["FAIL"] += 1
        rows.append({"name": d["name"], "module": d["file"], "asm_line": a["line"], "port_line": d["line"], "status": st})
    # coverage
    missing = {nme: EXPECTED_ABSENT.get(nme, "UNEXPECTED") for nme in asm_by if nme not in port_by}
    unexpected_missing = [nme for nme, why in missing.items() if why == "UNEXPECTED"]
    unexpected_present = [nme for nme in EXPECTED_ABSENT if nme in port_by]
    dup_port = {nme: [x["file"] + ":" + str(x["line"]) for x in v] for nme, v in port_by.items() if len(v) > 1}
    if unexpected_missing or unexpected_present or dup_port or dup_asm:
        ok = False
    summary = {"ok": ok, "assembled_decls": len(asm), "port_decls": len(port),
               "per_module": {m: len(v) for m, v in per_module.items()}, "counts": counts,
               "absent_from_port": missing, "unexpected_missing": unexpected_missing,
               "unexpected_present": unexpected_present, "declared_twice_in_port": dup_port,
               "declared_twice_in_assembled": dup_asm}
    if want_json:
        print(json.dumps({"summary": summary, "rows": rows}, indent=1, ensure_ascii=False))
    else:
        for r in rows:
            if not r["status"].startswith("identical"):
                print(f"{r['status']:70} {r['name']} [{r['module']}]")
        print(json.dumps(summary, indent=1, ensure_ascii=False))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
