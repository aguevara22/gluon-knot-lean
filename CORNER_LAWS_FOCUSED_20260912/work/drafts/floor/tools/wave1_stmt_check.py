import re, sys, pathlib
base = pathlib.Path("Statements_FINAL.lean").read_text().split("\n")
asm_text = pathlib.Path("Wave1_Assembled.lean").read_text()
decl_re = re.compile(r"^(@\[[^\]]*\]\s*)?(private |protected |noncomputable )?(theorem|def|structure|abbrev|instance|lemma)\s+([A-Za-z_][\w.'₀-₉!?]*)")
# Extract each base declaration's statement: from header line through the line where the
# top-level `:=` / `where` / `:= by` appears (structures: whole block up to next blank line at col 0).
ok = bad = 0
names = []
i = 0
while i < len(base):
    m = decl_re.match(base[i])
    if not m:
        i += 1; continue
    kind, name = m.group(3), m.group(4)
    j = i
    if kind == "structure":
        # block = until a line that is blank followed by a non-indented line
        while j + 1 < len(base) and not (base[j + 1].strip() == "" and (j + 2 >= len(base) or not base[j + 2].startswith(" "))):
            j += 1
        stmt = "\n".join(base[i:j + 1])
    else:
        while True:
            line = base[j]
            if ":=" in line or line.rstrip().endswith(" where"):
                break
            j += 1
        stmt_lines = base[i:j + 1]
        last = stmt_lines[-1]
        # cut at the first `:=` (statement text up to and including `:=`); keep ` where` headers whole
        if ":=" in last:
            last = last[: last.index(":=") + 2]
        stmt_lines[-1] = last
        stmt = "\n".join(stmt_lines)
    cnt = asm_text.count(stmt)
    if cnt >= 1:
        ok += 1
    else:
        bad += 1
        print("MISMATCH:", kind, name, "\n", stmt[:300])
    names.append((kind, name, cnt))
    i = j + 1
print(f"declarations checked: {ok + bad}; byte-identical statements found: {ok}; mismatches: {bad}")
dups = [(k, n, c) for (k, n, c) in names if c > 1]
if dups: print("statements occurring more than once (check for duplicate declarations):", dups)
