#!/usr/bin/env python3
"""check_57_identity.py — row 57 freeze check.

Asserts that the frozen text of Statements_FINAL.lean is byte-identical inside every unit file:
  block DEFS   : from the line `namespace SM` up to (not including) the `/-! ## §5` header
                 (all definitions of §1-§4);
  block BUNDLE : from the `/-! ## §5` header through the end of `structure GaussTwoDiscsData`
                 (up to, not including, the docstring of the row theorem);
  block THM    : the header of the row theorem, `theorem lem_gauss_two_discs ... :\n    GaussTwoDiscsData P := by`.
Each block must occur verbatim (as a substring) in each checked file.  Files whose name starts with
`Statements_` are the reference itself and are skipped.

Usage: python3 check_57_identity.py [file.lean ...]
  With no arguments: checks Skeleton_FINAL.lean and every U*.lean / Unit*.lean in this directory.
Exit status 0 iff every block is found in every file.
"""
import sys, glob, os

HERE = os.path.dirname(os.path.abspath(__file__))
REF = os.path.join(HERE, "Statements_FINAL.lean")


def blocks(text: str):
    i_ns = text.index("\nnamespace SM\n") + 1
    i_s5 = text.index("/-! ## §5")
    i_thmdoc = text.index("/-- **lem:gauss-two-discs** (row 57")
    i_thm = text.index("theorem lem_gauss_two_discs")
    i_by = text.index("GaussTwoDiscsData P := by", i_thm) + len("GaussTwoDiscsData P := by")
    return {
        "DEFS": text[i_ns:i_s5],
        "BUNDLE": text[i_s5:i_thmdoc],
        "THM": text[i_thm:i_by],
    }


def main(argv):
    ref = open(REF, encoding="utf-8").read()
    B = blocks(ref)
    files = argv[1:]
    if not files:
        files = [os.path.join(HERE, "Skeleton_FINAL.lean")]
        files += sorted(glob.glob(os.path.join(HERE, "U*.lean")))
        files += sorted(glob.glob(os.path.join(HERE, "Unit*.lean")))
    ok = True
    for f in files:
        if os.path.basename(f).startswith("Statements_"):
            continue
        if not os.path.exists(f):
            print(f"MISSING {f}")
            ok = False
            continue
        t = open(f, encoding="utf-8").read()
        for name, blk in B.items():
            if blk in t:
                print(f"OK      {name:6s} {os.path.relpath(f, HERE)}")
            else:
                print(f"DIFFERS {name:6s} {os.path.relpath(f, HERE)}")
                ok = False
    print("IDENTITY OK" if ok else "IDENTITY FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
