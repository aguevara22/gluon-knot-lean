#!/usr/bin/env python3
"""check_57_identity_port.py — row 57 freeze check, re-pointed at the port modules.

Same blocks as check_57_identity.py (DEFS, BUNDLE, THM of Statements_FINAL.lean), checked as verbatim substrings of
  DEFS   -> port/SM/GaussTwoDiscsDefs.lean
  BUNDLE -> port/SM/GaussTwoDiscs.lean
  THM    -> port/SM/GaussTwoDiscs.lean
Usage: python3 check_57_identity_port.py [port_dir]   (default: the directory of this script).  Exit 0 iff all found.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
REF = os.path.join(os.path.dirname(HERE), "Statements_FINAL.lean")
sys.path.insert(0, os.path.dirname(HERE))
from check_57_identity import blocks

def main(argv):
    port = argv[1] if len(argv) > 1 else HERE
    B = blocks(open(REF, encoding="utf-8").read())
    where = {"DEFS": "SM/GaussTwoDiscsDefs.lean", "BUNDLE": "SM/GaussTwoDiscs.lean", "THM": "SM/GaussTwoDiscs.lean"}
    ok = True
    for name, blk in B.items():
        f = os.path.join(port, where[name])
        t = open(f, encoding="utf-8").read() if os.path.exists(f) else ""
        found = blk in t
        ok &= found
        print(f"{'OK     ' if found else 'DIFFERS'} {name:6s} {where[name]}")
    print("IDENTITY OK" if ok else "IDENTITY FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv))
