#!/usr/bin/env python3
"""Every \\lean{...} name in the blueprint must be a declaration of the checker's map
(work/lean/lean-declarations.json), i.e. one whose statement hash the receipts bind. Exit 1 otherwise."""
import json, re, sys, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[1]
names = {r["declaration"] for r in json.load(open(ROOT / "CORNER_LAWS_FOCUSED_20260912/work/lean/lean-declarations.json"))["declarations"]}
used = re.findall(r"\\lean\{([^}]+)\}", open(ROOT / "blueprint/src/content.tex", encoding="utf-8").read())
bad = [u for u in used if u not in names]
print(f"blueprint \\lean names: {len(used)} | not in the declaration map: {len(bad)} {bad[:5]}")
sys.exit(1 if bad else 0)
