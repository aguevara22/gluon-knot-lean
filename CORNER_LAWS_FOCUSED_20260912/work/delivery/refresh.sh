#!/usr/bin/env bash
# refresh.sh — re-copy the live evidence into work/delivery/ (the delivery package).
#
# Written 2026-09-14 by the pod executor's documentation agent. Run it from anywhere:
#     bash work/delivery/refresh.sh
# It copies (never moves) the current pins, declaration map, review records, checker
# receipts, progress history and decision log into this directory and writes
# MANIFEST.sha256 over the copied files. It does NOT run the checker, lake, or any
# Lean tool: run `python3 tools/check_lean.py work/lean` (development) or `--all`
# (stage) yourself first if you want the receipts refreshed, then run this script.
# Sources (reference/, provenance/, blueprint/) are frozen in place and are not copied.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"          # .../work/delivery
WORK="$(cd "$HERE/.." && pwd)"                                 # .../work
ROOT="$(cd "$WORK/.." && pwd)"                                 # package root
PY="${PYTHON:-python3}"

say() { printf '%s\n' "$*"; }

mkdir -p "$HERE/pins" "$HERE/declaration-map" "$HERE/reviews" "$HERE/receipts" "$HERE/progress" "$HERE/tools"

# 1. Pins and policy (the exact toolchain/library pins the receipts bind).
cp -f "$WORK/lean/lean-toolchain"        "$HERE/pins/lean-toolchain"
cp -f "$WORK/lean/lake-manifest.json"    "$HERE/pins/lake-manifest.json"
cp -f "$WORK/lean/lakefile.toml"         "$HERE/pins/lakefile.toml"
cp -f "$WORK/lean/axiom-policy.json"     "$HERE/pins/axiom-policy.json"
cp -f "$WORK/lean/ENVIRONMENT.md"        "$HERE/pins/ENVIRONMENT.md"
if [ -f "$WORK/lake-manifest.shipped.json" ]; then
  cp -f "$WORK/lake-manifest.shipped.json" "$HERE/pins/lake-manifest.shipped.json"
  if cmp -s "$WORK/lake-manifest.shipped.json" "$WORK/lean/lake-manifest.json"; then
    say "pins: lake-manifest.json is byte-identical to the shipped manifest"
  else
    say "pins: WARNING lake-manifest.json differs from lake-manifest.shipped.json (record the pin change in AUTHOR_NOTES)"
  fi
fi

# 2. Declaration map (the file map_row.py edits; the checker's row source of truth).
cp -f "$WORK/lean/lean-declarations.json" "$HERE/declaration-map/lean-declarations.json"

# 3. Review records: every work/reviews file (review JSON, reviewer-input statements,
#    source/registry excerpts, raw workflow outputs, countersignature raw output).
#    --delete keeps the copy an exact mirror; reviews are never deleted upstream.
if command -v rsync >/dev/null 2>&1; then
  rsync -a --delete "$WORK/reviews/" "$HERE/reviews/"
else
  rm -rf "$HERE/reviews"; mkdir -p "$HERE/reviews"; cp -a "$WORK/reviews/." "$HERE/reviews/"
fi

# 4. Checker receipts: the per-run development receipts, the current stage receipt,
#    the current declaration audit (gzipped: the raw file is ~0.8 GB because it carries
#    the expanded definition bodies) and a small summary of the audit, plus the checker
#    run logs if present.
rm -f "$HERE"/receipts/dev-check-*.json "$HERE"/receipts/checker-run-*.log "$HERE"/receipts/stage-*.json
cp -f "$WORK"/checks/dev-check-*.json "$HERE/receipts/" 2>/dev/null || true
cp -f "$WORK"/checks/checker-run-*.log "$WORK"/checks/stage-all-attempt-*.log "$HERE/receipts/" 2>/dev/null || true
cp -f "$WORK/checks/stage-development.json" "$HERE/receipts/stage-development.json"
for f in "$WORK"/checks/stage-1.json "$WORK"/checks/stage-all.json "$WORK"/checks/stage-*.json; do
  [ -f "$f" ] && cp -f "$f" "$HERE/receipts/" || true
done
gzip -1 -c "$WORK/checks/declaration-audit.json" > "$HERE/receipts/declaration-audit.json.gz"
"$PY" - "$WORK/checks/declaration-audit.json" "$HERE/receipts/declaration-audit.summary.json" <<'PYEOF'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
a = json.load(open(src))
out = {
  "note": "Summary of work/checks/declaration-audit.json (bodies and semantic dependencies dropped); the full file is declaration-audit.json.gz next to this one.",
  "stage_requested": a.get("stage_requested"),
  "checked": a.get("audit", {}).get("checked"),
  "mapped_declarations": [
    {"declaration": d.get("declaration"), "kind": d.get("kind"), "module": d.get("module"), "axioms": d.get("axioms")}
    for d in a.get("audit", {}).get("declarations", [])
  ],
  "statement_hashes": a.get("statement_hashes", {}),
}
json.dump(out, open(dst, "w"), indent=1, ensure_ascii=False)
print("receipts: audit summary written (%d mapped declarations, %d audited)" % (len(out["mapped_declarations"]), out["checked"] or 0))
PYEOF

# 5. Progress history and status.
cp -f "$WORK/progress-watch.log" "$HERE/progress/progress-watch.log"
cp -f "$WORK/STATUS.md"          "$HERE/progress/STATUS.md"
[ -f "$WORK/PROGRESS.md" ] && cp -f "$WORK/PROGRESS.md" "$HERE/progress/PROGRESS.md"
[ -f "$WORK/TASKS.json" ]   && cp -f "$WORK/TASKS.json"  "$HERE/progress/TASKS.json"
mkdir -p "$HERE/progress/progress"
cp -f "$WORK"/progress/*.json "$WORK"/progress/*.jsonl "$HERE/progress/progress/" 2>/dev/null || true

# 6. Decision log and the final review (draft while rows are still being accepted;
#    the executor replaces it by the final FINAL_REVIEW.md at the end).
cp -f "$WORK/AUTHOR_NOTES.md" "$HERE/AUTHOR_NOTES.md"
[ -f "$WORK/FINAL_REVIEW_DRAFT.md" ] && cp -f "$WORK/FINAL_REVIEW_DRAFT.md" "$HERE/FINAL_REVIEW_DRAFT.md"
cp -f "$ROOT/FINAL_REVIEW.md" "$HERE/FINAL_REVIEW.md" 2>/dev/null || true  # root file (fixed 18:20Z)

# 7. Manifest over everything copied (excluding the manifest itself).
( cd "$HERE" && find . -type f ! -name MANIFEST.sha256 -print0 | sort -z | xargs -0 sha256sum ) > "$HERE/MANIFEST.sha256"

# 8. One-line summary from the receipts, for the log.
"$PY" - "$HERE/receipts/stage-development.json" "$HERE/declaration-map/lean-declarations.json" <<'PYEOF'
import json, sys, collections
s = json.load(open(sys.argv[1])); m = json.load(open(sys.argv[2]))["declarations"]
c = collections.Counter(r["status"] for r in m)
print("refresh done: receipt passed=%s stage=%s stage_accepted=%s mapped=%s audited=%s | map rows: %s" %
      (s.get("passed"), s.get("stage"), s.get("stage_accepted"), s.get("mapped_declarations"), s.get("audited_declarations"), dict(c)))
PYEOF
say "refreshed $(date -u '+%Y-%m-%dT%H:%MZ'); manifest: $HERE/MANIFEST.sha256 ($(wc -l < "$HERE/MANIFEST.sha256") files)"
