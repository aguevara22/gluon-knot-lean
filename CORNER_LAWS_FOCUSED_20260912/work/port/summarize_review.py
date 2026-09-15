#!/usr/bin/env python3
"""summarize_review.py <workflow-output-file> <row-slug>: save raw result to
work/reviews/<slug>-review-workflow-raw.json and print verdicts, discrepancies, weaker items."""
import json, sys
from pathlib import Path
raw = json.load(open(sys.argv[1])); slug = sys.argv[2]
obj = raw['result']
Path(f'work/reviews/{slug}-review-workflow-raw.json').write_text(json.dumps(obj, indent=1, ensure_ascii=False))
ok = True
for i, r in enumerate(obj['reviews']):
    print(f"REVIEW {i}: {r['verdict']} | discrepancies={len(r['discrepancies'])} | files={len(r['reviewer_files_read'])} defs={len(r['supporting_definitions_inspected'])} | reason {len(r['reason'])} chars")
    for d in r['discrepancies']: print('   DISCREPANCY:', d[:600])
    for w in r['weaker_than_source']: print('   weaker:', w[:500])
    ok &= r['verdict'] == 'faithful' and not r['discrepancies']
for i, r in enumerate(obj['refuters']):
    print(f"REFUTER {i}: refuted={r['refuted']}")
    if r['refuted']: print('   ARGUMENT:', r['argument'][:2500]); ok = False
    else: print('   checked:', r['argument'][:400].replace('\n',' '))
print('ALL CLEAR' if ok else 'ATTENTION NEEDED')
