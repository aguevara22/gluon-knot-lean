#!/usr/bin/env python3
"""List the claims in document order with their status and what stands before them.

A claim is a source statement with a printed proof (action PROVE) or one of the
R/bridge/final obligations of EXECUTION.json. Definitions, literature inputs and
hypotheses are not claims but are units of work that precede claims. "verified"
means status accepted in the declaration map: kernel-checked and independently
reviewed. Report claims verified / total claims every 15 minutes.

Document order is a valid formalization order (the source has no forward
references). The explicit dependency columns are incomplete, so the tool also
counts the unaccepted definitions that precede a claim in its own source file:
a claim with pending definitions before it usually needs them first.
`--next` prints the recommended next unit: the first pending row (definition
or claim) in document order whose explicit dependencies are all accepted.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.scope import SPEC, source_rows

SKIP = {'AXIOM', 'HYPOTHESIS', 'SKIP', 'CERTIFICATE'}


def load(work):
    rows = source_rows()
    by_row = {r['id']: r for r in rows}
    decl = json.loads((work / 'lean/lean-declarations.json').read_text())['declarations'] if (work / 'lean/lean-declarations.json').is_file() else []
    status = {d['id']: d.get('status', 'pending') for d in decl}
    graph = ROOT / 'blueprint/DEPENDENCIES.json'
    deps = json.loads(graph.read_text()).get('edges', {}) if graph.is_file() else {r['id']: r['deps'].split() for r in rows}
    return rows, by_row, status, deps


def units(work):
    """Every unit of work (definitions and claims) in document order, then the extra obligations."""
    rows, by_row, status, deps = load(work)
    claim_ids = {r['id'] for r in rows if r['action'] == 'PROVE'} | set(SPEC['extra'])
    ordered = [r for r in rows if r['action'] not in SKIP] 
    result, pending_defs_before = [], {}
    for r in ordered:
        f = r.get('source') or r.get('file', '')
        n = pending_defs_before.setdefault(f, [])
        unaccepted = sorted(d for d in deps.get(r['id'], []) if status.get(d) != 'accepted' and by_row.get(d, {}).get('action') not in {'AXIOM', 'HYPOTHESIS'})
        result.append({'id': r['id'], 'unit': 'claim' if r['id'] in claim_ids else 'definition', 'kind': r['env'],
                       'status': status.get(r['id'], 'pending'), 'source': f + ':' + str(r['line']),
                       'pending_definitions_earlier_in_file': list(n), 'unaccepted_explicit_dependencies': unaccepted})
        if r['action'] == 'DEFINE' and status.get(r['id']) != 'accepted':
            n.append(r['id'])
    for x in SPEC['extra']:
        unaccepted = sorted(d for d in deps.get(x, []) if status.get(d) != 'accepted' and by_row.get(d, {}).get('action') not in {'AXIOM', 'HYPOTHESIS'})
        result.append({'id': x, 'unit': 'claim', 'kind': 'obligation', 'status': status.get(x, 'pending'), 'source': '',
                       'pending_definitions_earlier_in_file': [], 'unaccepted_explicit_dependencies': unaccepted})
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=ROOT / 'work')
    parser.add_argument('--json', action='store_true')
    parser.add_argument('--pending-only', action='store_true')
    parser.add_argument('--next', action='store_true', help='print the recommended next unit of work')
    args = parser.parse_args()
    all_units = units(args.work_dir.resolve())
    claims = [u for u in all_units if u['unit'] == 'claim']
    verified = sum(c['status'] == 'accepted' for c in claims)
    if args.next:
        for u in all_units:
            if u['status'] != 'accepted' and not u['unaccepted_explicit_dependencies'] and not u['pending_definitions_earlier_in_file']:
                print(f"next unit: {u['id']} ({u['unit']}, {u['kind']}) at {u['source']}"); break
        else:
            print('next unit: none with all explicit dependencies accepted; take the first pending definition in document order')
        sys.exit(0)
    if args.json:
        print(json.dumps({'claims_verified': verified, 'claims_total': len(claims), 'units': all_units}, indent=2))
        sys.exit(0)
    print(f'# Claims: {verified} verified / {len(claims)} total (definitions listed as units, not counted)\n')
    print('Document order. A claim with pending definitions earlier in its file usually needs them first.\n')
    print('| # | unit | id | kind | status | source | pending definitions earlier in file | unaccepted explicit dependencies |')
    print('|---|---|---|---|---|---|---|---|')
    for k, u in enumerate(all_units, 1):
        if args.pending_only and u['status'] == 'accepted':
            continue
        print(f"| {k} | {u['unit']} | `{u['id']}` | {u['kind']} | {'VERIFIED' if u['status'] == 'accepted' else u['status']} | {u['source']} | {len(u['pending_definitions_earlier_in_file'])} | {' '.join('`' + d + '`' for d in u['unaccepted_explicit_dependencies'])} |")
