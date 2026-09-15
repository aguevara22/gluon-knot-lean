#!/usr/bin/env python3
"""Report accepted checklist rows, not estimated effort or mathematical truth."""
import sys
sys.dont_write_bytecode = True
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import math
import os
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.scope import configuration, required_ids, source_rows
from tools.receipts import current


def read(path, default):
    return json.loads(path.read_text()) if path.is_file() else default


def atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + '.' + str(os.getpid()) + '.tmp')
    temp.write_text(value)
    temp.replace(path)


def records_by_id(records):
    if not isinstance(records, list) or not all(isinstance(row, dict) for row in records):
        raise ValueError('progress records must be a list of objects')
    result = {}
    for row in records:
        name = row['id']
        if not isinstance(name, str) or not name or name in result:
            raise ValueError('empty or duplicate progress ID: ' + str(name))
        result[name] = row
    return result


def acceptance(work, stages, root=ROOT):
    """Report existing checker receipts only when their bound files still match."""
    result = {}
    for stage in stages:
        receipt = read(work / 'checks' / ('stage-' + str(stage) + '.json'), {})
        valid = receipt.get('stage') == stage and current(receipt, work, root)
        result[str(stage)] = 'checker receipt current' if valid else 'not established by a current checker receipt'
    return result


def snapshot(work, root=ROOT):
    spec = configuration(root)
    declarations = read(work / 'lean/lean-declarations.json', {'declarations': []})['declarations']
    certificates = read(work / 'certificates/index.json', {'certificates': []})['certificates']
    byid = records_by_id(declarations + certificates)
    prior = read(work / 'progress/scope.json', {'ids': []})
    ids = required_ids(root) | set(byid) | set(prior['ids'])
    accepted = sum(byid.get(name, {}).get('status') == 'accepted' for name in ids)
    # Claims: statements with printed proofs plus the R/bridge/final obligations.
    claim_ids = {r['id'] for r in source_rows(root) if r['action'] == 'PROVE'} | set(spec['extra'])
    claims_verified = sum(byid.get(i, {}).get('status') == 'accepted' for i in claim_ids)
    claims_awaiting = sum(byid.get(i, {}).get('status') in {'implemented', 'review'} for i in claim_ids)
    percentage = round(100 * accepted / len(ids), 1) if ids else 0.0
    if accepted < len(ids):
        percentage = min(99.9, percentage)
    tasks = read(work / 'TASKS.json', [])
    if not isinstance(tasks, list) or not all(isinstance(task, dict) for task in tasks):
        raise ValueError('TASKS.json must be a list of task objects')
    result = {'timestamp_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
              'name': spec['name'], 'metric': 'claims verified (accepted proof claims) and accepted checklist rows; not effort or proof truth',
              'claims_verified': claims_verified, 'claims_total': len(claim_ids),
              'claims_percentage': round(100 * claims_verified / len(claim_ids), 1) if claim_ids else 0.0,
              'claims_awaiting_review': claims_awaiting,
              'accepted': accepted, 'total': len(ids), 'percentage': percentage,
              'added_since_previous': sorted(ids - set(prior['ids'])) if prior['ids'] else [],
              'targets_accepted': sum(byid.get(i, {}).get('status') == 'accepted' for i in spec['targets']),
              'targets_total': len(spec['targets']),
              'active': [t['id'] for t in tasks if t.get('state') == 'active'],
              'blocked_local': [t['id'] for t in tasks if t.get('state') == 'blocked-local'],
              'acceptance': acceptance(work, spec['acceptance_stages'], root)}
    atomic(work / 'progress/scope.json', json.dumps({'ids': sorted(ids)}, indent=2) + '\n')
    return result


def report(work, root=ROOT):
    try:
        data = snapshot(work, root)
        line = (f"[{data['timestamp_utc']}] {data['name']}: claims verified "
                f"{data['claims_verified']}/{data['claims_total']} ({data['claims_percentage']:.1f}%); "
                f"kernel-checked awaiting review {data['claims_awaiting_review']}; {data['percentage']:.1f}% "
                f"checklist ({data['accepted']}/{data['total']} accepted); "
                f"targets {data['targets_accepted']}/{data['targets_total']}; "
                f"active: {', '.join(data['active']) or 'none recorded'}; "
                f"local blockers: {', '.join(data['blocked_local']) or 'none recorded'}.")
        detail = '\n'.join('Stage ' + stage + ': ' + state + '.' for stage, state in data['acceptance'].items())
        if data['added_since_previous']:
            detail += '\nScope expanded by ' + str(len(data['added_since_previous'])) + ' obligations; denominator recalculated.'
        detail += '\nClaims verified = accepted proof claims (kernel-checked and independently reviewed). Percentages count reported accepted rows; they are not a time estimate or a proof certificate.'
    except (ValueError, OSError, KeyError, TypeError, AttributeError) as error:
        data = {'timestamp_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
                'percentage': None, 'error': str(error)}
        line = '[' + data['timestamp_utc'] + '] Progress unavailable: ' + str(error)
        detail = 'Repair the progress metadata locally; mathematical work can continue.'
    try:
        atomic(work / 'progress/latest.json', json.dumps(data, indent=2) + '\n')
        with (work / 'progress/history.jsonl').open('a') as stream:
            stream.write(json.dumps(data) + '\n')
        atomic(work / 'PROGRESS.md', line + '\n\n' + detail + '\n')
    except OSError as error:
        data['error'] = 'progress files unavailable: ' + str(error)
        detail += '\n' + data['error'] + '. Execution may continue; repair logging locally.'
    print(line + '\n' + detail, flush=True)
    return data


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=ROOT / 'work')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--once', action='store_true')
    mode.add_argument('--watch', action='store_true')
    parser.add_argument('--interval', type=float, default=configuration()['progress_interval_seconds'])
    args = parser.parse_args()
    if not math.isfinite(args.interval) or args.interval <= 0:
        parser.error('--interval must be finite and positive')
    try:
        while True:
            data = report(args.work_dir.resolve())
            if not args.watch:
                sys.exit(1 if data.get('error') else 0)
            time.sleep(args.interval)
    except KeyboardInterrupt:
        pass
