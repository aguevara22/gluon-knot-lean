#!/usr/bin/env python3
"""Report original proof claims with compilation and independent-review evidence.

This is an incremental report, not the complete-stage acceptance checker.
It does not count definitions, literature inputs, or supporting lemmas as proofs.
"""
import csv
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
WORK = Path(__file__).resolve().parent
ROOT = WORK.parent
sys.path.insert(0, str(ROOT))
from tools.scope import SPEC


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def snapshot():
    source = list(csv.DictReader((ROOT / 'blueprint/NODES.tsv').open(), delimiter='\t'))
    proof_ids = {r['id'] for r in source if r['action'] == 'PROVE'} | set(SPEC['extra'])
    baseline = {r['id'] for r in source} | set(SPEC['extra'])
    rows = json.loads((WORK / 'lean/lean-declarations.json').read_text())['declarations']
    by_id = {r['id']: r for r in rows}
    if len(rows) != len(by_id):
        raise ValueError('duplicate declaration-map ID')
    audit = json.loads((WORK / 'checks/declaration-audit.json').read_text())
    receipt = json.loads((WORK / 'checks/stage-development.json').read_text())
    if receipt.get('passed') is not True:
        raise ValueError('latest development audit is not successful')
    actual = {r['declaration']: r for r in audit['audit']['declarations']}
    accepted, awaiting, issues = [], [], []
    source_by_id = {r['id']: r for r in source}
    for row in rows:
        ident = row['id']
        if row.get('status') not in {'accepted', 'review', 'implemented'}:
            continue
        try:
            info = actual[row['declaration']]
            code = row['module'].replace('.', '/') + '.lean'
            if digest(WORK / 'lean' / code) != receipt['project_sha256'][code]:
                raise ValueError('source module changed after compilation/audit')
            if ident in proof_ids and info['kind'] != 'theorem':
                raise ValueError('proof claim is not a theorem')
            if row['status'] != 'accepted':
                if ident in proof_ids:
                    awaiting.append(ident)
                continue
            review = json.loads((WORK / row['review_file']).read_text())
            if not (review['id'] == ident and review['verdict'] == 'faithful'
                    and review['reviewer'] == row['reviewer'] != row['author']
                    and review['statement_sha256'] == row['statement_sha256']
                    == audit['statement_hashes'][ident]
                    and row['parameters_reviewed'] is True
                    and row['definition_equivalence_reviewed'] is True):
                raise ValueError('review identity, verdict, or semantic hash mismatch')
            if ident in source_by_id:
                if digest(ROOT / row['source']) != review['source_sha256']:
                    raise ValueError('reviewed mathematical source changed')
            files = review.get('reviewed_files_sha256', {})
            if not files:
                raise ValueError('review lacks supporting file inventory')
            for name, expected in files.items():
                path = ROOT / name
                if not path.resolve().is_relative_to(WORK.resolve()) or digest(path) != expected:
                    raise ValueError('reviewed code/supporting proof changed: ' + name)
                relative = path.relative_to(WORK / 'lean').as_posix()
                if receipt['project_sha256'].get(relative) != expected:
                    raise ValueError('reviewed supporting proof was not audited: ' + name)
            accepted.append(ident)
        except (KeyError, OSError, ValueError) as err:
            issues.append(ident + ': ' + str(err))
    proved = sorted(set(accepted) & proof_ids)
    return {
        'timestamp_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'proved_original_claims': len(proved), 'original_proof_obligations': len(proof_ids),
        'proof_percentage': 100 * len(proved) / len(proof_ids),
        'proof_ids': proved, 'compiled_proofs_awaiting_review': sorted(awaiting),
        'accepted_original_checklist': len(set(accepted) & baseline),
        'original_checklist_total': len(baseline),
        'additional_tracked_ids': sorted(set(by_id) - baseline),
        'evidence_issues': issues,
        'meaning': 'Incremental kernel-checked, independently source-reviewed original claims; not effort or complete-stage acceptance.',
    }


if __name__ == '__main__':
    try:
        data = snapshot()
    except (OSError, ValueError, KeyError) as err:
        print('Claim progress unavailable: ' + str(err))
        sys.exit(1)
    target = WORK / 'progress/claims-latest.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(data, indent=2) + '\n')
    with (WORK / 'progress/claims-history.jsonl').open('a') as stream:
        stream.write(json.dumps(data) + '\n')
    print(f"{data['proof_percentage']:.2f}% source proofs "
          f"({data['proved_original_claims']}/{data['original_proof_obligations']}); "
          f"{len(data['compiled_proofs_awaiting_review'])} compiled proofs awaiting review; "
          f"checklist {data['accepted_original_checklist']}/{data['original_checklist_total']}.")
    if data['evidence_issues']:
        print('Not counted: ' + '; '.join(data['evidence_issues']))
