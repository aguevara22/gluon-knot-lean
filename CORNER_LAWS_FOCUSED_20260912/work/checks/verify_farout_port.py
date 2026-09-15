#!/usr/bin/env python3
"""Verify exact installation and audit evidence; never infer fidelity from hashes."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
LEAN = WORK / 'lean'
CHECKS = WORK / 'checks'

def read(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def checkhash(path, expected):
    assert path.is_file() and sha(path) == expected, str(path)

receipt_path = Path(sys.argv[1])
if not receipt_path.is_absolute():
    receipt_path = ROOT / receipt_path
receipt = read(receipt_path)
assert receipt['passed'] and not receipt['stage_accepted']
assert receipt['mapped_declarations'] == 39
for path, expected in receipt['project_sha256'].items():
    checkhash(LEAN / path, expected)
for path, expected in receipt['bundle_sha256'].items():
    checkhash(ROOT / path, expected)
assert (CHECKS / 'stage-development.json').read_bytes() == receipt_path.read_bytes()

prep = read(CHECKS / 'farout-port-preparation.json')
assert len(prep['prior_SM_files_sha256']) == 307
assert len(list((LEAN / 'SM').glob('*.lean'))) == 319
for path, expected in prep['prior_SM_files_sha256'].items():
    checkhash(LEAN / path, expected)
assert len(prep['new_modules']) == 12
for installed, record in prep['new_modules'].items():
    checkhash(ROOT / installed, record['candidate_sha256'])
    assert (ROOT / installed).read_bytes() == (ROOT / record['candidate']).read_bytes()
    for fragment in record['source_fragments']:
        checkhash(ROOT / fragment['source'], fragment['source_sha256'])
    checkhash(ROOT / record['root_receipt'], record['root_receipt_sha256'])

oldmap = read(CHECKS / 'lean-declarations-before-farout.json')
newmap = read(LEAN / 'lean-declarations.json')
assert len(oldmap['declarations']) == len(newmap['declarations'])
oldrows = {r['id']: r for r in oldmap['declarations']}
newrows = {r['id']: r for r in newmap['declarations']}
assert set(oldrows) == set(newrows)
for name in oldrows:
    if name != 'lem:farout':
        assert oldrows[name] == newrows[name], name
row = newrows['lem:farout']
assert row['declaration'] == 'SM.farout' and row['module'] == 'SM.Farout'
assert row['status'] in {'review', 'accepted'}
assert row['source'] == 'reference/SM/sm-2-amplitude.tex' and row['line'] == 146

audit = read(CHECKS / 'declaration-audit.json')
oldaudit = read(CHECKS / 'checkpoint-066-declaration-audit.json')
assert len(audit['statement_hashes']) == 39
assert len(oldaudit['statement_hashes']) == 38
for name, expected in oldaudit['statement_hashes'].items():
    assert audit['statement_hashes'][name] == expected, name
assert audit['audit']['checked'] == receipt['audited_declarations']
assert receipt['audited_declarations'] > 3965
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for r in audit['audit']['declarations'])
main = next(r for r in audit['audit']['declarations'] if r['declaration'] == 'SM.farout')
assert main['kind'] == 'theorem' and main['module'] == 'SM.Farout'

if row['status'] == 'accepted':
    report = read(WORK / row['review_file'])
    assert report['id'] == 'lem:farout' and report['verdict'] == 'faithful'
    assert report['reviewer'] == row['reviewer'] != row['author']
    assert report['statement_sha256'] == row['statement_sha256'] == audit['statement_hashes']['lem:farout']
    assert report['parameters_reviewed'] and report['definition_equivalence_reviewed']
    assert report['source_claim_accepted'] and report['in_theorem_library'] and report['reason']
    checkhash(ROOT / row['source'], report['source_sha256'])

print(json.dumps({'passed': True, 'receipt': str(receipt_path.relative_to(ROOT)),
    'canonical_SM_modules': 319, 'prior307_unchanged': True,
    'all38_previous_semantics_unchanged': True, 'only_map_change': 'lem:farout',
    'farout_status': row['status'], 'farout_semantic_sha256': audit['statement_hashes']['lem:farout'],
    'audited_declarations': receipt['audited_declarations'], 'stage_complete': False}, indent=2))
