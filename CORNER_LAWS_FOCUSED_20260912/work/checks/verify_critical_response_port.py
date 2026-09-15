#!/usr/bin/env python3
"""Check exact helper integration and preservation; source fidelity is reviewed separately."""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
LEAN = WORK / 'lean'
CHECKS = WORK / 'checks'

def read(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

receipt_path = Path(sys.argv[1])
if not receipt_path.is_absolute():
    receipt_path = ROOT / receipt_path
receipt = read(receipt_path)
assert receipt['passed'] and not receipt['stage_accepted']
assert receipt['mapped_declarations'] == 39
for name, expected in receipt['project_sha256'].items():
    assert sha(LEAN / name) == expected, name
for name, expected in receipt['bundle_sha256'].items():
    assert sha(ROOT / name) == expected, name
assert (CHECKS / 'stage-development.json').read_bytes() == receipt_path.read_bytes()

prep = read(CHECKS / 'critical-response-port-preparation.json')
installed = read(CHECKS / 'critical-response-port-installed.json')
assert sha(CHECKS / 'critical-response-port-preparation.json') == installed['preparation_sha256']
assert len(prep['prior_SM_files_sha256']) == 319
assert len(list((LEAN / 'SM').glob('*.lean'))) == 327
for name, expected in prep['prior_SM_files_sha256'].items():
    assert sha(LEAN / name) == expected, name
assert len(prep['new_modules']) == 8
for name, rec in prep['new_modules'].items():
    assert sha(ROOT / name) == rec['candidate_sha256'], name
    assert (ROOT / name).read_bytes() == (ROOT / rec['candidate']).read_bytes(), name
    assert sha(ROOT / rec['source_body']) == rec['source_body_sha256'], name
    assert sha(ROOT / rec['root_receipt']) == rec['root_receipt_sha256'], name
    expected = ''.join('import ' + m + '\n' for m in rec['imports']) + '\n'
    expected += (ROOT / rec['source_body']).read_text()
    assert (ROOT / name).read_text() == expected, name
supp = (LEAN / 'Supplemental.lean').read_bytes()
suffix = b'\nimport SM.CriticalSourceResponse\n'
assert supp.endswith(suffix)
assert hashlib.sha256(supp[:-len(suffix)]).hexdigest() == prep['prior_Supplemental_sha256']
assert sha(LEAN / 'Supplemental.lean') == installed['Supplemental_sha256']
assert sha(LEAN / 'lean-declarations.json') == prep['prior_map_sha256'] == installed['map_sha256']

old = read(CHECKS / 'checkpoint-068-declaration-audit.json')
audit = read(CHECKS / 'declaration-audit.json')
assert len(old['statement_hashes']) == 39
assert audit['statement_hashes'] == old['statement_hashes']
assert len(audit['audit']['declarations']) == 39
assert audit['audit']['checked'] == receipt['audited_declarations'] > 4169
assert all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for row in audit['audit']['declarations'])
report_path = WORK / 'reviews/critical-source-response-prototype.json'
assert sha(report_path) == installed['full_prototype_review_sha256']
report = read(report_path)
assert report['verdict'] == 'faithful' and not report['source_claim_accepted']
assert report['parameters_reviewed'] and report['definition_equivalence_reviewed']
assert report['evidence']['independent_kernel_exit_code'] == 0
assert report['evidence']['declaration_count'] == 53
assert report['evidence']['additional_example_count'] == 41
for group in ['reviewed_files_sha256', 'inherited_review_binding', 'additional_source_sha256']:
    for name, expected in report.get(group, {}).items():
        assert sha(ROOT / name) == expected, name

print(json.dumps({
    'passed': True, 'receipt': str(receipt_path.relative_to(ROOT)),
    'receipt_sha256': sha(receipt_path),
    'canonical_SM_modules': 327, 'all319_prior_SM_unchanged': True,
    'all39_mapped_semantics_unchanged': True, 'map_unchanged': True,
    'audited_declarations': receipt['audited_declarations'],
    'source_claim_acceptance_increment': 0, 'stage_complete': False,
    'canonical_fidelity_review_required_separately': True,
}, indent=2))
