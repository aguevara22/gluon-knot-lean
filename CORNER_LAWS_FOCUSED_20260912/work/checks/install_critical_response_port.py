#!/usr/bin/env python3
"""Install exact independently reviewed helper bodies; do not change the map."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
LEAN = WORK / 'lean'
CHECKS = WORK / 'checks'

def read(p):
    return json.loads(p.read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

report_path = WORK / 'reviews/critical-source-response-prototype.json'
assert sha(report_path) == 'bea6534e4ed4850ee5dbe41e31a07df1e01964e7a52e3ee4725c346e43f9ed0c'
report = read(report_path)
assert report['verdict'] == 'faithful'
assert report['parameters_reviewed'] and report['definition_equivalence_reviewed']
assert not report['source_claim_accepted']
assert report['reviewer'] != report['implementer']
assert sha(ROOT / report['source']) == report['source_sha256']
assert sha(ROOT / report['separate_source_domain_note']) == report['separate_source_domain_note_sha256']
evidence = report['evidence']
assert evidence['independent_kernel_session'] == 70536
assert evidence['independent_kernel_exit_code'] == 0
assert evidence['declaration_count'] == 53 and evidence['additional_example_count'] == 41
for group in ['reviewed_files_sha256', 'inherited_review_binding', 'additional_source_sha256']:
    for name, expected in report.get(group, {}).items():
        assert sha(ROOT / name) == expected, name
for stem, expected in report['prototype_files_sha256'].items():
    p = CHECKS / (stem + '.prototype.lean') if '/' not in stem else ROOT / stem
    assert sha(p) == expected, str(p)
for key, expected in evidence.items():
    if key.endswith('_sha256') and key[:-7] in evidence:
        p = ROOT / evidence[key[:-7]]
        assert p.is_file() and sha(p) == expected, key
log = (ROOT / evidence['independent_trace_log']).read_text()
assert 'error:' not in log
traces = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log, re.S)
empty = re.findall(r"'([^']+)' does not depend on any axioms", log)
assert len(traces) + len(empty) == 94
for name, axioms in traces:
    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
        'propext', 'Classical.choice', 'Quot.sound'}, name

prep_path = CHECKS / 'critical-response-port-preparation.json'
prep = read(prep_path)
assert len(prep['prior_SM_files_sha256']) == 319
assert len(list((LEAN / 'SM').glob('*.lean'))) == 319
for name, expected in prep['prior_SM_files_sha256'].items():
    assert sha(LEAN / name) == expected, name
assert sha(LEAN / 'Supplemental.lean') == prep['prior_Supplemental_sha256']
assert sha(LEAN / 'lean-declarations.json') == prep['prior_map_sha256']
assert len(prep['new_modules']) == 8
for name, record in prep['new_modules'].items():
    assert not (ROOT / name).exists(), name
    assert sha(ROOT / record['candidate']) == record['candidate_sha256'], name
    assert sha(ROOT / record['source_body']) == record['source_body_sha256'], name
    expected = ''.join('import ' + m + '\n' for m in record['imports']) + '\n'
    expected += (ROOT / record['source_body']).read_text()
    assert (ROOT / record['candidate']).read_text() == expected, name
    assert sha(ROOT / record['root_receipt']) == record['root_receipt_sha256'], name
    root_result = read(ROOT / record['root_receipt'])
    assert root_result['exit_code'] == 0, name
    for source, expected_hash in root_result['files_sha256'].items():
        assert sha(ROOT / source) == expected_hash, source

# All preconditions pass before the first canonical file is written.
for name, record in prep['new_modules'].items():
    (ROOT / name).write_bytes((ROOT / record['candidate']).read_bytes())
supplemental = LEAN / 'Supplemental.lean'
supplemental.write_bytes(supplemental.read_bytes() + b'\nimport SM.CriticalSourceResponse\n')
assert sha(LEAN / 'lean-declarations.json') == prep['prior_map_sha256']
result = {
    'utc': datetime.now(timezone.utc).isoformat(),
    'installed_modules': 8, 'canonical_SM_modules': 327,
    'all319_prior_SM_unchanged': True, 'map_unchanged': True,
    'source_acceptance_increment': 0, 'canonical_review_pending': True,
    'full_prototype_review_sha256': sha(report_path),
    'preparation_sha256': sha(prep_path),
    'Supplemental_sha256': sha(supplemental),
    'map_sha256': sha(LEAN / 'lean-declarations.json'),
}
(CHECKS / 'critical-response-port-installed.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
