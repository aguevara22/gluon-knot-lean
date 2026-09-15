#!/usr/bin/env python3
"""Install only exact reviewed candidates; leave original acceptance pending."""
import hashlib
import json
from pathlib import Path
import sys
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
CHECKS = WORK / 'checks'
LEAN = WORK / 'lean'

def read(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

report_path = WORK / 'reviews/farout-prototype.json'
assert sha(report_path) == sys.argv[1]
report = read(report_path)
assert report['verdict'] == 'faithful'
assert report['parameters_reviewed'] and report['definition_equivalence_reviewed']
evidence = report['evidence']
assert evidence['independent_kernel_session'] == 37694
assert evidence['independent_kernel_exit_code'] == 0
assert len(evidence['checked_declarations']) == 127
assert len(evidence['additional_examples']) == 48
for key in ['reviewed_files_sha256', 'inherited_review_binding', 'additional_source_sha256']:
    for filename, expected in report.get(key, {}).items():
        assert sha(ROOT / filename) == expected, filename
for stem, expected in report.get('prototype_files_sha256', {}).items():
    path = CHECKS / (stem + '.prototype.lean') if '/' not in stem else ROOT / stem
    assert sha(path) == expected, str(path)
for key in ['independent_trace_source', 'independent_trace_log']:
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']

prep_path = CHECKS / 'farout-port-preparation.json'
prep = read(prep_path)
assert len(prep['new_modules']) == 12
assert len(prep['prior_SM_files_sha256']) == 307
assert len(list((LEAN / 'SM').glob('*.lean'))) == 307
for filename, expected in prep['prior_SM_files_sha256'].items():
    assert sha(LEAN / filename) == expected, filename
assert sha(LEAN / 'Supplemental.lean') == prep['prior_Supplemental_sha256']
assert sha(LEAN / 'lean-declarations.json') == prep['prior_map_sha256']
for filename, record in prep['new_modules'].items():
    assert not (ROOT / filename).exists(), filename
    assert sha(ROOT / record['candidate']) == record['candidate_sha256']
    for fragment in record['source_fragments']:
        assert sha(ROOT / fragment['source']) == fragment['source_sha256']
    assert sha(ROOT / record['root_receipt']) == record['root_receipt_sha256']
    root_result = read(ROOT / record['root_receipt'])
    # The earlier direct-kernel receipt names its actual process result exit_code.
    assert root_result.get('subprocess_exit_code', root_result.get('exit_code')) == 0

# All evidence is verified before any project mutation.
for filename, record in prep['new_modules'].items():
    (ROOT / filename).write_bytes((ROOT / record['candidate']).read_bytes())
supplemental = LEAN / 'Supplemental.lean'
supplemental.write_bytes(supplemental.read_bytes() + b'\nimport SM.Farout\n')
map_path = LEAN / 'lean-declarations.json'
mapping = read(map_path)
row = next(r for r in mapping['declarations'] if r['id'] == 'lem:farout')
assert row['status'] == 'pending' and not row['declaration']
row.update({'declaration': 'SM.farout', 'module': 'SM.Farout', 'status': 'review',
            'author': 'root-implementation-20260910'})
map_path.write_text(json.dumps(mapping, indent=2) + '\n')
prep['state'] = 'Twelve exact prototype-reviewed modules installed; canonical review pending'
prep['external_reviews_sha256']['farout-prototype.json'] = sha(report_path)
prep_path.write_text(json.dumps(prep, indent=2) + '\n')
result = {'utc': datetime.now(timezone.utc).isoformat(), 'installed_modules': 12,
          'canonical_SM_modules': 319, 'all307_prior_SM_unchanged': True,
          'only_map_change': 'lem:farout candidate review row', 'source_acceptance_increment': 0,
          'full_prototype_review_sha256': sha(report_path),
          'preparation_sha256': sha(prep_path), 'Supplemental_sha256': sha(supplemental),
          'map_sha256': sha(map_path)}
(CHECKS / 'farout-port-installed.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
