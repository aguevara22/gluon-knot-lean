#!/usr/bin/env python3
"""Verify the independent avoidance prototype review without source acceptance."""
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.receipts import matches, hashes, project_files

WORK = ROOT / 'work'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rp = WORK / 'reviews/multivariate-avoidance-prototype.json'
r = json.loads(rp.read_text())
assert sha(rp) == 'd2853b0311f247589c24e7183ad6b8e38bed73e6e5ed3da8099264ee3be5c985'
assert r['verdict'] == 'partial' and r['implemented_scope_verdict'] == 'faithful'
assert not r['source_claim_accepted']
assert matches(ROOT, r['reviewed_files_sha256'])
assert sha(ROOT / r['source']) == r['source_sha256']
assert r['parameters_reviewed'] and r['definition_equivalence_reviewed']
assert matches(ROOT, r['pins']['pin_files_sha256'])
library_root = (WORK / 'lean/.lake/packages/mathlib').resolve()
for key in ('direct_import_files_sha256', 'inspected_supporting_library_files_sha256'):
    for name, digest in r['pins'][key].items():
        path = (ROOT / name).resolve()
        assert path.is_relative_to(library_root) and sha(path) == digest
e = r['evidence']
assert e['independent_kernel_exit_code'] == e['root_build_exit_code'] == 0
for key in ('independent_check_source', 'independent_trace_log', 'root_build_log', 'root_result_record'):
    assert sha(ROOT / e[key]) == e[key + '_sha256']
assert (ROOT / e['independent_check_source']).read_text().startswith(
    (ROOT / r['prototype_file']).read_text())
assert len(e['declaration_axioms']) == 5
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for a in e['declaration_axioms'].values())
assert e['empty_finite_condition_family_checked']
b = r['receipt_binding']
p = ROOT / b['receipt']
assert sha(p) == b['receipt_sha256']
receipt = json.loads(p.read_text())
assert receipt['project_sha256'] == hashes(WORK / 'lean', project_files(WORK / 'lean'))
assert matches(ROOT, receipt['bundle_sha256'])
assert sha(ROOT / b['declaration_audit']) == b['declaration_audit_sha256']
out = {'passed': True, 'prototype_review_sha256': sha(rp),
       'prototype_sha256': r['prototype_sha256'],
       'independent_trace_sha256': e['independent_trace_log_sha256'],
       'receipt_sha256': sha(p), 'standard_only_axioms': True,
       'exact_project_and_frozen_inventory_current': True, 'original_increment': 0,
       'prototype_remains_outside_theorem_library': True}
(WORK / 'checks/checkpoint-052-avoidance-prototype-verification.json').write_text(
    json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
