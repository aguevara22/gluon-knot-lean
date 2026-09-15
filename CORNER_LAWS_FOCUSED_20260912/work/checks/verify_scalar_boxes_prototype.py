#!/usr/bin/env python3
"""Bind independent prototype review to exact source, trace and import bytes.

This checks evidence integrity; it does not accept the original source theorem.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / 'work/lean'
sys.path.insert(0, str(ROOT))
from tools.receipts import hashes, matches, project_files

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

review_path = ROOT / 'work/reviews/scalar-boxes-prototype.json'
review = json.loads(review_path.read_text())
assert review['reviewer'] == 'review_chirotope-independent-20260910'
assert review['verdict'] == 'partial'
assert review['implemented_scope_verdict'] == 'faithful'
assert review['source_claim_accepted'] is False
assert review['in_theorem_library'] is False
assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
for key in ['prototype', 'source']:
    name = review['prototype_file'] if key == 'prototype' else review['source']
    assert sha(ROOT / name) == review[key + '_sha256']

seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = LEAN / (module.replace('.', '/') + '.lean')
    for dep in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
        visit(dep)

for module in review['import_closure_roots']:
    visit(module)
closure = {'work/lean/' + m.replace('.', '/') + '.lean':
           sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}
assert closure == review['reviewed_files_sha256']
assert len(closure) == review['import_closure_file_count'] == 23
covered = set()
for path, binding in review['inherited_review_binding']['reviews'].items():
    assert sha(ROOT / path) == binding['sha256']
    inherited = json.loads((ROOT / path).read_text())['reviewed_files_sha256']
    matching = {p for p, h in closure.items() if inherited.get(p) == h}
    assert len(matching) == binding['matching_file_count_in_current_closure']
    covered.update(matching)
assert covered == set(closure)

pins = review['pins']
assert matches(ROOT, pins['pin_files_sha256'])
assert pins['lean_toolchain'] == 'leanprover/lean4:v4.34.0-rc2'
assert pins['mathlib_revision'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
library_root = (LEAN / '.lake/packages/mathlib').resolve()
for path, expected in pins['additional_pinned_library_files_read_sha256'].items():
    actual = (library_root / path).resolve()
    assert actual.is_relative_to(library_root) and sha(actual) == expected

evidence = review['evidence']
for key in ['independent_trace_source', 'independent_trace_log', 'prototype_root_log',
            'prototype_result', 'independent_closure_evidence']:
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
assert evidence['independent_kernel_exit_code'] == 0
assert evidence['prototype_root_kernel_exit_code'] == 0
assert evidence['additional_examples_passed']
assert evidence['checked_declarations'] == len(evidence['declaration_axioms']) == 14
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(a) <= standard for a in evidence['declaration_axioms'].values())
trace = (ROOT / evidence['independent_trace_log']).read_text()
assert 'error:' not in trace and 'sorryAx' not in trace
prototype = (ROOT / review['prototype_file']).read_text()
prefix = prototype.split('#print axioms', 1)[0]
assert (ROOT / evidence['independent_trace_source']).read_text().startswith(prefix)

context = review['audit_context']
receipt_path = ROOT / context['receipt']
assert sha(receipt_path) == context['receipt_sha256']
receipt = json.loads(receipt_path.read_text())
assert receipt['passed'] and not receipt['stage_accepted']
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert matches(ROOT, receipt['bundle_sha256'])
assert len(receipt['project_sha256']) == 269
assert len(receipt['bundle_sha256']) == 38
assert len([p for p in receipt['project_sha256'] if p.startswith('SM/')]) == 263
assert not (LEAN / 'SM/ScalarBoxes.lean').exists()
result = {
    'passed': True, 'review': str(review_path.relative_to(ROOT)),
    'review_sha256': sha(review_path), 'prototype_sha256': review['prototype_sha256'],
    'receipt_sha256': sha(receipt_path), 'exact_import_closure': 23,
    'independent_kernel_session': evidence['independent_kernel_session'],
    'independent_kernel_exit_code': 0, 'standard_only_axiom_sets': 14,
    'additional_semantic_examples_passed': True,
    'source_claim_accepted': False, 'original_proof_increment': 0,
    'in_theorem_library': False,
}
out = ROOT / 'work/checks/checkpoint-054-scalar-boxes-prototype-verification.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
