#!/usr/bin/env python3
"""Bind the independently reviewed global timed-germ prototype to its exact evidence.

This does not accept thm:relgp or include the prototype in the theorem library.
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

rp = ROOT / 'work/reviews/global-timed-germs-prototype.json'
review = json.loads(rp.read_text())
assert review['reviewer'] == 'review_chirotope-independent-20260910'
assert review['verdict'] == 'partial' and review['implemented_scope_verdict'] == 'faithful'
assert review['source_claim_accepted'] is False and review['in_theorem_library'] is False
assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
assert sha(ROOT / review['source']) == review['source_sha256']
prototype_path = ROOT / 'work/checks/GlobalTimedGerms.prototype.lean'
assert sha(prototype_path) == '50c70047983855005d4595926624deae6ccdec755511ba3a2e97c1aebbf3016f'
assert ROOT / review['prototype_file'] == prototype_path
assert sha(prototype_path) == review['prototype_sha256']
prototype = prototype_path.read_text()
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = LEAN / (module.replace('.', '/') + '.lean')
    for dep in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
        visit(dep)
for module in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', prototype, re.M):
    visit(module)
closure = {'work/lean/' + m.replace('.', '/') + '.lean':
           sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}
assert len(closure) == 83 and review['reviewed_files_sha256'] == closure
binding = review['inherited_review_binding']
covered = set()
for path, expected in binding['reviews_sha256'].items():
    assert sha(ROOT / path) == expected
    inherited = json.loads((ROOT / path).read_text())['reviewed_files_sha256']
    covered.update(p for p, h in closure.items() if inherited.get(p) == h)
assert covered == set(closure)
assert len(review['body_files_sha256']) == 2
assert matches(ROOT, review['body_files_sha256'])
for path in review['body_files_sha256']:
    assert (ROOT / path).read_text() in prototype
local_prefix = (ROOT / 'work/checks/MultiCellCoordinatePolyline.prototype.lean').read_text().split('#print axioms', 1)[0]
assert local_prefix in prototype
assert not re.findall(r'\b(?:sorry|axiom|native_decide)\b', prototype)
assert matches(ROOT, review['pins']['pin_files_sha256'])
assert review['pins']['lean_toolchain'] == 'leanprover/lean4:v4.34.0-rc2'
assert review['pins']['mathlib_revision'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
library_root = (LEAN / '.lake/packages/mathlib').resolve()
for key in ['additional_pinned_library_files_read_sha256']:
    for path, expected in review['pins'][key].items():
        actual = (library_root / path).resolve()
        assert actual.is_relative_to(library_root) and sha(actual) == expected
evidence = review['evidence']
assert evidence['independent_kernel_exit_code'] == 0
assert len(evidence['checked_declarations']) == len(evidence['declaration_axioms']) == 12
assert set(evidence['checked_declarations']) == set(evidence['declaration_axioms'])
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for a in evidence['declaration_axioms'].values())
assert evidence['additional_examples_passed'] and len(evidence['additional_examples']) == 2
for key in ['independent_trace_source', 'independent_trace_log', 'successful_build_log',
            'independent_closure_evidence']:
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
trace = (ROOT / evidence['independent_trace_log']).read_text()
assert 'error:' not in trace and 'sorryAx' not in trace
assert (ROOT / evidence['independent_trace_source']).read_text().startswith(
    prototype.split('#print axioms', 1)[0])
assert sha(ROOT / evidence['root_result_file']) == evidence['root_result_sha256']
root_result = json.loads((ROOT / evidence['root_result_file']).read_text())
assert root_result['successful_kernel_session'] == 5732
assert root_result['successful_kernel_exit_code'] == 0
assert matches(ROOT / 'work', root_result['files_sha256'])
root_log = (ROOT / evidence['successful_build_log']).read_text()
assert not re.search(r'error[:(]', root_log) and 'sorryAx' not in root_log
receipt_path = ROOT / 'work/checks/checkpoint-056-output.json'
receipt = json.loads(receipt_path.read_text())
assert receipt['passed'] and not receipt['stage_accepted']
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert matches(ROOT, receipt['bundle_sha256'])
assert len(receipt['project_sha256']) == 279 and len(receipt['bundle_sha256']) == 38
assert not (LEAN / 'SM/GlobalTimedGerms.lean').exists()
out = {'passed': True, 'review': str(rp.relative_to(ROOT)), 'review_sha256': sha(rp),
       'prototype_sha256': sha(prototype_path), 'receipt_sha256': sha(receipt_path),
       'independent_kernel_session': evidence['independent_kernel_session'],
       'independent_kernel_exit_code': 0, 'standard_only_axiom_sets': 12,
       'additional_semantic_examples_passed': 2, 'local_SM_import_closure': 83,
       'in_theorem_library': False, 'original_proof_increment': 0,
       'source_claim_accepted': False}
target = ROOT / 'work/checks/checkpoint-056-global-timed-germs-prototype-verification.json'
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
