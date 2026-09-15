#!/usr/bin/env python3
"""Bind the independently reviewed strict-mesh prototype to its exact evidence.

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

rp = ROOT / 'work/reviews/uniform-mesh-prototype.json'
review = json.loads(rp.read_text())
assert review['reviewer'] == 'review_chirotope-independent-20260910'
assert review['verdict'] == 'partial' and review['implemented_scope_verdict'] == 'faithful'
assert review['source_claim_accepted'] is False and review['in_theorem_library'] is False
assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
assert sha(ROOT / review['source']) == review['source_sha256']
prototype_path = ROOT / 'work/checks/UniformMesh.prototype.lean'
assert sha(prototype_path) == 'aa11f56fdb9fdfcea3aec07c0803cca03b51902f4fc38b1f50730735aa4ad691'
assert ROOT / review['prototype_file'] == prototype_path
assert sha(prototype_path) == review['prototype_sha256']
prototype = prototype_path.read_text()
assert not re.findall(r'^import SM\.', prototype, re.M)
assert not re.findall(r'\b(?:sorry|axiom|native_decide)\b', prototype)
assert matches(ROOT, review['pins']['pin_files_sha256'])
assert review['pins']['lean_toolchain'] == 'leanprover/lean4:v4.34.0-rc2'
assert review['pins']['mathlib_revision'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
library_root = (LEAN / '.lake/packages/mathlib').resolve()
for key in ['direct_imports_sha256', 'supporting_pinned_library_files_read_sha256']:
    for path, expected in review['pins'][key].items():
        actual = (library_root / path).resolve()
        assert actual.is_relative_to(library_root) and sha(actual) == expected
evidence = review['evidence']
assert evidence['independent_kernel_exit_code'] == 0
assert evidence['checked_declarations'] == len(evidence['declaration_axioms']) == 9
assert all(set(a) <= {'propext', 'Classical.choice', 'Quot.sound'}
           for a in evidence['declaration_axioms'].values())
assert evidence['additional_examples_passed'] and len(evidence['additional_examples']) == 2
for key in ['independent_trace_source', 'independent_trace_log', 'successful_build_log',
            'prototype_result']:
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
trace = (ROOT / evidence['independent_trace_log']).read_text()
assert 'error:' not in trace and 'sorryAx' not in trace
assert (ROOT / evidence['independent_trace_source']).read_text().startswith(
    prototype.split('#print axioms', 1)[0])
root_result = json.loads((ROOT / 'work/checks/uniform-mesh-prototype-result.json').read_text())
assert root_result['kernel_session'] == 73550 and root_result['kernel_exit_code'] == 0
assert sha(ROOT / root_result['prototype']) == root_result['prototype_sha256']
assert sha(ROOT / root_result['log']) == root_result['log_sha256']
root_log = (ROOT / root_result['log']).read_text()
assert 'error:' not in root_log and 'sorryAx' not in root_log
receipt_path = ROOT / 'work/checks/checkpoint-055-output.json'
receipt = json.loads(receipt_path.read_text())
assert receipt['passed'] and not receipt['stage_accepted']
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert matches(ROOT, receipt['bundle_sha256'])
assert len(receipt['project_sha256']) == 274 and len(receipt['bundle_sha256']) == 38
assert not (LEAN / 'SM/UniformMesh.lean').exists()
out = {'passed': True, 'review': str(rp.relative_to(ROOT)), 'review_sha256': sha(rp),
       'prototype_sha256': sha(prototype_path), 'receipt_sha256': sha(receipt_path),
       'independent_kernel_session': evidence['independent_kernel_session'],
       'independent_kernel_exit_code': 0, 'standard_only_axiom_sets': 9,
       'additional_semantic_examples_passed': 2, 'local_SM_imports': 0,
       'in_theorem_library': False, 'original_proof_increment': 0,
       'source_claim_accepted': False}
target = ROOT / 'work/checks/checkpoint-055-uniform-mesh-prototype-verification.json'
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
