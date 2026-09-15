#!/usr/bin/env python3
"""Verify integration of the reviewed actual timed path and event-certificate port.

Full thm:relgp is deliberately not accepted by this evidence check.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work'
LEAN = WORK / 'lean'
sys.path.insert(0, str(ROOT))
from tools.receipts import hashes, matches, project_files
from work.claim_progress import snapshot

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

rp = Path(sys.argv[1]).resolve()
receipt = json.loads(rp.read_text())
old = json.loads((WORK / 'checks/checkpoint-056-output.json').read_text())
assert receipt['passed'] is True and receipt['stage_accepted'] is False
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert receipt['bundle_sha256'] == old['bundle_sha256']
assert matches(ROOT, receipt['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == rp.read_bytes()
old_sm = {p: h for p, h in old['project_sha256'].items() if p.startswith('SM/')}
assert len(old_sm) == 273 and matches(LEAN, old_sm)
new_modules = ['TimedCoordinatePolyline', 'MultiCellCoordinatePolyline', 'GlobalTimedCollars',
               'GlobalTimedGerms', 'SmoothControlGraph', 'GlobalEventCertificate']
assert set(receipt['project_sha256']) - set(old['project_sha256']) == {
    'SM/' + m + '.lean' for m in new_modules}
assert {p for p, h in old['project_sha256'].items()
        if receipt['project_sha256'][p] != h} == {'Supplemental.lean'}

audit_path = WORK / 'checks/declaration-audit.json'
audit = json.loads(audit_path.read_text())
assert audit['audit']['checked'] == receipt['audited_declarations']
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(d['axioms']) <= standard for d in audit['audit']['declarations'])
rows = json.loads((LEAN / 'lean-declarations.json').read_text())['declarations']
accepted = [r for r in rows if r['status'] == 'accepted']
assert len(accepted) == 30
for row in accepted:
    review = json.loads((WORK / row['review_file']).read_text())
    assert row['statement_sha256'] == review['statement_sha256'] == audit['statement_hashes'][row['id']]
    assert row['reviewer'] == review['reviewer'] != row['author']
    assert review['verdict'] == 'faithful'
    assert matches(ROOT, review['reviewed_files_sha256'])
    source = review.get('source', 'reference/SM/sm-1-polygons.tex')
    assert sha(ROOT / source) == review['source_sha256']

seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = LEAN / (module.replace('.', '/') + '.lean')
    for dep in re.findall(r'^import (SM\.[A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
        visit(dep)
for module in new_modules:
    visit('SM.' + module)
closure = {'work/lean/' + m.replace('.', '/') + '.lean':
           sha(LEAN / (m.replace('.', '/') + '.lean')) for m in sorted(seen)}
review_path = WORK / 'reviews/global-event-port.json'
review = json.loads(review_path.read_text())
assert review['verdict'] == 'partial' and review['implemented_scope_verdict'] == 'faithful'
assert review['source_claim_accepted'] is False
assert review['reviewer'] == 'review_chirotope-independent-20260910'
assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
assert review['reviewed_files_sha256'] == closure and len(closure) == 89
assert matches(ROOT, review['canonical_module_files_sha256'])
covered = set()
for path, expected in review['inherited_review_binding']['reviews_sha256'].items():
    assert sha(ROOT / path) == expected
    inherited = json.loads((ROOT / path).read_text())['reviewed_files_sha256']
    covered.update(p for p, h in closure.items() if inherited.get(p) == h)
assert covered == set(closure) - set(review['canonical_module_files_sha256'])
assert len(covered) == 83
assert sha(ROOT / review['source']) == review['source_sha256']
assert matches(ROOT, review['pins']['pin_files_sha256'])
assert review['pins']['lean_toolchain'] == 'leanprover/lean4:v4.34.0-rc2'
assert review['pins']['mathlib_revision'] == '85e3a25e006c35636f0e53b0e9296caca2685bc0'
library_root = (LEAN / '.lake/packages/mathlib').resolve()
for path, expected in review['pins'].get('additional_pinned_library_files_read_sha256', {}).items():
    actual = (library_root / path).resolve()
    assert actual.is_relative_to(library_root) and sha(actual) == expected
evidence = review['evidence']
assert evidence['independent_kernel_exit_code'] == 0
assert evidence['successful_build_exit_code'] == 0
assert len(evidence['checked_declarations']) == len(evidence['declaration_axioms']) == 26
assert set(evidence['checked_declarations']) == set(evidence['declaration_axioms'])
assert evidence['additional_examples_passed'] and len(evidence['additional_examples']) == 5
assert all(set(a) <= standard for a in evidence['declaration_axioms'].values())
for key in ['independent_trace_source', 'independent_trace_log', 'successful_build_log',
            'candidate_manifest', 'independent_closure_evidence']:
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
trace = (ROOT / evidence['independent_trace_log']).read_text()
assert not re.search(r'error[:(]', trace) and 'sorryAx' not in trace

candidate_path = WORK / 'checks/global-event-port-candidate-files.json'
candidate = json.loads(candidate_path.read_text())
assert sha(candidate_path) == '1d07f6a3491a664d7d64c1b5ddfdf44683c076751032c538a17976484bf52c21'
assert candidate['actual_local_closure_sha256'] == closure
assert candidate['prior_SM_files_sha256'] == old_sm
assert matches(LEAN, candidate['prior_SM_files_sha256'])
assert len(candidate['new_modules']) == 6
for path, binding in candidate['new_modules'].items():
    port_path = ROOT / path
    prototype_path = ROOT / binding['source']
    assert sha(port_path) == binding['sha256']
    assert sha(prototype_path) == binding['source_sha256']
    prototype = prototype_path.read_text().split('#print axioms', 1)[0]
    port = port_path.read_text()
    body = prototype[prototype.index('namespace SM'):].strip() + '\n'
    assert hashlib.sha256(body.encode()).hexdigest() == binding['body_sha256']
    assert body == port[port.index('namespace SM'):]
assert sha(LEAN / 'Supplemental.lean') == candidate['new_Supplemental_sha256']
root_result_path = WORK / 'checks/global-event-port-build-result.json'
assert sha(root_result_path) == evidence['build_result_sha256']
assert matches(ROOT, evidence['example_sources_sha256'])
root_result = json.loads(root_result_path.read_text())
assert root_result['successful_build_session'] == 46292
assert root_result['successful_build_exit_code'] == 0
assert sha(candidate_path) == root_result['candidate_manifest_sha256']
assert sha(WORK / root_result['build_log']) == root_result['build_log_sha256']
assert not re.search(r'error[:(]', (WORK / root_result['build_log']).read_text())
for name in ['timed-coordinate-polyline', 'multi-cell-coordinate-polyline',
             'global-timed-germs', 'smooth-control-graph', 'global-event-certificate']:
    verification = json.loads((WORK / f'checks/checkpoint-056-{name}-prototype-verification.json').read_text())
    assert verification['passed'] and verification['original_proof_increment'] == 0
    assert verification['receipt_sha256'] == sha(WORK / 'checks/checkpoint-056-output.json')
    assert verification['review_sha256'] == sha(ROOT / verification['review'])
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == 14 and progress['accepted_original_checklist'] == 29
assert progress['compiled_proofs_awaiting_review'] == []
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(rp),
       'audit_sha256': sha(audit_path), 'previous_SM_modules_unchanged': 273,
       'SM_modules': 279, 'new_modules': new_modules,
       'audited_declarations': receipt['audited_declarations'],
       'project_files': len(receipt['project_sha256']), 'frozen_files': len(receipt['bundle_sha256']),
       'accepted_review_bindings_current': len(accepted),
       'new_review_file': str(review_path.relative_to(ROOT)), 'new_review_sha256': sha(review_path),
       'reviewed_import_closure': len(closure),
       'independent_axiom_sets': len(evidence['checked_declarations']),
       'additional_semantic_examples_passed': 5, 'inherited_review_files_current': 83,
       'all_six_port_mathematical_bodies_unchanged': True,
       'original_thm_relgp_accepted': False, 'progress': progress}
target = rp.with_name(rp.name.replace('-output.json', '-global-event-port-verification.json'))
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
