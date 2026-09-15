#!/usr/bin/env python3
"""Verify integration of the reviewed curve cubes and joint waypoints.

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
old = json.loads((WORK / 'checks/checkpoint-055-output.json').read_text())
assert receipt['passed'] is True and receipt['stage_accepted'] is False
assert receipt['project_sha256'] == hashes(LEAN, project_files(LEAN))
assert receipt['bundle_sha256'] == old['bundle_sha256']
assert matches(ROOT, receipt['bundle_sha256'])
assert (WORK / 'checks/stage-development.json').read_bytes() == rp.read_bytes()
old_sm = {p: h for p, h in old['project_sha256'].items() if p.startswith('SM/')}
assert len(old_sm) == 268 and matches(LEAN, old_sm)
new_modules = ['UniformMesh', 'UniformMeshCells', 'CurveCubeSubdivision',
               'CubeWaypointDomains', 'CubeWaypoints']
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
review_path = WORK / 'reviews/curve-cubes-waypoints.json'
review = json.loads(review_path.read_text())
assert review['verdict'] == 'partial' and review['implemented_scope_verdict'] == 'faithful'
assert review['source_claim_accepted'] is False
assert review['reviewer'] == 'review_chirotope-independent-20260910'
assert review['parameters_reviewed'] and review['definition_equivalence_reviewed']
assert review['reviewed_files_sha256'] == closure and len(closure) == 71
assert matches(ROOT, review['new_module_files_sha256'])
covered = set()
for path, binding in review['inherited_review_binding']['reviews'].items():
    assert sha(ROOT / path) == binding['sha256']
    inherited = json.loads((ROOT / path).read_text())['reviewed_files_sha256']
    matching = {p for p, h in closure.items() if inherited.get(p) == h}
    assert len(matching) == binding['matching_file_count_in_current_closure']
    covered.update(matching)
assert covered == set(closure) - set(review['new_module_files_sha256'])
assert len(covered) == 66
binding = review['inherited_review_binding']
assert sha(ROOT / binding['uniform_mesh_prototype_review']) == binding['uniform_mesh_prototype_review_sha256']
assert sha(ROOT / binding['uniform_mesh_prototype_source']) == binding['uniform_mesh_prototype_source_sha256']
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
assert evidence['checked_declarations'] == len(evidence['declaration_axioms']) == 57
assert evidence['additional_examples_passed'] and len(evidence['additional_examples']) == 3
assert all(set(a) <= standard for a in evidence['declaration_axioms'].values())
for key in ['independent_trace_source', 'independent_trace_log', 'successful_build_log',
            'candidate_inventory', 'independent_closure_evidence']:
    assert sha(ROOT / evidence[key]) == evidence[key + '_sha256']
trace = (ROOT / evidence['independent_trace_log']).read_text()
assert 'error:' not in trace and 'sorryAx' not in trace

prototype = (WORK / 'checks/UniformMesh.prototype.lean').read_text()
port = (LEAN / 'SM/UniformMesh.lean').read_text()
assert prototype[prototype.index('namespace SM'):].split('#print axioms', 1)[0].rstrip() == \
       port[port.index('namespace SM'):].rstrip()
candidate = json.loads((WORK / 'checks/curve-cubes-waypoints-candidate-files.json').read_text())
assert candidate['reviewed_import_closure_candidate'] == closure
assert matches(ROOT, candidate['new_files_sha256'])
progress = snapshot()
assert not progress['evidence_issues']
assert progress['proved_original_claims'] == 14 and progress['accepted_original_checklist'] == 29
assert progress['compiled_proofs_awaiting_review'] == []
out = {'passed': True, 'stage_accepted': False, 'receipt_sha256': sha(rp),
       'audit_sha256': sha(audit_path), 'previous_SM_modules_unchanged': 268,
       'SM_modules': 273, 'new_modules': new_modules,
       'audited_declarations': receipt['audited_declarations'],
       'project_files': len(receipt['project_sha256']), 'frozen_files': len(receipt['bundle_sha256']),
       'accepted_review_bindings_current': len(accepted),
       'new_review_file': str(review_path.relative_to(ROOT)), 'new_review_sha256': sha(review_path),
       'reviewed_import_closure': len(closure),
       'independent_axiom_sets': evidence['checked_declarations'],
       'additional_semantic_examples_passed': 3, 'inherited_review_files_current': 66,
       'uniform_mesh_port_mathematical_body_unchanged': True,
       'original_thm_relgp_accepted': False, 'progress': progress}
target = rp.with_name(rp.name.replace('-output.json', '-curve-cubes-waypoints-verification.json'))
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
